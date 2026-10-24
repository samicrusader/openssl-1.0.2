/*
 * Copyright 2016 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#include <string.h>

#include "e_os.h"

#include <openssl/bio.h>
#include <openssl/crypto.h>
#include <openssl/ssl.h>
#include <openssl/err.h>

#include "ssltestlib.h"
#include "testutil.h"

#ifdef OPENSSL_SYS_WINDOWS
static void test_sleep(unsigned int millis)
{
    Sleep(millis);
}
#else
# include <unistd.h>
static void test_sleep(unsigned int millis)
{
    usleep(millis * 1000);
}
#endif

static char *cert = NULL;
static char *privkey = NULL;

#define NUM_TESTS   2

/* Times the retransmit timer is fired while a write is parked */
#define NUM_RETRANSMITS 2


#define DUMMY_CERT_STATUS_LEN  12

unsigned char certstatus[] = {
    SSL3_RT_HANDSHAKE, /* Content type */
    0xfe, 0xfd, /* Record version */
    0, 1, /* Epoch */
    0, 0, 0, 0, 0, 0x0f, /* Record sequence number */
    0, DTLS1_HM_HEADER_LENGTH + DUMMY_CERT_STATUS_LEN - 2,
    SSL3_MT_CERTIFICATE_STATUS, /* Cert Status handshake message type */
    0, 0, DUMMY_CERT_STATUS_LEN, /* Message len */
    0, 5, /* Message sequence */
    0, 0, 0, /* Fragment offset */
    0, 0, DUMMY_CERT_STATUS_LEN - 2, /* Fragment len */
    0x80, 0x80, 0x80, 0x80, 0x80,
    0x80, 0x80, 0x80, 0x80, 0x80 /* Dummy data */
};

#define RECORD_SEQUENCE 10

static int test_dtls_unprocessed(int testidx)
{
    SSL_CTX *sctx = NULL, *cctx = NULL;
    SSL *serverssl1 = NULL, *clientssl1 = NULL;
    BIO *c_to_s_fbio, *c_to_s_mempacket;
    int testresult = 0;

    printf("Starting Test %d\n", testidx);

    if (!create_ssl_ctx_pair(DTLS_server_method(), DTLS_client_method(), &sctx,
                             &cctx, cert, privkey)) {
        printf("Unable to create SSL_CTX pair\n");
        return 0;
    }

    if (!SSL_CTX_set_ecdh_auto(sctx, 1)) {
        printf("Failed configuring auto ECDH\n");
    }

    if (!SSL_CTX_set_cipher_list(cctx, "AES128-SHA")) {
        printf("Failed setting cipher list\n");
    }

    c_to_s_fbio = BIO_new(bio_f_tls_dump_filter());
    if (c_to_s_fbio == NULL) {
        printf("Failed to create filter BIO\n");
        goto end;
    }

    /* BIO is freed by create_ssl_connection on error */
    if (!create_ssl_objects(sctx, cctx, &serverssl1, &clientssl1, NULL,
                               c_to_s_fbio)) {
        printf("Unable to create SSL objects\n");
        ERR_print_errors_fp(stdout);
        goto end;
    }

    if (testidx == 1)
        certstatus[RECORD_SEQUENCE] = 0xff;

    /*
     * Inject a dummy record from the next epoch. In test 0, this should never
     * get used because the message sequence number is too big. In test 1 we set
     * the record sequence number to be way off in the future. This should not
     * have an impact on the record replay protection because the record should
     * be dropped before it is marked as arrivedg
     */
    c_to_s_mempacket = SSL_get_wbio(clientssl1);
    c_to_s_mempacket = BIO_next(c_to_s_mempacket);
    mempacket_test_inject(c_to_s_mempacket, (char *)certstatus,
                          sizeof(certstatus), 1, INJECT_PACKET_IGNORE_REC_SEQ);

    if (!create_ssl_connection(serverssl1, clientssl1)) {
        printf("Unable to create SSL connection\n");
        ERR_print_errors_fp(stdout);
        goto end;
    }

    testresult = 1;
 end:
    SSL_free(serverssl1);
    SSL_free(clientssl1);
    SSL_CTX_free(sctx);
    SSL_CTX_free(cctx);

    return testresult;
}

/*
 * A filter BIO that passes at most |fragstate.allowed| more writes down to
 * the BIO below it and fails every write after that retryably - what a
 * congested nonblocking datagram socket does. dtls1_do_write() hands over
 * exactly one DTLS fragment per write, so this suspends a handshake write
 * at a fragment boundary of our choosing.
 */
#define BIO_TYPE_FRAG_FILTER    (0x82 | BIO_TYPE_FILTER)

static struct {
    int allowed;                /* fragment writes still permitted */
    int write_calls;            /* bwrite() invocations, passed or not */
} fragstate;

static int frag_write(BIO *bio, const char *in, int inl)
{
    BIO *next = BIO_next(bio);

    BIO_clear_retry_flags(bio);
    fragstate.write_calls++;

    if (fragstate.allowed <= 0) {
        BIO_set_retry_write(bio);
        return -1;
    }
    fragstate.allowed--;

    return BIO_write(next, in, inl);
}

static int frag_read(BIO *bio, char *out, int outl)
{
    return BIO_read(BIO_next(bio), out, outl);
}

static long frag_ctrl(BIO *bio, int cmd, long num, void *ptr)
{
    return BIO_ctrl(BIO_next(bio), cmd, num, ptr);
}

static int frag_gets(BIO *bio, char *buf, int size)
{
    return -1;
}

static int frag_puts(BIO *bio, const char *str)
{
    return frag_write(bio, str, strlen(str));
}

static int frag_new(BIO *bio)
{
    bio->init = 1;
    return 1;
}

static int frag_free(BIO *bio)
{
    if (bio == NULL)
        return 0;
    bio->init = 0;
    return 1;
}

static BIO_METHOD method_frag = {
    BIO_TYPE_FRAG_FILTER,
    "Fragment limiting filter",
    frag_write,
    frag_read,
    frag_puts,
    frag_gets,
    frag_ctrl,
    frag_new,
    frag_free
};

/* The ALPN padding that makes the ClientHello big enough to fragment */
static int set_fat_alpn(SSL_CTX *ctx)
{
    static unsigned char alpn[750];
    size_t used = 0;
    unsigned int i;

    for (i = 0; i < 3; i++) {
        char name[250];
        int n = BIO_snprintf(name, sizeof(name), "proto-%04u-%s", i,
                             "padpadpadpadpadpadpadpadpadpadpadpadpadpadpad"
                             "padpadpadpadpadpadpadpadpadpadpadpadpadpadpad"
                             "padpadpadpadpadpadpadpadpadpadpadpadpadpadpad"
                             "padpadpadpadpadpadpadpadpadpadpadpadpadpadpad"
                             "padpadpadpadpadpadpadpadpadpadpadpadpadpad");

        if (n <= 0 || used + 1 + (size_t)n > sizeof(alpn))
            return 0;
        alpn[used++] = (unsigned char)n;
        memcpy(alpn + used, name, (size_t)n);
        used += (size_t)n;
    }

    return SSL_CTX_set_alpn_protos(ctx, alpn, (unsigned int)used) == 0;
}

/*
 * Bring a client to the point where its ClientHello write is suspended
 * mid-message: the message is padded out via ALPN and the MTU pinned so that
 * it takes several fragments, and the filter BIO lets only |allowed| of them
 * through. The caller frees the objects either way.
 */
static int park_client_write(SSL_CTX **sctx, SSL_CTX **cctx, SSL **sssl,
                             SSL **cssl, int allowed)
{
    BIO *fbio;
    int ret, err;

    if (!create_ssl_ctx_pair(DTLS_server_method(), DTLS_client_method(), sctx,
                             cctx, cert, privkey)) {
        printf("Unable to create SSL_CTX pair\n");
        return 0;
    }

    if (!set_fat_alpn(*cctx)) {
        printf("Failed setting the ALPN list\n");
        return 0;
    }

    memset(&fragstate, 0, sizeof(fragstate));
    fragstate.allowed = allowed;

    fbio = BIO_new(&method_frag);
    if (fbio == NULL) {
        printf("Failed to create the fragment limiting BIO\n");
        return 0;
    }

    /* BIO is freed by create_ssl_objects on error */
    if (!create_ssl_objects(*sctx, *cctx, sssl, cssl, NULL, fbio)) {
        printf("Unable to create SSL objects\n");
        ERR_print_errors_fp(stdout);
        return 0;
    }

    /*
     * Pin the MTU so the ClientHello fragments deterministically.
     * SSL_OP_NO_QUERY_MTU stops dtls1_query_mtu() from overriding it with a
     * value queried from the BIO.
     */
    SSL_set_options(*cssl, SSL_OP_NO_QUERY_MTU);
    if (!SSL_set_mtu(*cssl, 256)) {
        printf("Failed to set the MTU\n");
        return 0;
    }

    /*
     * |allowed| fragments of the ClientHello go out and the next write is
     * the one that suspends, leaving the message half sent and the write
     * parked on WANT_WRITE.
     */
    ret = SSL_connect(*cssl);
    err = SSL_get_error(*cssl, ret);
    if (ret > 0 || err != SSL_ERROR_WANT_WRITE) {
        printf("ClientHello write did not suspend (ret %d, err %d)\n", ret,
               err);
        ERR_print_errors_fp(stdout);
        return 0;
    }

    if (fragstate.write_calls <= allowed) {
        printf("ClientHello was not fragmented (%d writes)\n",
               fragstate.write_calls);
        return 0;
    }

    return 1;
}

/* Wait for the retransmit timer of |s| to expire. Returns 0 on failure. */
static int wait_for_timer(SSL *s)
{
    struct timeval tv;

    if (DTLSv1_get_timeout(s, &tv) <= 0) {
        printf("No retransmit timer is running\n");
        return 0;
    }

    test_sleep((unsigned int)(tv.tv_sec * 1000 + tv.tv_usec / 1000) + 10);

    return 1;
}

/*
 * While a handshake write is parked mid-message, an expiring retransmit
 * timer must not touch the retransmit queue. A retransmit reconstructs an
 * already sent message into s->init_buf/s->init_off/s->init_num/
 * s->d1->w_msg_hdr - the very fields the parked write is still using - and
 * once it has run to completion it leaves init_off and init_num both 0, so
 * resuming the parked write re-enters dtls1_do_write() and trips its entry
 * assertion. OPENSSL_assert() is not compiled out of release builds, so that
 * is an abort(), which is why simply reaching the end of this test matters as
 * much as the fragment counting does.
 */
static int test_dtls_retransmit_parked(void)
{
    SSL_CTX *sctx = NULL, *cctx = NULL;
    SSL *serverssl = NULL, *clientssl = NULL;
    int testresult = 0;
    int ret, err, i, before;

    printf("Starting DTLS parked write retransmit test\n");

    if (!park_client_write(&sctx, &cctx, &serverssl, &clientssl, 1))
        goto end;

    /* Nothing but the guard should stop a retransmit from going out now */
    fragstate.allowed = 100;

    for (i = 0; i < NUM_RETRANSMITS; i++) {
        before = fragstate.write_calls;

        if (!wait_for_timer(clientssl))
            goto end;

        if (DTLSv1_handle_timeout(clientssl) < 0) {
            printf("DTLSv1_handle_timeout failed\n");
            ERR_print_errors_fp(stdout);
            goto end;
        }

        if (fragstate.write_calls != before) {
            printf("Retransmitted %d fragments while a write was parked\n",
                   fragstate.write_calls - before);
            goto end;
        }
    }

    /* Resume the parked write; it should carry on as an ordinary handshake */
    ret = SSL_connect(clientssl);
    err = SSL_get_error(clientssl, ret);
    if (err == SSL_ERROR_SSL || err == SSL_ERROR_SYSCALL) {
        printf("Resuming the parked write failed (ret %d, err %d)\n", ret, err);
        ERR_print_errors_fp(stdout);
        goto end;
    }

    testresult = 1;
 end:
    SSL_free(serverssl);
    SSL_free(clientssl);
    SSL_CTX_free(sctx);
    SSL_CTX_free(cctx);

    return testresult;
}

int main(int argc, char *argv[])
{
    BIO *err = NULL;
    int testresult = 0;

    if (argc != 3) {
        printf("Invalid argument count\n");
        return 1;
    }

    cert = argv[1];
    privkey = argv[2];

    err = BIO_new_fp(stderr, BIO_NOCLOSE | BIO_FP_TEXT);

    SSL_library_init();
    SSL_load_error_strings();

    CRYPTO_malloc_debug_init();
    CRYPTO_dbg_set_options(V_CRYPTO_MDEBUG_ALL);
    CRYPTO_mem_ctrl(CRYPTO_MEM_CHECK_ON);

    if (!test_dtls_unprocessed(0) || !test_dtls_unprocessed(1)
            || !test_dtls_retransmit_parked())
        testresult = 1;

    ERR_free_strings();
    ERR_remove_thread_state(NULL);
    EVP_cleanup();
    CRYPTO_cleanup_all_ex_data();
    CRYPTO_mem_leaks(err);
    BIO_free(err);

    if (!testresult)
        printf("PASS\n");

    return testresult;
}
