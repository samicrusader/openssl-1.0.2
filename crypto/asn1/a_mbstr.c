/* a_mbstr.c */
/*
 * Written by Dr Stephen N Henson (steve@openssl.org) for the OpenSSL project
 * 1999.
 */
/* ====================================================================
 * Copyright (c) 1999 The OpenSSL Project.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * 3. All advertising materials mentioning features or use of this
 *    software must display the following acknowledgment:
 *    "This product includes software developed by the OpenSSL Project
 *    for use in the OpenSSL Toolkit. (http://www.OpenSSL.org/)"
 *
 * 4. The names "OpenSSL Toolkit" and "OpenSSL Project" must not be used to
 *    endorse or promote products derived from this software without
 *    prior written permission. For written permission, please contact
 *    licensing@OpenSSL.org.
 *
 * 5. Products derived from this software may not be called "OpenSSL"
 *    nor may "OpenSSL" appear in their names without prior written
 *    permission of the OpenSSL Project.
 *
 * 6. Redistributions of any form whatsoever must retain the following
 *    acknowledgment:
 *    "This product includes software developed by the OpenSSL Project
 *    for use in the OpenSSL Toolkit (http://www.OpenSSL.org/)"
 *
 * THIS SOFTWARE IS PROVIDED BY THE OpenSSL PROJECT ``AS IS'' AND ANY
 * EXPRESSED OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE OpenSSL PROJECT OR
 * ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 * ====================================================================
 *
 * This product includes cryptographic software written by Eric Young
 * (eay@cryptsoft.com).  This product includes software written by Tim
 * Hudson (tjh@cryptsoft.com).
 *
 */

#include <stdio.h>
#include <ctype.h>
#include <limits.h>
#include "cryptlib.h"
#include <openssl/asn1.h>

static int traverse_string(const unsigned char *p, int len, int inform,
                           int (*rfunc) (unsigned long value, void *in),
                           void *arg);
static int in_utf8(unsigned long value, void *arg);
static int out_utf8(unsigned long value, void *arg);
static int type_str(unsigned long value, void *arg);
static int cpy_asc(unsigned long value, void *arg);
static int cpy_bmp(unsigned long value, void *arg);
static int cpy_univ(unsigned long value, void *arg);
static int cpy_utf8(unsigned long value, void *arg);

typedef enum {
    SURROGATE_MIN = 0xd800UL,
    SURROGATE_MAX = 0xdfffUL,
    UNICODE_MAX = 0x10ffffUL,
    UNICODE_LIMIT
} UNICODE_CONSTANTS;

static int is_unicode_surrogate(unsigned long value)
{
    return value >= SURROGATE_MIN && value <= SURROGATE_MAX;
}

static int is_unicode_valid(unsigned long value)
{
    return value <= UNICODE_MAX && !is_unicode_surrogate(value);
}

#ifdef CHARSET_EBCDIC
static int ossl_toascii(int c)
{
    if (c < -128 || c > 256 || c == EOF)
        return c;
    /*
     * Adjust negatively signed characters.
     * This is not required for ASCII because any character that sign extends
     * is not seven bit and all of the checks are on the seven bit characters.
     * I.e. any check must fail on sign extension.
     */
    if (c < 0)
        c += 256;
    return os_toascii[c];
}

static int ossl_fromascii(int c)
{
    if (c < -128 || c > 256 || c == EOF)
        return c;
    if (c < 0)
        c += 256;
    return os_toebcdic[c];
}

#else
#define ossl_fromascii(c) (c)
#define ossl_toascii(c) (c)
#endif

#define ASCII_IS_DIGIT(c) (c >= 0x30 && c <= 0x39)
static int ossl_isdigit(int c)
{
    int a = ossl_toascii(c);

    return ASCII_IS_DIGIT(a);
}

#define CTYPE_MASK_lower 0x1
#define CTYPE_MASK_upper 0x2
#define CTYPE_MASK_digit 0x4
#define CTYPE_MASK_space 0x8
#define CTYPE_MASK_xdigit 0x10
#define CTYPE_MASK_blank 0x20
#define CTYPE_MASK_cntrl 0x40
#define CTYPE_MASK_graph 0x80
#define CTYPE_MASK_print 0x100
#define CTYPE_MASK_punct 0x200
#define CTYPE_MASK_base64 0x400
#define CTYPE_MASK_asn1print 0x800

static const unsigned short ctype_char_map[128] = {
    /* 00 nul */ CTYPE_MASK_cntrl,
    /* 01 soh */ CTYPE_MASK_cntrl,
    /* 02 stx */ CTYPE_MASK_cntrl,
    /* 03 etx */ CTYPE_MASK_cntrl,
    /* 04 eot */ CTYPE_MASK_cntrl,
    /* 05 enq */ CTYPE_MASK_cntrl,
    /* 06 ack */ CTYPE_MASK_cntrl,
    /* 07 \a  */ CTYPE_MASK_cntrl,
    /* 08 \b  */ CTYPE_MASK_cntrl,
    /* 09 \t  */ CTYPE_MASK_blank | CTYPE_MASK_cntrl | CTYPE_MASK_space,
    /* 0A \n  */ CTYPE_MASK_cntrl | CTYPE_MASK_space,
    /* 0B \v  */ CTYPE_MASK_cntrl | CTYPE_MASK_space,
    /* 0C \f  */ CTYPE_MASK_cntrl | CTYPE_MASK_space,
    /* 0D \r  */ CTYPE_MASK_cntrl | CTYPE_MASK_space,
    /* 0E so  */ CTYPE_MASK_cntrl,
    /* 0F si  */ CTYPE_MASK_cntrl,
    /* 10 dle */ CTYPE_MASK_cntrl,
    /* 11 dc1 */ CTYPE_MASK_cntrl,
    /* 12 dc2 */ CTYPE_MASK_cntrl,
    /* 13 dc3 */ CTYPE_MASK_cntrl,
    /* 14 dc4 */ CTYPE_MASK_cntrl,
    /* 15 nak */ CTYPE_MASK_cntrl,
    /* 16 syn */ CTYPE_MASK_cntrl,
    /* 17 etb */ CTYPE_MASK_cntrl,
    /* 18 can */ CTYPE_MASK_cntrl,
    /* 19 em  */ CTYPE_MASK_cntrl,
    /* 1A sub */ CTYPE_MASK_cntrl,
    /* 1B esc */ CTYPE_MASK_cntrl,
    /* 1C fs  */ CTYPE_MASK_cntrl,
    /* 1D gs  */ CTYPE_MASK_cntrl,
    /* 1E rs  */ CTYPE_MASK_cntrl,
    /* 1F us  */ CTYPE_MASK_cntrl,
    /* 20     */ CTYPE_MASK_blank | CTYPE_MASK_print | CTYPE_MASK_space
        | CTYPE_MASK_asn1print,
    /* 21  !  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 22  "  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 23  #  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 24  $  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 25  %  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 26  &  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 27  '  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_asn1print,
    /* 28  (  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_asn1print,
    /* 29  )  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_asn1print,
    /* 2A  *  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 2B  +  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 2C  ,  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_asn1print,
    /* 2D  -  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_asn1print,
    /* 2E  .  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_asn1print,
    /* 2F  /  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 30  0  */ CTYPE_MASK_digit | CTYPE_MASK_graph | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 31  1  */ CTYPE_MASK_digit | CTYPE_MASK_graph | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 32  2  */ CTYPE_MASK_digit | CTYPE_MASK_graph | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 33  3  */ CTYPE_MASK_digit | CTYPE_MASK_graph | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 34  4  */ CTYPE_MASK_digit | CTYPE_MASK_graph | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 35  5  */ CTYPE_MASK_digit | CTYPE_MASK_graph | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 36  6  */ CTYPE_MASK_digit | CTYPE_MASK_graph | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 37  7  */ CTYPE_MASK_digit | CTYPE_MASK_graph | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 38  8  */ CTYPE_MASK_digit | CTYPE_MASK_graph | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 39  9  */ CTYPE_MASK_digit | CTYPE_MASK_graph | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 3A  :  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_asn1print,
    /* 3B  ;  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 3C  <  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 3D  =  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 3E  >  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 3F  ?  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct
        | CTYPE_MASK_asn1print,
    /* 40  @  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 41  A  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 42  B  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 43  C  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 44  D  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 45  E  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 46  F  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 47  G  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 48  H  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 49  I  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 4A  J  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 4B  K  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 4C  L  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 4D  M  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 4E  N  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 4F  O  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 50  P  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 51  Q  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 52  R  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 53  S  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 54  T  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 55  U  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 56  V  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 57  W  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 58  X  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 59  Y  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 5A  Z  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_upper
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 5B  [  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 5C  \  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 5D  ]  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 5E  ^  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 5F  _  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 60  `  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 61  a  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 62  b  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 63  c  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 64  d  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 65  e  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 66  f  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_xdigit | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 67  g  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 68  h  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 69  i  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 6A  j  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 6B  k  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 6C  l  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 6D  m  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 6E  n  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 6F  o  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 70  p  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 71  q  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 72  r  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 73  s  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 74  t  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 75  u  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 76  v  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 77  w  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 78  x  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 79  y  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 7A  z  */ CTYPE_MASK_graph | CTYPE_MASK_lower | CTYPE_MASK_print
        | CTYPE_MASK_base64 | CTYPE_MASK_asn1print,
    /* 7B  {  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 7C  |  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 7D  }  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 7E  ~  */ CTYPE_MASK_graph | CTYPE_MASK_print | CTYPE_MASK_punct,
    /* 7F del */ CTYPE_MASK_cntrl
};

static int ossl_ctype_check(int c, unsigned int mask)
{
    const int max = sizeof(ctype_char_map) / sizeof(*ctype_char_map);
    const int a = ossl_toascii(c);

    return a >= 0 && a < max && (ctype_char_map[a] & mask) != 0;
}

#define ossl_isasn1print(c) (ossl_ctype_check((c), CTYPE_MASK_asn1print))

/*
 * These functions take a string in UTF8, ASCII or multibyte form and a mask
 * of permissible ASN1 string types. It then works out the minimal type
 * (using the order Printable < IA5 < T61 < BMP < Universal < UTF8) and
 * creates a string of the correct type with the supplied data. Yes this is
 * horrible: it has to be :-( The 'ncopy' form checks minimum and maximum
 * size limits too.
 */

int ASN1_mbstring_copy(ASN1_STRING **out, const unsigned char *in, int len,
                       int inform, unsigned long mask)
{
    return ASN1_mbstring_ncopy(out, in, len, inform, mask, 0, 0);
}

int ASN1_mbstring_ncopy(ASN1_STRING **out, const unsigned char *in, int len,
                        int inform, unsigned long mask,
                        long minsize, long maxsize)
{
    int str_type;
    int ret;
    char free_out;
    int outform, outlen = 0;
    ASN1_STRING *dest;
    unsigned char *p;
    int nchar;
    char strbuf[32];
    int (*cpyfunc) (unsigned long, void *) = NULL;
    if (len == -1)
        len = strlen((const char *)in);
    if (!mask)
        mask = DIRSTRING_TYPE;

    /* First do a string check and work out the number of characters */
    switch (inform) {

    case MBSTRING_BMP:
        if (len & 1) {
            ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY,
                    ASN1_R_INVALID_BMPSTRING_LENGTH);
            return -1;
        }
        nchar = len >> 1;
        break;

    case MBSTRING_UNIV:
        if (len & 3) {
            ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY,
                    ASN1_R_INVALID_UNIVERSALSTRING_LENGTH);
            return -1;
        }
        nchar = len >> 2;
        break;

    case MBSTRING_UTF8:
        nchar = 0;
        /* This counts the characters and does utf8 syntax checking */
        ret = traverse_string(in, len, MBSTRING_UTF8, in_utf8, &nchar);
        if (ret < 0) {
            ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY, ASN1_R_INVALID_UTF8STRING);
            return -1;
        }
        break;

    case MBSTRING_ASC:
        nchar = len;
        break;

    default:
        ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY, ASN1_R_UNKNOWN_FORMAT);
        return -1;
    }

    if ((minsize > 0) && (nchar < minsize)) {
        ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY, ASN1_R_STRING_TOO_SHORT);
        BIO_snprintf(strbuf, sizeof(strbuf), "%ld", minsize);
        ERR_add_error_data(2, "minsize=", strbuf);
        return -1;
    }

    if ((maxsize > 0) && (nchar > maxsize)) {
        ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY, ASN1_R_STRING_TOO_LONG);
        BIO_snprintf(strbuf, sizeof(strbuf), "%ld", maxsize);
        ERR_add_error_data(2, "maxsize=", strbuf);
        return -1;
    }

    /* Now work out minimal type (if any) */
    if (traverse_string(in, len, inform, type_str, &mask) < 0) {
        ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY, ASN1_R_ILLEGAL_CHARACTERS);
        return -1;
    }

    /* Now work out output format and string type */
    outform = MBSTRING_ASC;
    if (mask & B_ASN1_PRINTABLESTRING)
        str_type = V_ASN1_PRINTABLESTRING;
    else if (mask & B_ASN1_IA5STRING)
        str_type = V_ASN1_IA5STRING;
    else if (mask & B_ASN1_T61STRING)
        str_type = V_ASN1_T61STRING;
    else if (mask & B_ASN1_BMPSTRING) {
        str_type = V_ASN1_BMPSTRING;
        outform = MBSTRING_BMP;
    } else if (mask & B_ASN1_UNIVERSALSTRING) {
        str_type = V_ASN1_UNIVERSALSTRING;
        outform = MBSTRING_UNIV;
    } else {
        str_type = V_ASN1_UTF8STRING;
        outform = MBSTRING_UTF8;
    }
    if (!out)
        return str_type;
    if (*out) {
        free_out = 0;
        dest = *out;
        if (dest->data) {
            dest->length = 0;
            OPENSSL_free(dest->data);
            dest->data = NULL;
        }
        dest->type = str_type;
    } else {
        free_out = 1;
        dest = ASN1_STRING_type_new(str_type);
        if (!dest) {
            ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY, ERR_R_MALLOC_FAILURE);
            return -1;
        }
        *out = dest;
    }
    /* If both the same type just copy across */
    if (inform == outform) {
        if (!ASN1_STRING_set(dest, in, len)) {
            ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY, ERR_R_MALLOC_FAILURE);
            return -1;
        }
        return str_type;
    }

    /* Work out how much space the destination will need */
    switch (outform) {
    case MBSTRING_ASC:
        outlen = nchar;
        cpyfunc = cpy_asc;
        break;

    case MBSTRING_BMP:
        outlen = nchar << 1;
        cpyfunc = cpy_bmp;
        break;

    case MBSTRING_UNIV:
        outlen = nchar << 2;
        cpyfunc = cpy_univ;
        break;

    case MBSTRING_UTF8:
        outlen = 0;
        ret = traverse_string(in, len, inform, out_utf8, &outlen);
        if (ret < 0) {
            ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY, ASN1_R_INVALID_UTF8STRING);
            return -1;
        }
        cpyfunc = cpy_utf8;
        break;
    }
    if (!(p = OPENSSL_malloc(outlen + 1))) {
        if (free_out)
            ASN1_STRING_free(dest);
        ASN1err(ASN1_F_ASN1_MBSTRING_NCOPY, ERR_R_MALLOC_FAILURE);
        return -1;
    }
    dest->length = outlen;
    dest->data = p;
    p[outlen] = 0;
    traverse_string(in, len, inform, cpyfunc, &p);
    return str_type;
}

/*
 * This function traverses a string and passes the value of each character to
 * an optional function along with a void * argument.
 */

static int traverse_string(const unsigned char *p, int len, int inform,
                           int (*rfunc) (unsigned long value, void *in),
                           void *arg)
{
    unsigned long value;
    int ret;
    while (len) {
        if (inform == MBSTRING_ASC) {
            value = *p++;
            len--;
        } else if (inform == MBSTRING_BMP) {
            value = *p++ << 8;
            value |= *p++;
            len -= 2;
        } else if (inform == MBSTRING_UNIV) {
            value = ((unsigned long)*p++) << 24;
            value |= ((unsigned long)*p++) << 16;
            value |= *p++ << 8;
            value |= *p++;
            len -= 4;
        } else {
            ret = UTF8_getc(p, len, &value);
            if (ret < 0)
                return -1;
            len -= ret;
            p += ret;
        }
        if (rfunc) {
            ret = rfunc(value, arg);
            if (ret <= 0)
                return ret;
        }
    }
    return 1;
}

/* Various utility functions for traverse_string */

/* Just count number of characters */

static int in_utf8(unsigned long value, void *arg)
{
    int *nchar;

    if (!is_unicode_valid(value))
        return -2;
    nchar = arg;
    (*nchar)++;
    return 1;
}

/* Determine size of output as a UTF8 String */

static int out_utf8(unsigned long value, void *arg)
{
    int *outlen, len;
    len = UTF8_putc(NULL, -1, value);
    if (len <= 0)
        return len;
    outlen = arg;
    *outlen += len;
    return 1;
}

/*
 * Determine the "type" of a string: check each character against a supplied
 * "mask".
 */

static int type_str(unsigned long value, void *arg)
{
    unsigned long usable_types = *((unsigned long *)arg);
    unsigned long types = usable_types;
    const int native = value > INT_MAX ? INT_MAX : ossl_fromascii(value);

    /*
     * Clear out all the types which are not checked later. If any of those
     * is present in the mask, then the UTF8 type will be added and checked
     * below.
     */
    types &= B_ASN1_NUMERICSTRING | B_ASN1_PRINTABLESTRING
        | B_ASN1_IA5STRING | B_ASN1_T61STRING | B_ASN1_BMPSTRING
        | B_ASN1_UNIVERSALSTRING | B_ASN1_UTF8STRING;

    /*
     * If any other types were in the input mask, they're effectively treated
     * as UTF8
     */
    if (types != usable_types)
        types |= B_ASN1_UTF8STRING;

    /*
     * These checks should be in sync with ASN1_mbstring_ncopy.
     */
    if ((types & B_ASN1_NUMERICSTRING) && !(ossl_isdigit(native) || native == ' '))
        types &= ~B_ASN1_NUMERICSTRING;
    if ((types & B_ASN1_PRINTABLESTRING) && !ossl_isasn1print(native))
        types &= ~B_ASN1_PRINTABLESTRING;
    if ((types & B_ASN1_IA5STRING) && (value > 127))
        types &= ~B_ASN1_IA5STRING;
    if ((types & B_ASN1_T61STRING) && (value > 0xff))
        types &= ~B_ASN1_T61STRING;
    if ((types & B_ASN1_BMPSTRING) && (value > 0xffff))
        types &= ~B_ASN1_BMPSTRING;
    if ((types & B_ASN1_UTF8STRING) && !is_unicode_valid(value))
        types &= ~B_ASN1_UTF8STRING;
    if (!types)
        return -1;
    *((unsigned long *)arg) = types;
    return 1;
}

/* Copy one byte per character ASCII like strings */

static int cpy_asc(unsigned long value, void *arg)
{
    unsigned char **p, *q;
    p = arg;
    q = *p;
    *q = (unsigned char)value;
    (*p)++;
    return 1;
}

/* Copy two byte per character BMPStrings */

static int cpy_bmp(unsigned long value, void *arg)
{
    unsigned char **p, *q;
    p = arg;
    q = *p;
    *q++ = (unsigned char)((value >> 8) & 0xff);
    *q = (unsigned char)(value & 0xff);
    *p += 2;
    return 1;
}

/* Copy four byte per character UniversalStrings */

static int cpy_univ(unsigned long value, void *arg)
{
    unsigned char **p, *q;
    p = arg;
    q = *p;
    *q++ = (unsigned char)((value >> 24) & 0xff);
    *q++ = (unsigned char)((value >> 16) & 0xff);
    *q++ = (unsigned char)((value >> 8) & 0xff);
    *q = (unsigned char)(value & 0xff);
    *p += 4;
    return 1;
}

/* Copy to a UTF8String */

static int cpy_utf8(unsigned long value, void *arg)
{
    unsigned char **p;
    int ret;
    p = arg;
    /* We already know there is enough room so pass 0xff as the length */
    ret = UTF8_putc(*p, 0xff, value);
    if (ret < 0)
        return ret;
    *p += ret;
    return 1;
}
