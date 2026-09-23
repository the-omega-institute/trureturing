/* Rotten and doubly rotten 2/3 words (curling numbers).
 *
 * Chaffin, Linderman, Sloane, Wilks, "On Curling Numbers of Integer
 * Sequences", J. Integer Seq. 16 (2013), Art. 13.4.3 (arXiv:1212.6102v3).
 * cn(S) is the greatest k with S = X Y^k, Y nonempty; tau(S) counts the
 * appends of cn before it is 1.  S is rotten when tau(2S) or tau(3S) is
 * smaller than tau(S), doubly rotten when both are.  Conjecture 22 says no
 * doubly rotten word exists; the authors verified lengths up to 34.
 *
 * The walk is bounded rather than trusted: the paper reports Omega(n), the
 * largest tau over words of length n, by direct search for every n <= 48, and
 * Omega = 120 across the lengths touched here, so exceeding it is a hard error
 * and not a silent truncation.
 *
 *   cc -O3 -march=native -o curling curling.c
 *   ./curling <n> [shard] [stride]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define OMEGA_MAX 120
#define MAXLEN (48 + OMEGA_MAX + 4)

static unsigned char buf[MAXLEN];

/* greatest k with s[0..len) = X Y^k, Y nonempty */
static inline int curling(const unsigned char *s, int len) {
    int best = 1;
    for (int p = 1; p + p <= len; p++) {
        int k = 1;
        const unsigned char *y = s + len - p;
        while ((k + 1) * p <= len &&
               memcmp(s + len - (k + 1) * p, y, (size_t)p) == 0)
            k++;
        if (k > best) best = k;
    }
    return best;
}

/* steps until the curling number is 1; -1 means the Omega bound was passed */
static int tau(const unsigned char *word, int n) {
    memcpy(buf, word, (size_t)n);
    int len = n, t = 0;
    for (;;) {
        int c = curling(buf, len);
        if (c == 1) return t;
        if (t >= OMEGA_MAX) return -1;
        buf[len++] = (unsigned char)(c > 255 ? 255 : c);
        t++;
    }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: curling n [shard stride]\n"); return 2; }
    int n = atoi(argv[1]);
    unsigned long long shard = argc > 3 ? strtoull(argv[2], 0, 10) : 0;
    unsigned long long stride = argc > 3 ? strtoull(argv[3], 0, 10) : 1;
    unsigned char w[MAXLEN], w2[MAXLEN], w3[MAXLEN];
    unsigned long long rotten = 0, doubly = 0, total = 0;
    unsigned long long hi = 1ULL << n;

    for (unsigned long long m = shard; m < hi; m += stride) {
        for (int i = 0; i < n; i++) w[i] = (unsigned char)(2 + ((m >> i) & 1ULL));
        w2[0] = 2; memcpy(w2 + 1, w, (size_t)n);
        w3[0] = 3; memcpy(w3 + 1, w, (size_t)n);
        int t = tau(w, n), a = tau(w2, n + 1), b = tau(w3, n + 1);
        if (t < 0 || a < 0 || b < 0) {
            fprintf(stderr, "OMEGA BOUND EXCEEDED at n=%d mask=%llu\n", n, m);
            return 3;
        }
        int ra = a < t, rb = b < t;
        if (ra || rb) rotten++;
        if (ra && rb) {
            doubly++;
            printf("*** DOUBLY ROTTEN | n=%d mask=%llu |", n, m);
            for (int i = 0; i < n; i++) printf("%d", w[i]);
            printf(" tau=%d tau2=%d tau3=%d\n", t, a, b);
            fflush(stdout);
        }
        total++;
    }
    printf("n=%d shard=%llu/%llu words=%llu rotten=%llu doubly=%llu\n",
           n, shard, stride, total, rotten, doubly);
    return 0;
}
