/*
 * Search for distinct x < y such that rad(x+i) = rad(y+i) for each
 * 0 <= i < steps.  Equal radicals mean equal prime support, not divisibility:
 * candidates for x are all products in which every prime in rad(y) occurs
 * with an arbitrary positive exponent.  In particular, neither member of a
 * pair need divide the other.
 *
 * Since rad(y+i) = rad(x+i) <= x+i < y+i, every y+i must be non-squarefree.
 * A segmented factor sieve applies that necessary filter and supplies the
 * radicals of the surviving y values; memory does not grow with the search
 * interval.  Each survivor's complete positive exponent vectors are then
 * enumerated below y, and the remaining radicals are factored exactly.
 *
 * Before every requested search, a steps=2 search through 2000 must find
 * exactly (2,8), (6,48), (14,224), (30,960), and (75,1215).  Failure of this
 * ladder contract aborts the requested search.
 */

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(__unix__) || defined(__APPLE__)
#include <sys/resource.h>
#define HAVE_GETRUSAGE 1
#else
#define HAVE_GETRUSAGE 0
#endif

#define SEGMENT_SIZE (1U << 20)
#define MAX_STEPS 64U
#define MAX_SUPPORT 16U
#define MAX_PRIMES 7000U
#define LADDER_LIMIT 2000U
#define LADDER_PAIRS 5U

typedef struct {
    uint32_t x;
    uint32_t y;
} Pair;

typedef struct {
    uint32_t primes[MAX_PRIMES];
    size_t count;
} PrimeTable;

typedef void (*pair_fn)(uint32_t x, uint32_t y, void *opaque);

typedef struct {
    const PrimeTable *table;
    const uint32_t *targets;
    uint32_t steps;
    uint32_t y;
    uint32_t support[MAX_SUPPORT];
    size_t support_count;
    pair_fn emit;
    void *emit_data;
    uint64_t *pair_count;
} CandidateSearch;

typedef struct {
    Pair pairs[32];
    size_t stored;
    uint64_t total;
} LadderResult;

static void usage(FILE *stream, const char *program) {
    fprintf(stream, "usage: %s --limit N [--steps k] [--from LO]\n", program);
}

static int parse_u64(const char *text, uint64_t *value) {
    char *end = NULL;
    unsigned long long parsed;

    if (text[0] == '\0' || text[0] == '-') {
        return 0;
    }
    errno = 0;
    parsed = strtoull(text, &end, 10);
    if (errno != 0 || *end != '\0') {
        return 0;
    }
    *value = (uint64_t)parsed;
    return 1;
}

static int build_prime_table(PrimeTable *table) {
    uint8_t composite[65536] = {0};
    uint32_t n;

    table->count = 0;
    for (n = 2; n <= 65535U; ++n) {
        uint32_t multiple;
        if (composite[n]) {
            continue;
        }
        if (table->count == MAX_PRIMES) {
            return 0;
        }
        table->primes[table->count++] = n;
        if (n > 255U) {
            continue;
        }
        for (multiple = n * n; multiple <= 65535U; multiple += n) {
            composite[multiple] = 1;
        }
    }
    return 1;
}

static uint32_t radical(uint32_t value, const PrimeTable *table) {
    uint32_t remaining = value;
    uint32_t result = 1;
    size_t i;

    for (i = 0; i < table->count; ++i) {
        uint32_t p = table->primes[i];
        if ((uint64_t)p * p > remaining) {
            break;
        }
        if (remaining % p != 0) {
            continue;
        }
        result *= p;
        do {
            remaining /= p;
        } while (remaining % p == 0);
    }
    if (remaining > 1) {
        result *= remaining;
    }
    return result;
}

static size_t factor_squarefree(uint32_t value, const PrimeTable *table,
                                uint32_t factors[MAX_SUPPORT]) {
    uint32_t remaining = value;
    size_t count = 0;
    size_t i;

    for (i = 0; i < table->count; ++i) {
        uint32_t p = table->primes[i];
        if ((uint64_t)p * p > remaining) {
            break;
        }
        if (remaining % p != 0) {
            continue;
        }
        if (count == MAX_SUPPORT) {
            return 0;
        }
        factors[count++] = p;
        remaining /= p;
    }
    if (remaining > 1) {
        if (count == MAX_SUPPORT) {
            return 0;
        }
        factors[count++] = remaining;
    }
    return count;
}

static void test_candidate(CandidateSearch *search, uint32_t x) {
    uint32_t i;

    for (i = 1; i < search->steps; ++i) {
        if (radical(x + i, search->table) != search->targets[i]) {
            return;
        }
    }
    ++*search->pair_count;
    search->emit(x, search->y, search->emit_data);
}

static void enumerate_support(CandidateSearch *search, size_t index,
                              uint32_t product) {
    uint32_t p;
    uint32_t power;
    uint32_t max_factor;

    if (index == search->support_count) {
        test_candidate(search, product);
        return;
    }

    p = search->support[index];
    max_factor = (search->y - 1U) / product;
    power = p;
    while (power <= max_factor) {
        enumerate_support(search, index + 1U, product * power);
        if (power > max_factor / p) {
            break;
        }
        power *= p;
    }
}

static int sieve_segment(uint32_t low, uint32_t high,
                         const PrimeTable *table, uint32_t *remaining,
                         uint32_t *radicals, uint8_t *nonsquarefree) {
    size_t length = (size_t)((uint64_t)high - low + 1U);
    size_t i;
    size_t prime_index;

    for (i = 0; i < length; ++i) {
        remaining[i] = low + (uint32_t)i;
        radicals[i] = 1;
        nonsquarefree[i] = 0;
    }

    for (prime_index = 0; prime_index < table->count; ++prime_index) {
        uint32_t p = table->primes[prime_index];
        uint64_t first;
        uint64_t multiple;
        if ((uint64_t)p * p > high) {
            break;
        }
        first = ((uint64_t)low + p - 1U) / p * p;
        for (multiple = first; multiple <= high; multiple += p) {
            size_t offset = (size_t)(multiple - low);
            uint32_t quotient = remaining[offset] / p;
            radicals[offset] *= p;
            if (quotient % p == 0) {
                nonsquarefree[offset] = 1;
            }
            while (quotient % p == 0) {
                quotient /= p;
            }
            remaining[offset] = quotient;
        }
    }

    for (i = 0; i < length; ++i) {
        if (remaining[i] > 1U) {
            radicals[i] *= remaining[i];
        }
    }
    return 1;
}

static int search_range(uint32_t from, uint32_t limit, uint32_t steps,
                        const PrimeTable *table, pair_fn emit, void *emit_data,
                        uint64_t *pair_count) {
    size_t capacity = (size_t)SEGMENT_SIZE + steps - 1U;
    uint32_t *remaining = malloc(capacity * sizeof(*remaining));
    uint32_t *radicals = malloc(capacity * sizeof(*radicals));
    uint8_t *nonsquarefree = malloc(capacity * sizeof(*nonsquarefree));
    uint64_t aligned;

    if (remaining == NULL || radicals == NULL || nonsquarefree == NULL) {
        fprintf(stderr, "allocation failed for segment buffers\n");
        free(remaining);
        free(radicals);
        free(nonsquarefree);
        return 0;
    }

    *pair_count = 0;
    if (from > limit) {
        free(remaining);
        free(radicals);
        free(nonsquarefree);
        return 1;
    }

    aligned = 2U + ((uint64_t)from - 2U) / SEGMENT_SIZE * SEGMENT_SIZE;
    while (aligned <= limit) {
        uint64_t main_high64 = aligned + SEGMENT_SIZE - 1U;
        uint32_t segment_low = (uint32_t)aligned;
        uint32_t main_high;
        uint32_t sieve_high;
        uint64_t y64;

        if (main_high64 > limit) {
            main_high64 = limit;
        }
        main_high = (uint32_t)main_high64;
        sieve_high = main_high + steps - 1U;
        if (!sieve_segment(segment_low, sieve_high, table, remaining,
                           radicals, nonsquarefree)) {
            free(remaining);
            free(radicals);
            free(nonsquarefree);
            return 0;
        }

        y64 = from > segment_low ? from : segment_low;
        for (; y64 <= main_high; ++y64) {
            uint32_t y = (uint32_t)y64;
            size_t offset = (size_t)(y - segment_low);
            uint32_t i;
            CandidateSearch candidate;
            int passes_filter = 1;

            for (i = 0; i < steps; ++i) {
                if (!nonsquarefree[offset + i]) {
                    passes_filter = 0;
                    break;
                }
            }
            if (!passes_filter) {
                continue;
            }

            candidate.table = table;
            candidate.targets = radicals + offset;
            candidate.steps = steps;
            candidate.y = y;
            candidate.support_count = factor_squarefree(
                radicals[offset], table, candidate.support);
            candidate.emit = emit;
            candidate.emit_data = emit_data;
            candidate.pair_count = pair_count;
            if (candidate.support_count == 0) {
                fprintf(stderr, "internal error: support overflow at y=%" PRIu32 "\n", y);
                free(remaining);
                free(radicals);
                free(nonsquarefree);
                return 0;
            }
            enumerate_support(&candidate, 0, 1);
        }

        aligned += SEGMENT_SIZE;
    }

    free(remaining);
    free(radicals);
    free(nonsquarefree);
    return 1;
}

static void collect_ladder_pair(uint32_t x, uint32_t y, void *opaque) {
    LadderResult *result = opaque;
    if (result->stored < sizeof(result->pairs) / sizeof(result->pairs[0])) {
        result->pairs[result->stored].x = x;
        result->pairs[result->stored].y = y;
        ++result->stored;
    }
    ++result->total;
}

static void print_pair(uint32_t x, uint32_t y, void *opaque) {
    (void)opaque;
    printf("%" PRIu32 " %" PRIu32 "\n", x, y);
}

static int pair_compare(const void *left, const void *right) {
    const Pair *a = left;
    const Pair *b = right;
    if (a->y != b->y) {
        return a->y < b->y ? -1 : 1;
    }
    if (a->x != b->x) {
        return a->x < b->x ? -1 : 1;
    }
    return 0;
}

static int verify_ladder(const PrimeTable *table) {
    static const Pair expected[LADDER_PAIRS] = {
        {2, 8}, {6, 48}, {14, 224}, {30, 960}, {75, 1215}
    };
    LadderResult result = {{{0, 0}}, 0, 0};
    uint64_t count;
    size_t i;
    int matches = 1;

    if (!search_range(2, LADDER_LIMIT, 2, table, collect_ladder_pair,
                      &result, &count)) {
        fprintf(stderr, "ladder k=2 limit=2000: search failed\n");
        return 0;
    }
    if (count != result.total || result.total != LADDER_PAIRS ||
        result.stored != LADDER_PAIRS) {
        matches = 0;
    }
    qsort(result.pairs, result.stored, sizeof(result.pairs[0]), pair_compare);
    if (matches) {
        for (i = 0; i < LADDER_PAIRS; ++i) {
            if (result.pairs[i].x != expected[i].x ||
                result.pairs[i].y != expected[i].y) {
                matches = 0;
                break;
            }
        }
    }
    if (!matches) {
        fprintf(stderr, "ladder k=2 limit=2000: mismatch; got");
        for (i = 0; i < result.stored; ++i) {
            fprintf(stderr, " (%" PRIu32 ",%" PRIu32 ")",
                    result.pairs[i].x, result.pairs[i].y);
        }
        if (result.total > result.stored) {
            fprintf(stderr, " ... (%" PRIu64 " total)", result.total);
        }
        fputc('\n', stderr);
        return 0;
    }
    fprintf(stderr, "ladder k=2 limit=2000: ok (5 pairs)\n");
    return 1;
}

static uint64_t peak_rss_kb(void) {
#if HAVE_GETRUSAGE
    struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage) == 0) {
#if defined(__APPLE__)
        return (uint64_t)usage.ru_maxrss / 1024U;
#else
        return (uint64_t)usage.ru_maxrss;
#endif
    }
#endif
    return 0;
}

int main(int argc, char **argv) {
    PrimeTable table;
    uint64_t limit64 = 0;
    uint64_t from64 = 2;
    uint64_t steps64 = 3;
    uint64_t pair_count;
    uint64_t rss;
    int have_limit = 0;
    int i;

    for (i = 1; i < argc; ++i) {
        uint64_t *destination;
        if (strcmp(argv[i], "--help") == 0) {
            usage(stdout, argv[0]);
            return 0;
        }
        if (strcmp(argv[i], "--limit") == 0) {
            destination = &limit64;
            have_limit = 1;
        } else if (strcmp(argv[i], "--steps") == 0) {
            destination = &steps64;
        } else if (strcmp(argv[i], "--from") == 0) {
            destination = &from64;
        } else {
            fprintf(stderr, "unknown option: %s\n", argv[i]);
            usage(stderr, argv[0]);
            return 2;
        }
        if (++i == argc || !parse_u64(argv[i], destination)) {
            fprintf(stderr, "invalid or missing value for %s\n", argv[i - 1]);
            usage(stderr, argv[0]);
            return 2;
        }
    }

    if (!have_limit) {
        fprintf(stderr, "--limit is required\n");
        usage(stderr, argv[0]);
        return 2;
    }
    if (steps64 == 0 || steps64 > MAX_STEPS) {
        fprintf(stderr, "--steps must be in 1..%u\n", MAX_STEPS);
        return 2;
    }
    if (limit64 > UINT32_MAX - (steps64 - 1U)) {
        fprintf(stderr,
                "--limit plus --steps minus one must not exceed %" PRIu32 "\n",
                UINT32_MAX);
        return 2;
    }
    if (from64 < 2 || from64 > UINT32_MAX) {
        fprintf(stderr, "--from must be in 2..%" PRIu32 "\n", UINT32_MAX);
        return 2;
    }
    if (!build_prime_table(&table)) {
        fprintf(stderr, "internal error: prime table capacity exceeded\n");
        return 1;
    }
    if (!verify_ladder(&table)) {
        return 1;
    }
    if (!search_range((uint32_t)from64, (uint32_t)limit64,
                      (uint32_t)steps64, &table, print_pair, NULL,
                      &pair_count)) {
        return 1;
    }
    if (fflush(stdout) != 0) {
        fprintf(stderr, "failed to flush pair output\n");
        return 1;
    }

    rss = peak_rss_kb();
    fprintf(stderr,
            "reached=%" PRIu64 " steps=%" PRIu64 " pairs=%" PRIu64,
            limit64, steps64, pair_count);
    if (rss != 0) {
        fprintf(stderr, " peak_rss_kb=%" PRIu64, rss);
    } else {
        fprintf(stderr, " peak_rss_kb=unavailable");
    }
    fputc('\n', stderr);
    return 0;
}
