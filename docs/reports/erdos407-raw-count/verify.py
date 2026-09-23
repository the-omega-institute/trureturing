#!/usr/bin/env python3
"""Exact finite checker for the MFH2025/OEIS A387688 raw count.

The checker is deliberately stdlib-only.  It compares direct quadruple
enumeration with an independently aggregated Counter convolution and checks
the published finite summaries and witnesses.  The --negative-control mode
deduplicates repeated pure sums, corrupting the counting semantics, and must
fail.
"""

from collections import Counter, defaultdict
import argparse
import sys


B = 76_546_075
EXPECTED_CANDIDATES = 210_681
EXPECTED_ACCEPTED = 106_750
EXPECTED_REPRESENTED = 82_943
EXPECTED_SUM_NR = 1_545_759_402_665
EXPECTED_SUM_R2 = 173_506
EXPECTED_R_HIST = {
    1: 65019,
    2: 14228,
    3: 2283,
    4: 1026,
    5: 193,
    6: 93,
    7: 46,
    8: 31,
    9: 15,
    10: 6,
    11: 2,
    12: 1,
}
EXPECTED_LAST = {7: 2563, 8: 2267, 9: 515, 10: 299, 11: 161, 12: 37}
EXPECTED_CLASS_HIST = {1: 88197, 2: 8657, 3: 413}
EXPECTED_CLASS_MAX = 3
EXPECTED_CLASS_WITNESS = (6, (1, 2, 3))

ANCHORS = {
    2563: [
        (4, 5, 8, 2), (8, 1, 8, 2), (9, 1, 11, 0),
        (10, 1, 9, 1), (10, 4, 1, 6), (10, 5, 4, 4), (11, 1, 9, 0),
    ],
    2267: [
        (1, 6, 9, 1), (3, 7, 3, 2), (4, 7, 6, 0), (5, 7, 4, 1),
        (6, 7, 4, 0), (9, 3, 6, 3), (11, 1, 3, 3), (11, 3, 6, 1),
    ],
    515: [
        (1, 0, 9, 0), (1, 3, 1, 5), (1, 4, 4, 3), (4, 5, 8, 0),
        (7, 1, 7, 1), (7, 5, 4, 2), (8, 1, 8, 0), (8, 5, 4, 0), (9, 0, 1, 0),
    ],
    299: [
        (1, 2, 5, 2), (1, 4, 3, 3), (1, 5, 1, 3), (3, 1, 5, 2),
        (3, 5, 4, 1), (4, 3, 8, 0), (5, 5, 3, 1), (7, 2, 1, 4),
        (7, 3, 4, 2), (8, 3, 4, 0),
    ],
    161: [
        (3, 2, 4, 2), (3, 4, 3, 2), (4, 0, 4, 2), (4, 4, 6, 0),
        (5, 0, 7, 0), (5, 4, 4, 1), (6, 0, 5, 1), (6, 4, 4, 0),
        (7, 0, 5, 0), (7, 2, 3, 1), (7, 3, 1, 1),
    ],
    37: [
        (0, 2, 0, 3), (0, 3, 0, 2), (1, 1, 5, 0), (1, 3, 3, 0),
        (2, 0, 5, 0), (2, 2, 3, 1), (2, 3, 1, 1), (3, 3, 1, 0),
        (4, 1, 1, 2), (4, 2, 2, 1), (5, 0, 2, 0), (5, 1, 1, 0),
    ],
}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def powers(base, maximum):
    values = []
    value = 1
    while value <= maximum:
        values.append(value)
        value *= base
    return values


def direct_enumeration(two, three):
    counts = Counter()
    tuples_by_n = defaultdict(list)
    class_counts = Counter()
    class_multisets = {}
    candidates = 0
    for r, p2 in enumerate(two):
        for s, p3 in enumerate(three):
            pure = p2 + p3
            for t, mixed_base in enumerate(two):
                for u, p3u in enumerate(three):
                    candidates += 1
                    n = pure + mixed_base * p3u
                    if n <= B:
                        q = (r, s, t, u)
                        counts[n] += 1
                        tuples_by_n[n].append(q)
                        values = (p2, p3, mixed_base * p3u)
                        terms = tuple(sorted(set(values)))
                        multiset = tuple(sorted(values))
                        key = (n, terms)
                        if key in class_multisets:
                            require(class_multisets[key] == multiset,
                                    f"fixed-N set-to-multiset failure at N={n}, C={terms}")
                        else:
                            class_multisets[key] = multiset
                        class_counts[key] += 1
    return candidates, counts, tuples_by_n, class_counts, class_multisets


def convolution(two, three, deduplicate=False):
    pure_values = [p2 + p3 for p2 in two for p3 in three]
    mixed_values = [p2 * p3 for p2 in two for p3 in three]
    if deduplicate:
        pure_values = sorted(set(pure_values))
    pure = Counter(pure_values)
    mixed = Counter(mixed_values)
    result = Counter()
    for left, left_count in pure.items():
        for right, right_count in mixed.items():
            n = left + right
            if n <= B:
                result[n] += left_count * right_count
    return result


def check_summary(counts):
    require(sum(counts.values()) == EXPECTED_ACCEPTED,
            "accepted tuple count mismatch")
    require(len(counts) == EXPECTED_REPRESENTED,
            "represented-N count mismatch")
    require(sum(n * r for n, r in counts.items()) == EXPECTED_SUM_NR,
            "sum N*R(N) mismatch")
    require(sum(r * r for r in counts.values()) == EXPECTED_SUM_R2,
            "sum R(N)^2 mismatch")
    histogram = Counter(counts.values())
    require(dict(histogram) == EXPECTED_R_HIST, "R histogram mismatch")
    require(max(counts.values()) == 12, "maximum R mismatch")
    require([n for n, r in counts.items() if r == 12] == [37],
            "maximum index mismatch")
    last = {k: max(n for n, r in counts.items() if r == k) for k in EXPECTED_LAST}
    require(last == EXPECTED_LAST, "last occurrence mismatch")


def is_nontrivial_power(value, base):
    if value <= 1:
        return False
    while value % base == 0:
        value //= base
    return value == 1


def check_classes(counts, class_counts, class_multisets):
    require(set(class_counts) == set(class_multisets),
            "set-class and multiset key sets differ")
    by_n = defaultdict(int)
    for (n, _terms), multiplicity in class_counts.items():
        by_n[n] += multiplicity
    require(dict(by_n) == dict(counts), "set-class fibers do not recover R(N)")
    class_hist = Counter(class_counts.values())
    require(dict(class_hist) == EXPECTED_CLASS_HIST, "class-fiber histogram mismatch")
    maximum = max(class_counts.values())
    require(maximum == EXPECTED_CLASS_MAX, "class-fiber maximum mismatch")
    witness = [key for key, value in class_counts.items() if value == maximum]
    require(EXPECTED_CLASS_WITNESS in witness, "class-fiber witness missing")
    for (_n, terms), multiplicity in class_counts.items():
        fiber_three_shape = (
            len(terms) == 3
            and terms[0] == 1
            and (
                (is_nontrivial_power(terms[1], 2)
                 and is_nontrivial_power(terms[2], 3))
                or
                (is_nontrivial_power(terms[1], 3)
                 and is_nontrivial_power(terms[2], 2))
            )
        )
        require((multiplicity == 3) == fiber_three_shape,
                f"fiber-three characterization failed for C={terms}")


def require_equal_counters(direct, aggregated):
    if direct == aggregated:
        return
    differing = next(
        n for n in sorted(set(direct) | set(aggregated))
        if direct[n] != aggregated[n]
    )
    raise AssertionError(
        "direct and convolution Counters differ at "
        f"N={differing}: direct={direct[differing]} "
        f"convolution={aggregated[differing]}"
    )


def check_anchors(tuples_by_n):
    require(sum(len(expected) for expected in ANCHORS.values()) == 57,
            "anchor fixture count mismatch")
    for n, expected in ANCHORS.items():
        actual = set(tuples_by_n[n])
        require(len(actual) == len(expected) == len(tuples_by_n[n]),
                f"anchor {n} has duplicate or unexpected tuples")
        require(actual == set(expected), f"anchor {n} witness mismatch")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--negative-control", action="store_true",
                        help="deduplicate pure sums; expected to fail")
    args = parser.parse_args(argv)

    two = powers(2, B)
    three = powers(3, B)
    require(len(two) == 27 and len(three) == 17,
            "integer exponent bounds are not 26 and 16")
    require(two[-1] == 2 ** 26 and two[-1] * 2 > B,
            "2-adic completeness boundary failed")
    require(three[-1] == 3 ** 16 and three[-1] * 3 > B,
            "3-adic completeness boundary failed")

    candidates, counts, tuples_by_n, class_counts, class_multisets = \
        direct_enumeration(two, three)
    require(candidates == EXPECTED_CANDIDATES, "candidate tuple count mismatch")
    check_summary(counts)
    check_classes(counts, class_counts, class_multisets)
    check_anchors(tuples_by_n)

    aggregated = convolution(two, three, deduplicate=args.negative_control)
    require_equal_counters(counts, aggregated)
    print("verified exact finite prefix")
    print(f"B={B} candidates={candidates} accepted={sum(counts.values())} "
          f"represented={len(counts)} max_R={max(counts.values())}")
    print(f"last_occurrences={EXPECTED_LAST}")
    print(f"class_histogram={EXPECTED_CLASS_HIST} max_class=3 witness=(6,(1,2,3))")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, ValueError) as error:
        print(f"verification failed: {error}", file=sys.stderr)
        raise SystemExit(2)
