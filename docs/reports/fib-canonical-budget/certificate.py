#!/usr/bin/env python3
"""Exact finite-future signatures by local trees and common-phase supports.

Python 3.8+ standard library only. No input files or global residue-state graph.
Repository source; distributed under the root Apache-2.0 LICENSE.
"""

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import product
import json
from math import gcd, prod
from pathlib import Path
import sys


ALPHABET = ("000", "100", "010", "101", "001")
FACTORS = (16, 9, 5, 7)
H = prod(FACTORS)
TAGS = ((0, False), (0, True), (1, True))
ERROR = "error"


def check(condition, message):
    """Checks remain active with python -O."""
    if not condition:
        raise ValueError(message)


def weight_orbit(modulus):
    rows, seen = [], set()
    pair = (2 % modulus, 3 % modulus)
    while pair not in seen:
        seen.add(pair)
        rows.append(pair)
        u, v = pair
        pair = ((u + 2 * v) % modulus, (2 * u + 3 * v) % modulus)
    check(pair == rows[0], "weight orbit has a transient part")
    return rows


@lru_cache(None)
def step(modulus, state, letter):
    """Local one-bit recurrence; state order is r,u,v,seam,End."""
    if state is None:
        return None
    r, u, v, seam, end = state
    for bit in map(int, letter):
        if seam and bit:
            return None
        r = (r + bit * u) % modulus
        u, v = v, (u + v) % modulus
        seam = bit
    return (r, u, v, seam, letter != "000")


# Pools are separate for each modulus and depth. IDs refer to exact tuples,
# never to a digest: dictionary hash collisions still compare complete keys.
intern = defaultdict(dict)
trees = defaultdict(list)


@lru_cache(None)
def signature(modulus, depth, state):
    out = ERROR if state is None or not state[4] else modulus // gcd(state[0], modulus)
    children = () if depth == 0 else tuple(
        signature(modulus, depth - 1, step(modulus, state, b)) for b in ALPHABET
    )
    key = (out, children)
    pool = intern[modulus, depth]
    if key not in pool:
        pool[key] = len(pool)
        trees[modulus, depth].append(key)
    return pool[key]


def tree_output(modulus, depth, sig, word):
    for letter in word:
        sig = trees[modulus, depth][sig][1][ALPHABET.index(letter)]
        depth -= 1
    return trees[modulus, depth][sig][0]


def phase_supports(modulus, depth, tag, phases):
    supports = {}
    seam, end = tag
    for j, (u, v) in enumerate(phases):
        for r in range(modulus):
            sig = signature(modulus, depth, (r, u % modulus, v % modulus, seam, end))
            supports[sig] = supports.get(sig, 0) | (1 << j)
    return supports


def intersect_histograms(histograms, full):
    dp, widths = {full: 1}, []
    for histogram in histograms:
        next_dp = Counter()
        for oldmask, oldcount in dp.items():
            for localmask, multiplicity in histogram.items():
                intersection = oldmask & localmask
                if intersection:
                    next_dp[intersection] += oldcount * multiplicity
        dp = dict(next_dp)
        widths.append(len(dp))
    return dp, widths


def hex_histogram(histogram, period):
    return {format(mask, "0{}x".format((period + 3) // 4)): count
            for mask, count in sorted(histogram.items())}


def literal_decode(epsilon, windows):
    """Independent integer decoder: build F_n, then sum selected positions.

    This does not call the modular step function or construct a global graph.
    Even an invalid word is read literally; invalidity remains absorbing.
    """
    check(epsilon in (0, 1), "invalid initialization")
    check(all(b in ALPHABET for b in windows), "letter outside the alphabet")
    bits = (epsilon,) + tuple(int(bit) for b in windows for bit in b)
    fib = [0, 1]
    for _ in range(3 * len(windows) + 3):
        fib.append(fib[-1] + fib[-2])
    live = all(not (a and b) for a, b in zip(bits, bits[1:]))
    value = sum(bit * fib[i + 2] for i, bit in enumerate(bits))
    end = bool(epsilon) if not windows else windows[-1] != "000"
    out = H // gcd(value, H) if live and end and value > 0 else ERROR
    return {"live": live, "N": value, "row": fib[-2:],
            "tag": [bits[-1], end], "output": out}


def words_through(depth):
    return [word for n in range(depth + 1) for word in product(ALPHABET, repeat=n)]


def literal_checks():
    prefixes = (
        ("010", "100", "100", "100", "010", "000", "000", "000", "000", "001"),
        ("100", "000", "101", "000", "010", "100", "000", "000", "000", "001"),
    )
    decoded = [literal_decode(0, p) for p in prefixes]
    check([d["N"] for d in decoded] == [2179485, 2182005], "section 107.7 integers")
    check(all(d["live"] and d["row"] == [3524578, 5702887]
              and d["tag"] == [1, True] for d in decoded), "section 107.7 states")
    short_tests = {}
    for word in words_through(2):
        outputs = [literal_decode(0, p + word)["output"] for p in prefixes]
        check(outputs[0] == outputs[1], "S2 counterexample pair disagrees on a short word")
        short_tests["|".join(word)] = outputs[0]
    one_tests = {}
    for word in words_through(1):
        outputs = [literal_decode(0, p + ("000",) + word)["output"] for p in prefixes]
        check(outputs[0] == outputs[1], "S1 successor pair disagrees")
        one_tests["|".join(word)] = outputs[0]
    witness = ("000", "000", "010")
    outputs = [literal_decode(0, p + witness)["output"] for p in prefixes]
    check(outputs == [6, 3], "fixed-layer Q2/Q1 separating suffix")

    # Actual A prefix and actual invalid sink, both epsilon=0.
    zero_prefixes = (("000",), ("001", "100"))
    zero_before = [literal_decode(0, p)["output"] for p in zero_prefixes]
    zero_after = [literal_decode(0, p + ("010",))["output"] for p in zero_prefixes]
    check(zero_before == [ERROR, ERROR], "Q0 initial equality")
    check(zero_after == [5040, ERROR], "Q0 separation by 010")

    # Compare local trees to literal decoding on four concrete prefixes and
    # all 156 suffixes through depth 3; this includes both initializations.
    samples = [(0, p) for p in prefixes] + [(1, ()), (0, zero_prefixes[1])]
    comparisons = 0
    for epsilon, prefix in samples:
        source = literal_decode(epsilon, prefix)
        ids = []
        for h in FACTORS:
            state = None if not source["live"] else (
                source["N"] % h, source["row"][0] % h, source["row"][1] % h,
                *source["tag"])
            ids.append(signature(h, 3, state))
        for word in words_through(3):
            out = literal_decode(epsilon, prefix + word)["output"]
            local = [tree_output(h, 3, sig, word) for h, sig in zip(FACTORS, ids)]
            expected = [ERROR] * len(FACTORS) if out == ERROR else [gcd(out, h) for h in FACTORS]
            check(local == expected, "local tree versus literal output")
            check((ERROR if ERROR in local else prod(local)) == out, "CRT output reconstruction")
            comparisons += len(FACTORS)
    return {"prefixes": [{"epsilon": 0, "windows": list(p), **d}
                         for p, d in zip(prefixes, decoded)],
            "S2_shared_outputs": short_tests, "S1_shared_outputs_after_000": one_tests,
            "separating_suffix": list(witness), "separating_outputs": outputs,
            "Q0": {"epsilon": 0, "prefixes": [list(p) for p in zero_prefixes],
                   "before": zero_before, "letter": "010", "after": zero_after},
            "local_tree_literal_coordinate_comparisons": comparisons}


def certificate():
    check(all(gcd(a, b) == 1 for i, a in enumerate(FACTORS) for b in FACTORS[i + 1:]),
          "CRT factors are not pairwise coprime")
    phases = weight_orbit(H)
    period, full = len(phases), (1 << len(phases)) - 1
    periods = {str(h): len(weight_orbit(h)) for h in FACTORS}
    for h in FACTORS:
        local_rows = weight_orbit(h)
        check(all((u % h, v % h) == local_rows[j % len(local_rows)]
                  for j, (u, v) in enumerate(phases)), "common-phase projection")
    results, histograms_record, zero_images = [], [], []
    for depth in range(4):
        modes = []
        for tag in TAGS:
            supports = [phase_supports(h, depth, tag, phases) for h in FACTORS]
            histograms = [Counter(s.values()) for s in supports]
            dp, widths = intersect_histograms(histograms, full)
            modes.append({"tags": list(tag), "count": sum(dp.values()),
                          "local_signature_counts": [len(s) for s in supports],
                          "dp_widths": widths})
            histograms_record.append({"depth": depth, "tags": list(tag),
                "local_histograms": [hex_histogram(h, period) for h in histograms],
                "final_intersection_histogram": hex_histogram(dp, period)})
            if depth == 0:
                check(all(mask == full for s in supports for mask in s.values()),
                      "depth-zero label missing a phase")
                labels = [[trees[h, 0][sig][0] for sig in s] for h, s in zip(FACTORS, supports)]
                image = {ERROR if ERROR in values else prod(values) for values in product(*labels)}
                check(len(image) == modes[-1]["count"], "depth-zero tuple/label bijection")
                zero_images.append(image)
        total = len({ERROR}.union(*zero_images)) if depth == 0 else 1 + sum(m["count"] for m in modes)
        results.append({"depth": depth, "total": total, "modes": modes})
    divisors = {d for d in range(1, H + 1) if H % d == 0}
    check(zero_images == [{ERROR}, divisors, divisors], "depth-zero tag overlap")
    maximum_width = max(w for r in results for m in r["modes"] for w in m["dp_widths"])

    # Regression expectations are checked only after the complete derivation;
    # none supplies a count, signature, support mask, or stopping condition.
    check(period == 80 and periods == {"16": 8, "9": 8, "5": 20, "7": 16}, "phase periods")
    check([[m["count"] for m in r["modes"]] for r in results] ==
          [[1, 60, 60], [11790, 31096, 5572], [189000, 189000, 157500],
           [201600, 201600, 201600]], "fixed-tag counts")
    check([r["total"] for r in results] == [61, 48459, 535501, 604801], "actual signature totals")
    check(results[1]["modes"][0]["local_signature_counts"] == [17, 20, 9, 9], "t1 tag A marginals")
    check(maximum_width == 216, "finite DP width regression")
    return {"scope": {"H": H, "factors": list(FACTORS), "alphabet": list(ALPHABET),
                      "depths": [0, 1, 2, 3], "initializations": [0, 1],
                      "past": "arbitrary finite actual prefixes, including the invalid sink",
                      "budget": "remaining future windows starting at the current prefix; End costs zero",
                      "enumeration": "common weight orbit and local residue/signature models only",
                      "histograms": "distinct local signatures; hexadecimal bit j denotes common phase j",
                      "factor_order": list(FACTORS)},
            "global_weight_phase_period": period, "global_weight_phases": phases,
            "local_weight_phase_periods": periods, "results": results,
            "depth_zero": {"positive_labels": sorted(divisors), "A_and_sink": ERROR,
                           "B_and_C_same_label_image": True},
            "maximum_dp_width": maximum_width,
            "all_local_support_histograms_and_final_intersections": histograms_record,
            "literal_decoder_checks": literal_checks()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write JSON here instead of stdout")
    args = parser.parse_args()
    payload = (json.dumps(certificate(), sort_keys=True, indent=2) + "\n").encode("utf-8")
    if args.output is None:
        sys.stdout.buffer.write(payload)
    else:
        args.output.write_bytes(payload)


if __name__ == "__main__":
    main()
