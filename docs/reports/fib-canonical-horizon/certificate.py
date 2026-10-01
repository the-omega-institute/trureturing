#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Exact finite Fibonacci checks; Python 3.8+ standard library only."""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys

SYMBOLS = ("000", "100", "010", "101", "001")
ERROR = "ERROR"


class CertificateFailure(Exception):
    pass


def check(ok, condition, evidence):
    """Fail with an explicit mathematical counterexample, including under -O."""
    if not ok:
        raise CertificateFailure(json.dumps(
            {"condition": condition, "counterexample": evidence}, sort_keys=True))


def fibonacci_to(limit):
    f = [0, 1]
    while f[-1] <= limit:
        f.append(f[-1] + f[-2])
    return f


def exact_a(n):
    x = n + 1
    a = (math.isqrt(5 * x * x) - x) // 2
    # Independent integer inequalities for a <= x/phi < a+1.
    check(0 <= 2 * a + x and (2 * a + x) ** 2 <= 5 * x * x
          < (2 * a + x + 2) ** 2, "floor square bounds", [n, a])
    return a


def row_value(bits, u, v):
    total = 0
    for bit in bits:
        total += int(bit) * u
        u, v = v, u + v
    return total


def coefficient_witness(h, p, A, B, t, n, a):
    # Greedy integer decomposition, independent of the isqrt formula.
    f = fibonacci_to(n)
    remaining, support = n, []
    for k in range(len(f) - 1, 1, -1):
        if f[k] <= remaining:
            support.append(k)
            remaining -= f[k]
    check(bool(support), "nonempty positive Zeckendorf support", [h, A, B, n])
    highest = max(support)
    digits = ["0"] * (highest + 1)
    for k in support:
        digits[k] = "1"
    padding = (-len(digits)) % 3
    bits = "".join(digits) + "0" * padding
    ca, cb = row_value(bits, 1, 0), row_value(bits, 0, 1)
    selected = row_value(bits, 1, 2)
    seam_legal = ["11" not in str(s) + bits for s in (0, 1)]
    evidence = [h, A, B, t, n, a, bits, ca, cb, selected]
    check(remaining == 0 and all(x - y >= 2 for x, y in zip(support, support[1:])),
          "greedy nonadjacent decomposition", evidence)
    check(bits.startswith("00") and all(seam_legal) and bits[-3:] != "000"
          and 0 <= padding <= 2 and len(bits) % 3 == 0 and len(bits) <= 3 * p["L"],
          "canonical two-seam bounded word", evidence)
    check((ca, cb) == (a, n) and (ca % h, cb % h) == (A, B)
          and 1 <= t <= p["q"] and n == B + h * t
          and 0 < n < p["bound_exclusive"] and selected == a + 2 * n > 0,
          "independent coefficient and positivity reconstruction", evidence)
    return {"A": A, "B": B, "t": t, "n": n, "a": a, "bits_low_first": bits,
            "exact_coefficients": [ca, cb], "value_at_row_1_2": selected}


def class_vector(signatures):
    classes, vector = {}, []
    for signature in signatures:
        if signature not in classes:
            classes[signature] = len(classes)
        vector.append(classes[signature])
    return vector


def literal_end(code, suffix):
    epsilon, prefix_windows = code
    windows = prefix_windows + list(suffix)
    bits = str(epsilon) + "".join(windows)
    value, u, v, previous, legal = 0, 1, 2, 0, True
    for char in bits:
        bit = int(char)
        legal = legal and not (previous and bit)
        value += bit * u
        u, v = v, u + v
        previous = bit
    canonical = windows[-1] != "000" if windows else epsilon == 1
    positive = value > 0
    output = 5040 // math.gcd(value, 5040) if legal and canonical and positive else ERROR
    return {"bits_low_first": bits, "integer": value, "legal": legal,
            "canonical_last_triple": canonical, "positive": positive,
            "output": output, "next_row": [u, v], "last_bit": previous}


def greedy_actual(n):
    # Direct canonical encoding using actual weights 1,2,3,5,... .
    weights = [1, 2]
    while weights[-1] <= n:
        weights.append(weights[-1] + weights[-2])
    digits, remainder = ["0"] * len(weights), n
    for k in range(len(weights) - 1, -1, -1):
        if weights[k] <= remainder:
            digits[k] = "1"
            remainder -= weights[k]
    while digits[-1] == "0":
        digits.pop()
    bits = "".join(digits)
    bits += "0" * ((1 - len(bits)) % 3)
    check(remainder == 0 and "11" not in bits, "actual greedy encoding", [n, bits, remainder])
    return bits


def parameters(h):
    f = fibonacci_to(2 * h)
    j, q = len(f) - 1, f[-1]
    bound = h * (q + 1)
    while f[-1] < bound:
        f.append(f[-1] + f[-2])
    m = next(k for k, x in enumerate(f) if x >= bound)
    p = {"H": h, "j": j, "q": q, "bound_exclusive": bound,
         "m": m, "L": (m + 2) // 3, "F_m_minus_1": f[m - 1],
         "F_m": f[m], "F_j_minus_1": f[j - 1]}
    check(f[j - 1] <= 2 * h < q and f[m - 1] < bound <= f[m]
          and 3 * (p["L"] - 1) < m <= 3 * p["L"], "minimal q,m,L bounds", p)
    return p


def sample_targets():
    """Fixed target generator, independent of all coefficient outcomes."""
    residues = (0, 1, 2, 3, 5036, 5037, 5038, 5039)
    pairs = list(itertools.product(residues, repeat=2))
    seen, counter = set(pairs), 0
    while len(pairs) < 256:
        digest = hashlib.sha256(
            ("fib-canonical-horizon-5040-sample-v1:" + str(counter)).encode("ascii")
        ).digest()
        pair = tuple(int.from_bytes(part, "big") % 5040
                     for part in (digest[:16], digest[16:]))
        counter += 1
        if pair not in seen:
            pairs.append(pair)
            seen.add(pair)
    check(len(seen) == 256 and all(0 <= x < 5040 for pair in pairs for x in pair),
          "sample target domain", pairs)
    return pairs, counter


def small_coverage():
    results, selected = [], []
    for h in range(2, 65):
        p, found = parameters(h), {}
        for B in range(h):
            for t in range(1, p["q"] + 1):
                n = B + h * t
                a = exact_a(n)
                found.setdefault((a % h, B), (t, n, a))
        missing = [(A, B) for A in range(h) for B in range(h) if (A, B) not in found]
        check(not missing, "exhaustive coefficient coverage", {"H": h, "missing": missing})
        maximum = 0
        for A, B in sorted(found):
            w = coefficient_witness(h, p, A, B, *found[A, B])
            maximum = max(maximum, len(w["bits_low_first"]) // 3)
            if h in (2, 64) and (A, B) == (0, 0):
                selected.append({"H": h, **w})
        results.append({**p, "candidate_evaluations": h * p["q"],
                        "targets": h * h, "covered": len(found),
                        "maximum_witness_windows": maximum})
    return {"per_H": results, "targets": sum(r["targets"] for r in results),
            "candidate_evaluations": sum(r["candidate_evaluations"] for r in results),
            "selected_witnesses": selected}


def sampled_coverage():
    pairs, counters = sample_targets()
    p, maximum, selected = parameters(5040), 0, []
    for A, B in pairs:
        first = None
        for t in range(1, p["q"] + 1):
            n = B + 5040 * t
            a = exact_a(n)
            if a % 5040 == A and first is None:
                first = (t, n, a)
        check(first is not None, "fixed 5040 target coverage", [A, B])
        w = coefficient_witness(5040, p, A, B, *first)
        maximum = max(maximum, len(w["bits_low_first"]) // 3)
        if (A, B) in ((0, 0), (1, 0), (0, 5039), (5039, 5039)):
            selected.append(w)
    return {**p, "targets": len(pairs), "covered": len(pairs),
            "sample_fill_counters": counters,
            "sample_pairs_sha256": hashlib.sha256(json.dumps(
                pairs, separators=(",", ":")).encode("ascii")).hexdigest(),
            "candidate_evaluations": len(pairs) * p["q"],
            "maximum_witness_windows": maximum, "selected_witnesses": selected}


def local_automaton(h):
    """Construct a closed product cover, without a reachability assumption."""
    start = (2 % h, 3 % h)
    orbit, seen, row = [], set(), start
    while row not in seen:
        seen.add(row)
        orbit.append(row)
        u, v = row
        row = ((u + 2 * v) % h, (2 * u + 3 * v) % h)
    check(row == start, "row orbit returns to initial row", [h, row])
    tags = ((0, False), (0, True), (1, True))
    states = [(r, u, v, s, e) for r in range(h) for u, v in orbit for s, e in tags]
    ids = {state: i for i, state in enumerate(states)}
    sink = len(states)
    initial = [(epsilon, *start, epsilon, bool(epsilon)) for epsilon in (0, 1)]
    check(all(state in ids for state in initial), "both initial states included", [h, initial])
    edges, outputs = [], []
    for i, state in enumerate(states):
        r, u, v, s, e = state
        outputs.append(h // math.gcd(r, h) if e else ERROR)
        successors = []
        for block in SYMBOLS:
            b0, b1, b2 = map(int, block)
            target = None if s and b0 else (
                (r + (b0 + b2) * u + (b1 + b2) * v) % h,
                (u + 2 * v) % h, (2 * u + 3 * v) % h, b2, block != "000")
            check(target is None or target in ids, "transition closure", [h, state, block, target])
            successors.append(sink if target is None else ids[target])
            # Independent single-bit update checks the five triple formulas.
            rr, x, y, previous, legal = r, u, v, s, True
            occupied = False
            for char in block:
                bit = int(char)
                legal = legal and not (previous and bit)
                occupied = occupied or bool(bit)
                rr = (rr + bit * x) % h
                x, y = y, (x + y) % h
                previous = bit
            rebuilt = (rr, x, y, previous, occupied) if legal else None
            check(target == rebuilt, "independent bitwise transition", [h, i, block, target, rebuilt])
        edges.append(successors)
    outputs.append(ERROR)
    edges.append([sink] * len(SYMBOLS))
    check(outputs[sink] == ERROR and all(t == sink for t in edges[sink]),
          "INVALID absorbing error", [h, sink])
    check([outputs[ids[s]] for s in initial] == [ERROR, h], "initial End outputs", h)
    recoveries = 0
    for i, state in enumerate(states):
        if not state[-1]:
            target = edges[i][SYMBOLS.index("010")]
            check(outputs[i] == ERROR and target != sink and outputs[target] != ERROR,
                  "E=false is recoverable", [h, state, target])
            recoveries += 1
    # P0 is End. P(k+1) retains Pk and all five successor Pk classes.
    # IDs are canonical first-occurrence IDs, so vector equality is relation equality.
    prev = class_vector(outputs)
    counts = [len(set(prev))]
    depth = 0
    while True:
        nxt = class_vector((prev[i], *(prev[t] for t in edge))
                           for i, edge in enumerate(edges))
        parent = {}
        for old, new in zip(prev, nxt):
            check(parent.setdefault(new, old) == old, "monotone refinement", [h, old, new])
        counts.append(len(set(nxt)))
        if nxt == prev:
            break
        prev = nxt
        depth += 1
        check(depth <= len(outputs), "finite refinement termination", [h, depth])
    signatures = {}
    for i, label in enumerate(prev):
        signature = (outputs[i], *(prev[t] for t in edges[i]))
        check(signatures.setdefault(label, signature) == signature,
              "stable output and successor congruence", [h, i, label, signature])
    return {"H": h, "row_orbit_length": len(orbit), "states": len(outputs),
            "edges": sum(map(len, edges)), "initial_states": initial,
            "recoverable_E_false_states": recoveries, "class_counts_P0_onward": counts,
            "stable_depth": depth, "equal_relations": [depth, depth + 1],
            "output_successor_congruence": True}


def actual_lower_witness():
    integers = (2179485, 2182005)
    bits = [greedy_actual(n) for n in integers]
    codes = [(int(b[0]), [b[k:k + 3] for k in range(1, len(b), 3)]) for b in bits]
    prefixes = [literal_end(code, ()) for code in codes]
    for n, p in zip(integers, prefixes):
        check(p["integer"] == n and p["legal"] and p["positive"]
              and p["canonical_last_triple"], "actual canonical prefix", [n, p])
    check(prefixes[0]["next_row"] == prefixes[1]["next_row"]
          and prefixes[0]["last_bit"] == prefixes[1]["last_bit"] == 1
          and all(p["canonical_last_triple"] for p in prefixes),
          "common actual weight row, seam and E", prefixes)
    totals = []
    for length in range(3):
        equal, errors = 0, 0
        for suffix in itertools.product(SYMBOLS, repeat=length):
            decoded = [literal_end(code, suffix) for code in codes]
            check(decoded[0]["output"] == decoded[1]["output"],
                  "actual prefixes agree through two windows", [suffix, decoded])
            equal += 1
            errors += decoded[0]["output"] == ERROR
        totals.append({"length": length, "equal_outputs": equal, "common_errors": errors})
    check(sum(r["equal_outputs"] for r in totals) == 31, "all suffixes of length 0..2", totals)
    suffix = ("000", "000", "010")
    decoded = [literal_end(code, suffix) for code in codes]
    gcds = [math.gcd(d["integer"], 5040) for d in decoded]
    check([d["integer"] for d in decoded] == [104513640, 104516160]
          and gcds == [840, 1680] and [d["output"] for d in decoded] == [6, 3],
          "actual depth-three distinction", [decoded, gcds])
    return {"H": 5040, "prefixes": prefixes, "suffix_comparisons": totals,
            "distinguishing_suffix": suffix, "distinguishing_decoded": decoded,
            "distinguishing_gcds": gcds, "terminal_horizon_lower_bound": 3}


def counting():
    f = [0, 1]
    while len(f) <= 40:
        f.append(f[-1] + f[-2])
    literals = []
    for L in range(1, 5):
        canonical = set()
        for length in range(1, L + 1):
            for blocks in itertools.product(SYMBOLS, repeat=length):
                bits = "".join(blocks)
                if bits[0] == "0" and "11" not in bits and blocks[-1] != "000":
                    canonical.add(bits)
        ambient = set()
        for tail in itertools.product("01", repeat=3 * L - 1):
            bits = "0" + "".join(tail)
            if "11" not in bits and "1" in bits:
                ambient.add(bits)
        padded = {bits.ljust(3 * L, "0") for bits in canonical}
        counts = [len(canonical), sum(bits.startswith("00") for bits in canonical)]
        check(padded == ambient and len(canonical) == len(padded),
              "canonical padding bijection", [L, len(canonical), len(ambient)])
        check(counts == [f[3 * L + 1] - 1, f[3 * L] - 1], "literal count indexing", [L, counts])
        literals.append({"L": L, "W": counts[0], "W00": counts[1]})
    h2, w, w00 = 5040 ** 2, f[37] - 1, f[36] - 1
    check([w, w00, h2] == [24157816, 14930351, 25401600] and w00 <= w < h2,
          "5040 counting obstruction at 12 windows", [w, w00, h2])
    p = parameters(5040)
    check((p["q"], p["m"], p["L"]) == (10946, 39, 13), "5040 upper parameters", p)
    return {"literal_bijection_checks": literals,
            "bound_5040": {"L": 12, "W": w, "W00": w00, "H_squared": h2,
                           "minimum_missing_coefficient_pairs": h2 - w,
                           "coefficient_depth_lower_bound": 13}}


def run():
    small, sample = small_coverage(), sampled_coverage()
    locals_ = [local_automaton(h) for h in (16, 9, 5, 7)]
    check([a["states"] for a in locals_] == [385, 217, 301, 337]
          and [a["stable_depth"] for a in locals_] == [3, 3, 2, 3],
          "local finite cover results", locals_)
    return {"schema": "fib-canonical-horizon-v1", "status": "passed",
            "coefficient_checks": {"exhaustive_2_through_64": small, "sample_5040": sample},
            "local_covers": locals_, "total_local_states": sum(a["states"] for a in locals_),
            "total_local_edges": sum(a["edges"] for a in locals_),
            "lower_witness": actual_lower_witness(), "counting": counting(),
            "counterexamples": []}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write canonical JSON here (default: stdout)")
    args = parser.parse_args()
    try:
        result = run()
    except CertificateFailure as exc:
        print(str(exc), file=sys.stderr)
        return 1
    data = json.dumps(result, sort_keys=True, indent=2, ensure_ascii=True) + "\n"
    if args.output:
        args.output.write_bytes(data.encode("ascii"))
    else:
        sys.stdout.write(data)
    return 0


if __name__ == "__main__":
    sys.exit(main())
