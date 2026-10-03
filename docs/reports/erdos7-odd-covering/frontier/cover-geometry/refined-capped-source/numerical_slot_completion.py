#!/usr/bin/env python3
"""Exact finite checks for numerical-slot-preserving cap completion.

Ordinary rational checks, not a Lean proof or a noncoverage certificate.
No optimizer, external library, subprocess, or directory traversal is used.
"""
import argparse
import itertools
import json
from fractions import Fraction as F
from pathlib import Path

CHECKS = 0
Q = (5, 7, 11, 13, 17, 19, 23)
CASES = {
    "A": (F(0), F(0), F(2226446, 6816549),
          F(2771867, 6816549), F(1818236, 6816549)),
    "B": (F(394292, 2272183), F(1877891, 2272183), F(0), F(0), F(0)),
}


def check(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ValueError(message)


def simplex(v):
    check(len(v) > 0 and all(x >= 0 for x in v) and sum(v) == 1,
          "not a probability simplex vector")


def prefix(q, k, word):
    check(q >= 3 and k >= 1 and all(0 <= t < k for t in word),
          "invalid prefix data")
    p = [F(0)] * k
    for j, t in enumerate(word, 1):
        p[t] += F(q - 1, q ** j)
    check(sum(p) == 1 - F(1, q ** len(word)), "prefix total")
    return p


def extract(q, v, depth):
    """Membership in F_depth, with the unique accepted digit prefix."""
    simplex(v)
    check(q >= 3 and depth >= 0, "invalid extraction parameters")
    residual = list(v)
    word = []
    history = []
    for j in range(1, depth + 1):
        weight = F(q - 1, q ** j)
        choices = [i for i, x in enumerate(residual) if x >= weight]
        check(len(choices) <= 1, "odd-base uniqueness")
        history.append({"depth": j, "weight": str(weight),
                        "residual_before": list(map(str, residual)),
                        "choices": choices})
        if not choices:
            return {"member": False, "word": word, "history": history}
        t = choices[0]
        residual[t] -= weight
        word.append(t)
        check(all(x >= 0 for x in residual), "negative residual")
        check(sum(residual) == F(1, q ** j), "complete geometric tail")
    return {"member": True, "word": word, "history": history}


def branch_l1(v, p):
    """Exact l1 distance to {z>=p,sum z=1}, with a minimizing point."""
    deficit = sum(max(F(0), a - b) for a, b in zip(p, v))
    z = [max(a, b) for a, b in zip(p, v)]
    excess = deficit
    for i in range(len(z)):
        remove = min(excess, z[i] - p[i])
        z[i] -= remove
        excess -= remove
    check(excess == 0 and sum(z) == 1, "distance projection mass")
    check(all(a >= b for a, b in zip(z, p)), "distance projection branch")
    check(sum(abs(a - b) for a, b in zip(z, v)) == 2 * deficit,
          "distance projection objective")
    return 2 * deficit, z


def domain_distance(q, v, depth):
    best = None
    for word in itertools.product(range(len(v)), repeat=depth):
        p = prefix(q, len(v), word)
        distance, z = branch_l1(v, p)
        row = (distance, word, z)
        if best is None or row[:2] < best[:2]:
            best = row
    return {"distance_l1": str(best[0]), "closest_prefix": list(best[1]),
            "closest_point": list(map(str, best[2])),
            "tail_mass": str(F(1, q ** depth))}


def completion_controls():
    inventories = 0
    for q in (5, 7, 11):
        for k in (2, 3, 5):
            # -1 covers absent labels and present labels missing the live source.
            for labels in itertools.product(range(-1, k), repeat=3):
                raw = [F(0)] * k
                word = []
                for j, t in enumerate(labels, 1):
                    if t >= 0:
                        raw[t] += F(q - 1, q ** j)
                    word.append(t if t >= 0 else 0)
                completed = prefix(q, k, word)
                completed[0] += F(1, q ** 3)
                check(all(a >= b for a, b in zip(completed, raw)),
                      "completion must dominate every actual colour cap")
                check(extract(q, completed, 3)["member"],
                      "slotwise completion must satisfy all prefix constraints")
                inventories += 1
    return inventories


def mixed_controls():
    rows = []
    all_labels = set()
    for mask in range(1, 1 << len(Q)):
        primes = tuple(q for i, q in enumerate(Q) if mask & (1 << i))
        if len(primes) < 2:
            continue
        leading = F(1)
        finite_mass = F(1)
        for q in primes:
            leading *= F(q - 1, q)
            finite_mass *= 1 - F(1, q ** 2)
        direct_sum = F(0)
        for exponents in itertools.product((1, 2), repeat=len(primes)):
            weight = F(1)
            d = 1
            for q, e in zip(primes, exponents):
                d *= q ** e
                weight *= F(q - 1, q ** e)
            direct_sum += weight
            for a in (1, 3, 9):
                check(a * d not in all_labels, "duplicate full numerical label")
                all_labels.add(a * d)
        check(direct_sum == finite_mass, "mixed box geometric product")
        check(0 < leading <= finite_mass < 1, "mixed positive complete tail")
        rows.append({"mask": mask, "leading_weight": str(leading),
                     "box_depth_two_tail": str(1 - finite_mass)})
    return {"supports": len(rows), "distinct_numerical_labels": len(all_labels),
            "support_rows": rows}


def signed_responses(candidate, supports):
    """Independent monomer/mixed-block recurrence on all 128 prime subsets."""
    stars = candidate["stars"]
    colours = candidate["support_colors"]
    check(len(stars) == 7 and len(colours) == 120, "complete common table")
    for pieces in stars:
        simplex(tuple(F(w) for w, _ in pieces))
        check(all(r in (0, 1) and 0 <= t < 5 for _, (r, t) in pieces),
              "invalid star role")
    result = []
    for leaf in range(5):
        masses = [1 - F(1, q - 2) * sum(
            F(w) * (int((leaf >= 2) == bool(r)) + int(leaf == t))
            for w, (r, t) in pieces) for q, pieces in zip(Q, stars)]
        check(all(0 <= x <= 1 for x in masses), "star mass domain")
        factors = {}
        for support, spec in zip(supports, colours):
            pairs = [(spec, F(1))] if isinstance(spec, int) else [
                (j, F(w)) for j, w in spec]
            simplex(tuple(w for _, w in pairs))
            check(all(0 <= j < 10 for j, _ in pairs), "invalid common colour")
            cap = F(1)
            for i, q in enumerate(Q):
                if support >> i & 1:
                    cap /= q - 2
            factors[support] = cap * sum(w * (
                1 + int((leaf >= 2) == bool(j // 5)) + int(leaf == j % 5))
                for j, w in pairs)
        values = [F(1)] + [F(0)] * 127
        for mask in range(1, 128):
            bit = mask & -mask
            i = bit.bit_length() - 1
            values[mask] = masses[i] * values[mask ^ bit] - sum(
                factors[d] * values[mask ^ d] for d in supports
                if d & bit and d & mask == d)
        result.append(values[127])
    return result


def repaired_B(certificate):
    supports = [s for s in range(128) if s.bit_count() >= 2]
    check(certificate["primes"] == list(Q), "certificate prime axes")
    check(certificate["support_order"] in (
        supports, "increasing7-bit mask, with popcount at least2"),
        "certificate support addresses")
    originals = {c["name"]: c for c in certificate["candidates"]}
    check(set(originals) == {"A", "B"}, "certificate candidates")
    for name, candidate in originals.items():
        leaf = [F(0)] * 5
        for w, (_, t) in candidate["stars"][0]:
            leaf[t] += F(w)
        check(tuple(leaf) == CASES[name], "literal original q5 allocation")
    candidate = json.loads(json.dumps(originals["B"]))
    original_result = signed_responses(candidate, supports)
    check(original_result == list(map(F, candidate["expected_leaf_responses"])),
          "original B response freshly reconstructed")
    candidate["stars"][0] = [["21/125", [0, 0]], ["104/125", [0, 1]]]
    candidate["support_colors"][supports.index(37)] = [
        [5, "1570657/2041125"], [6, "470468/2041125"]]
    repaired_result = signed_responses(candidate, supports)
    check(repaired_result == original_result, "repaired B preserves signed response")
    check(F(4, 25) + F(1, 125) == F(21, 125), "full q5 tail in leaf0")
    check(F(4, 5) + F(4, 125) == F(104, 125), "q5 slots in leaf1")
    check(extract(5, (F(21, 125), F(104, 125), F(0), F(0), F(0)), 3)["word"]
          == [1, 0, 1], "repaired q5 prefix")
    return {
        "q5_leaf_allocation": ["21/125", "104/125", "0", "0", "0"],
        "q5_first_three_leaf_colours": [1, 0, 1],
        "q5_all_later_leaf_colour": 0,
        "mixed_support_37_colours": candidate["support_colors"][supports.index(37)],
        "signed_leaf_responses": list(map(str, repaired_result)),
        "scope": "Original B response persists with fully slotwise q5 allocation; "
                 "mixed supports 5,6,37 have slot realization not established by "
                 "these tests. No actual "
                 "family or all-fixed-weight obstruction is asserted.",
    }


def run(certificate):
    output = {
        "status": "ordinary-exact-rational-checks-no-Lean",
        "model": "slotwise cap completion, not true deletion mass",
        "witnesses": {},
    }
    for name, v in CASES.items():
        depths = (1,) if name == "A" else (1, 2, 3)
        row = {"q5_leaf_allocation": list(map(str, v)), "depths": {}}
        for depth in depths:
            member = extract(5, v, depth)
            distance = domain_distance(5, v, depth)
            check((F(distance["distance_l1"]) == 0) == member["member"],
                  "independent distance and digit tests agree")
            row["depths"][str(depth)] = dict(member, **distance)
        rejecting_depth = 1 if name == "A" else 3
        target_distance = row["depths"][str(rejecting_depth)]["distance_l1"]
        relabelings = 0
        # Every permutation is stronger than the needed within-root S2 x S3.
        for permutation in itertools.permutations(range(5)):
            changed = tuple(v[i] for i in permutation)
            check(not extract(5, changed, rejecting_depth)["member"],
                  "relabelled witness unexpectedly feasible")
            check(domain_distance(5, changed, rejecting_depth)["distance_l1"]
                  == target_distance, "distance must be permutation invariant")
            relabelings += 1
        row["all_leaf_relabelings_checked"] = relabelings
        output["witnesses"][name] = row
    check(output["witnesses"]["A"]["depths"]["1"]["distance_l1"]
          == "26813722/34082745", "A exact distance")
    check(output["witnesses"]["B"]["depths"]["3"]["distance_l1"]
          == "3141314/284022875", "B exact distance")
    mixed_root = (F(104825, 171999), F(67174, 171999))
    simplex(mixed_root)
    leading = F(4, 5) * F(6, 7) * F(10, 11)
    check(max(mixed_root) < leading, "A mixed root leading-atom obstruction")
    output["A_mixed_support_5_7_11"] = {
        "root_allocation": list(map(str, mixed_root)),
        "leading_weight": str(leading),
        "distance_l1_to_leading_corners": str(2 * (leading - max(mixed_root))),
    }
    output["finite_partial_inventories_checked"] = completion_controls()
    output["mixed_support_controls"] = mixed_controls()
    output["repaired_B_same_response"] = repaired_B(certificate)
    output["checks"] = CHECKS
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=Path(__file__).with_name(
        "clipped_common_source_obstruction_certificate.json"))
    parser.add_argument("--write-result")
    parser.add_argument("--expected", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    with args.certificate.open(encoding="utf-8") as handle:
        certificate = json.load(handle)
    result = run(certificate)
    if not args.write_result:
        with open(args.expected, encoding="utf-8") as handle:
            if json.load(handle) != result:
                raise ValueError("retained result differs from fresh exact computation")
    if args.write_result:
        with open(args.write_result, "w", encoding="utf-8") as handle:
            json.dump(result, handle, indent=2)
            handle.write("\n")
    print(json.dumps({"status": result["status"], "checks": result["checks"],
                      "A_rejects_at": 1, "B_rejects_at": 3}, sort_keys=True))


if __name__ == "__main__":
    main()
