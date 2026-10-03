#!/usr/bin/env python3
"""Exact finite original-family check for the raw depth-two cap certificate.

The listed phases, raw cap sums, signed polynomial, hinge and containment
repair are recomputed. No failure value is a survivor upper bound.
"""
import argparse
from fractions import Fraction as F
import heapq
from itertools import combinations
import json
from math import gcd, prod
from pathlib import Path

Q = (5, 7, 11, 13, 17, 19, 23)
SUPPORTS = tuple(s for s in range(128) if s.bit_count() >= 2)
PAIRS = tuple((s, t) for s, t in combinations(SUPPORTS, 2) if not s & t)
TRIPLES = tuple((s, t, u) for s, t, u in combinations(SUPPORTS, 3)
                if not (s & t or s & u or t & u))
LEAVES = (4, 7, 2, 5, 8)
WEIGHTS = (F(1, 3), F(1, 3), F(1, 9), F(1, 9), F(1, 9))
CUTOFF, PURE_HEIGHT = 1000000, 3
CHECKS = 0


def require(condition, reason):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ValueError(reason)


def smooth_numbers(bound):
    seen, queue, output = {1}, [1], []
    while queue:
        n = heapq.heappop(queue)
        if n > 1:
            output.append(n)
        for q in Q:
            nxt = n * q
            if nxt <= bound and nxt not in seen:
                seen.add(nxt)
                heapq.heappush(queue, nxt)
    return output


def exponents(n):
    remaining = n
    result = []
    for q in Q:
        e = 0
        while remaining % q == 0:
            remaining //= q
            e += 1
        result.append(e)
    require(remaining == 1, "numerical label has an undeclared prime")
    return tuple(result)


def mask_of(exps):
    return sum(1 << i for i, e in enumerate(exps) if e)


def allocation_roles(allocation, numbers):
    stars = {row["prime"]: row for row in allocation["star_completions"]}
    mixed = {row["support_mask"]: row for row in allocation["mixed_completions"]}
    require(set(stars) == set(Q) and set(mixed) == {5, 6, 37},
            "complete numerical-slot rule addresses")
    colours = dict(zip(SUPPORTS, allocation["candidate"]["support_colors"]))
    require(len(colours) == 120, "complete common support table")
    residual = {s: F(row["residual"]) for s, row in mixed.items()}
    selected = {s: set(row["selected_head_denominators"]) for s, row in mixed.items()}
    roles = {}
    for n in numbers:
        es = exponents(n)
        s = mask_of(es)
        if s.bit_count() == 1:
            i = s.bit_length() - 1
            row = stars[Q[i]]
            e = es[i]
            prefix = row["prefix_roles"]
            role = prefix[e - 1] if e <= len(prefix) else row["constant_tail_role"]
        elif s not in mixed:
            role = colours[s]
            require(isinstance(role, int), "unaccounted fractional common role")
        else:
            row = mixed[s]
            if n <= row["threshold"]:
                take_first = n in selected[s]
            else:
                atom = F(prod(q - 1 for i, q in enumerate(Q) if s >> i & 1), n)
                take_first = residual[s] >= atom
                if take_first:
                    residual[s] -= atom
            role = row["first_role"] if take_first else row["second_role"]
        require(isinstance(role, int) and 0 <= role < 10, "invalid numerical slot role")
        roles[n] = role
    return roles


def crt_phase(ternary_modulus, ternary_residue, n):
    # One common numerical phase: a=2 mod n and a=t mod 3 or9.
    a = 2 + n * (((ternary_residue - 2) * pow(n, -1, ternary_modulus))
                 % ternary_modulus)
    require(0 <= a < ternary_modulus * n, "noncanonical CRT phase")
    require(a % n == 2 and a % ternary_modulus == ternary_residue,
            "CRT did not retain both original projections")
    return a


def intended_family(allocation):
    numbers = smooth_numbers(CUTOFF)
    roles = allocation_roles(allocation, numbers)
    originals = {3: 0, 9: 1}
    for q in Q:
        for j in range(1, PURE_HEIGHT + 1):
            originals[q ** j] = q ** (j - 1)
    for n in numbers:
        s = mask_of(exponents(n))
        role = roles[n]
        root, leaf = divmod(role, 5)
        originals[3 * n] = crt_phase(3, root + 1, n)
        originals[9 * n] = crt_phase(9, LEAVES[leaf], n)
        if s.bit_count() >= 2:
            originals[n] = 2
    return numbers, originals


def make_certificate(allocation):
    _, originals = intended_family(allocation)
    return {
        "schema": "e7-raw-finite-slot-source-v1",
        "primes": list(Q), "nonternary_cutoff": CUTOFF,
        "pure_height": PURE_HEIGHT, "weights": list(map(str, WEIGHTS)),
        "ternary_leaves": list(LEAVES),
        "originals": [[m, originals[m]] for m in sorted(originals)],
        "scope": "One finite actual family, each full numerical modulus with one "
                 "fixed phase. Its raw individual-cylinder-cap certificate at the "
                 "specified weight fails the existing hinge threshold. A CRT "
                 "survivor is supplied; no survivor upper bound is claimed.",
    }


def hinge(caps, budgets):
    root_cap = max(sum(WEIGHTS[:2]), sum(WEIGHTS[2:]))
    leaf_cap = max(WEIGHTS)
    factors = []
    factors.append({k: 1 - root_cap if k == 1 else root_cap - leaf_cap if k == 2
                    else 2 * leaf_cap / 3 ** (k - 2) for k in range(1, 28)})
    for q, cap in zip(Q, caps):
        factors.append({k: 1 - cap / q if k == 1
                        else cap * F(q - 1, q ** k) for k in range(1, 28)})
    atoms = {1: F(1)}
    for factor in factors:
        nxt = {}
        for a, mass in atoms.items():
            for b, other in factor.items():
                if a * b < 28:
                    nxt[a * b] = nxt.get(a * b, F(0)) + mass * other
        atoms = nxt
    full_mean = (1 + root_cap + F(3, 2) * leaf_cap) * prod(1 + b for b in budgets)
    require(0 < full_mean < 28, "negative hinge thresholds cannot improve the zero threshold")
    rows = []
    for t in range(28):
        stop_loss = full_mean - t + sum((t - n) * mass for n, mass in atoms.items() if n < t)
        require(stop_loss > 0, "complete comparator tail must stay positive")
        rows.append({"threshold": t, "stop_loss": str(stop_loss),
                     "required_mass": str(stop_loss / (28 - t))})
    best = min(rows, key=lambda row: F(row["required_mass"]))
    return full_mean, rows, best


def retained_inventory_response(originals, caps):
    """Aggregate literal cylinder masses, then directly expand support packings."""
    star = [[F(0)] * 5 for _ in Q]
    mixed = {s: [F(0)] * 5 for s in SUPPORTS}
    for modulus, phase in originals:
        n, depth = modulus, 0
        while n % 3 == 0:
            n //= 3
            depth += 1
        if n == 1:
            continue
        es = exponents(n)
        s = mask_of(es)
        if depth == 0 and s.bit_count() == 1:
            continue
        mass = prod(caps[i] for i, e in enumerate(es) if e) / n
        for leaf, residue in enumerate(LEAVES):
            if residue % (3 ** depth) == phase % (3 ** depth):
                if s.bit_count() == 1:
                    star[s.bit_length() - 1][leaf] += mass
                else:
                    mixed[s][leaf] += mass
    masses = [[1 - v for v in row] for row in star]
    require(all(v > 0 for row in masses for v in row), "retained star source positivity")
    uncovered = {s: [prod(masses[i][l] for i in range(7) if not s >> i & 1)
                     for l in range(5)] for s in range(128)}
    response = uncovered[0].copy()
    for s in SUPPORTS:
        response = [v - uncovered[s][l] * mixed[s][l] for l, v in enumerate(response)]
    for s, t in PAIRS:
        response = [v + uncovered[s | t][l] * mixed[s][l] * mixed[t][l]
                    for l, v in enumerate(response)]
    for s, t, u in TRIPLES:
        response = [v - uncovered[s | t | u][l] * mixed[s][l] * mixed[t][l] * mixed[u][l]
                    for l, v in enumerate(response)]
    clipped = sum(w * max(F(0), v) for w, v in zip(WEIGHTS, response))
    return masses, response, clipped


def remove_contained(originals, caps, hinge_rows, required):
    retained, witnesses = [], {}
    for m, a in sorted(originals):
        divisor = next((n for n, b in retained if m % n == 0 and a % n == b), None)
        if divisor is None:
            retained.append((m, a))
        else:
            witnesses[m] = divisor
    retained_phases = dict(retained)
    original_phases = dict(originals)
    require(set(retained_phases) | set(witnesses) == set(original_phases)
            and not set(retained_phases) & set(witnesses), "complete containment partition")
    for m, n in witnesses.items():
        require(n in retained_phases and m % n == 0
                and original_phases[m] % n == retained_phases[n],
                "removed class lacks a retained original containing it")
    require(all((q ** j, q ** (j - 1)) in retained for q in Q
                for j in range(1, PURE_HEIGHT + 1))
            and (3, 0) in retained and (9, 1) in retained, "same pure source after containment pruning")
    masses, response, clipped = retained_inventory_response(retained, caps)
    require(len(retained) == 51 and len(witnesses) == 2899, "literal containment reduction count")
    require(clipped > required, "containment pruning did not restore this certificate")
    query_bounds = [(row["threshold"] + F(row["stop_loss"]) / clipped,
                     row["threshold"]) for row in hinge_rows]
    bound, threshold = min(query_bounds)
    require(bound < 28, "retained source query bound misses29 continuation gate")
    return {
        "original_count": len(retained), "removed_count": len(witnesses),
        "originals": [list(row) for row in retained],
        "containment_witnesses": {str(m): n for m, n in witnesses.items()},
        "star_masses": [list(map(str, row)) for row in masses],
        "signed_leaf_response": list(map(str, response)),
        "clipped_raw_certificate": str(clipped), "clipped_raw_decimal": float(clipped),
        "margin_over_required_mass": str(clipped - required),
        "best_query_threshold": threshold, "query_upper_bound": str(bound),
        "query_upper_decimal": float(bound),
        "scope": "Every removed congruence is contained in a retained original, so the "
                 "covered union is exactly unchanged. The reconstructed source can change; "
                 "its pure caps, leaf weights and hinge comparison stay the same. This "
                 "repairs this example only, not every irredundant family.",
    }


def calculate(certificate, allocation):
    require(certificate["schema"] == "e7-raw-finite-slot-source-v1", "certificate schema")
    require(certificate["primes"] == list(Q), "actual prime axes")
    require(certificate["nonternary_cutoff"] == CUTOFF and certificate["pure_height"] == PURE_HEIGHT,
            "actual source cutoff and pure height")
    require(certificate["weights"] == list(map(str, WEIGHTS))
            and certificate["ternary_leaves"] == list(LEAVES), "fixed weight and leaf interface")
    numbers, intended = intended_family(allocation)
    rows = certificate["originals"]
    require(all(isinstance(row, list) and len(row) == 2 and all(type(v) is int for v in row)
                for row in rows), "original row type")
    require(len({m for m, _ in rows}) == len(rows), "duplicate original numerical modulus")
    actual = dict(rows)
    require(actual == intended, "actual full-phase inventory differs from the declared slot prefix")
    require(all(m > 1 and m % 2 == 1 and 0 <= a < m for m, a in rows),
            "odd distinct original label domain")
    pure_mass, caps = [], []
    for q in Q:
        local = [(q ** j, actual[q ** j]) for j in range(1, PURE_HEIGHT + 1)]
        for (m, a), (n, b) in combinations(local, 2):
            require((a - b) % gcd(m, n) != 0, "pure exclusions must be disjoint")
        z = 1 - sum(F(1, m) for m, _ in local)
        require(z == F(q - 2, q - 1) + F(1, (q - 1) * q ** PURE_HEIGHT),
                "actual pure-survivor normalization")
        pure_mass.append(z)
        caps.append(1 / z)
    budgets = [cap / (q - 1) for q, cap in zip(Q, caps)]
    x = {s: [F(0), F(0)] for s in range(1, 128)}
    y = {s: [F(0)] * 5 for s in range(1, 128)}
    z = {s: F(0) for s in SUPPORTS}
    exponent_max = [0] * 7
    counts = {"ternary_pure": 0, "nonternary_pure": 0,
              "root": 0, "leaf": 0, "mixed_no3": 0}
    for modulus, phase in rows:
        if modulus in (3, 9):
            counts["ternary_pure"] += 1
            continue
        n, ternary_depth = modulus, 0
        while n % 3 == 0:
            n //= 3
            ternary_depth += 1
        es = exponents(n)
        s = mask_of(es)
        exponent_max = [max(a, b) for a, b in zip(exponent_max, es)]
        if ternary_depth == 0 and s.bit_count() == 1:
            counts["nonternary_pure"] += 1
            continue
        require(phase % n == 2, "one fixed nonternary original phase")
        for i, e in enumerate(es):
            if e:
                for j in range(1, PURE_HEIGHT + 1):
                    require((2 - Q[i] ** (j - 1)) % (Q[i] ** min(e, j)) != 0,
                            "phase2 cylinder meets a pure exclusion")
        normalized_cap = F(prod(q - 1 for i, q in enumerate(Q) if s >> i & 1), n)
        if ternary_depth == 0:
            require(s in z, "unexpected unconditioned singleton event")
            z[s] += normalized_cap
            counts["mixed_no3"] += 1
        elif ternary_depth == 1:
            root = phase % 3 - 1
            require(root in (0, 1), "actual root misses the live source")
            x[s][root] += normalized_cap
            counts["root"] += 1
        elif ternary_depth == 2:
            require(phase % 9 in LEAVES, "actual leaf misses the live source")
            y[s][LEAVES.index(phase % 9)] += normalized_cap
            counts["leaf"] += 1
        else:
            raise ValueError("old original ternary depth exceeds two")
    for s in range(1, 128):
        require(sum(x[s]) == sum(y[s]) < 1, "raw prefix inventories must remain unpadded")
        if s in z:
            require(z[s] == sum(x[s]), "same numerical prefix in all three mixed inventories")
    masses = [[1 - budgets[i] * (x[1 << i][int(l >= 2)] + y[1 << i][l])
               for l in range(5)] for i in range(7)]
    require(all(0 < masses[i][l] <= 1 for i in range(7) for l in range(5)),
            "raw source thinning masses")
    colour = {s: [z[s] + x[s][int(l >= 2)] + y[s][l] for l in range(5)]
              for s in SUPPORTS}
    require(all(0 <= c <= 3 for row in colour.values() for c in row),
            "raw mixed activity domain")
    coefficient = {s: [prod(budgets[i] if s >> i & 1 else masses[i][l]
                           for i in range(7)) for l in range(5)] for s in range(128)}
    response = coefficient[0].copy()
    for s in SUPPORTS:
        response = [v - coefficient[s][l] * colour[s][l] for l, v in enumerate(response)]
    for s, t in PAIRS:
        response = [v + coefficient[s | t][l] * colour[s][l] * colour[t][l]
                    for l, v in enumerate(response)]
    for s, t, u in TRIPLES:
        response = [v - coefficient[s | t | u][l] * colour[s][l] * colour[t][l] * colour[u][l]
                    for l, v in enumerate(response)]
    require((len(SUPPORTS), len(PAIRS), len(TRIPLES)) == (120, 546, 210),
            "complete disjoint-support polynomial inventory")
    require(all(v > 0 for v in response), "all five raw signed responses remain positive")
    clipped = sum(w * max(F(0), v) for w, v in zip(WEIGHTS, response))
    mean, hinge_rows, best = hinge(caps, budgets)
    required = F(best["required_mass"])
    gap = required - clipped
    require(gap > F(1, 100), "raw finite certificate gap did not exceed one hundredth")
    pruned = remove_contained(rows, caps, hinge_rows, required)
    nonternary_lcm = prod(q ** e for q, e in zip(Q, exponent_max))
    survivor = nonternary_lcm * ((4 * pow(nonternary_lcm, -1, 9)) % 9)
    require(survivor % 9 == 4 and survivor % nonternary_lcm == 0, "CRT survivor projections")
    for m, a in rows:
        require(survivor % m != a, "claimed survivor hits an actual original")
    require(len(rows) == 2950 and len(numbers) == 988, "complete finite family cardinality")
    return {
        "schema": "e7-raw-finite-slot-source-result-v1",
        "status": "ordinary-exact-finite-certificate-and-repair-no-Lean",
        "original_count": len(rows), "inventory_counts": counts,
        "nonternary_slot_count": len(numbers), "nonternary_exponent_max": exponent_max,
        "pure_survivor_masses": list(map(str, pure_mass)),
        "actual_tight_caps": list(map(str, caps)), "actual_cap_budgets": list(map(str, budgets)),
        "raw_root_caps": {str(s): list(map(str, row)) for s, row in x.items()},
        "raw_leaf_caps": {str(s): list(map(str, row)) for s, row in y.items()},
        "raw_no3_caps": {str(s): str(v) for s, v in z.items()},
        "star_masses": [list(map(str, row)) for row in masses],
        "signed_leaf_response": list(map(str, response)),
        "signed_leaf_decimal": list(map(float, response)),
        "clipped_raw_certificate": str(clipped), "clipped_raw_decimal": float(clipped),
        "complete_comparator_mean": str(mean), "hinge_ratios": hinge_rows,
        "best_hinge_threshold": best["threshold"], "required_mass": str(required),
        "required_mass_decimal": float(required), "gap": str(gap), "gap_decimal": float(gap),
        "nonternary_lcm": str(nonternary_lcm), "explicit_survivor": str(survivor),
        "pruned": pruned,
        "checks": CHECKS,
        "scope": "All listed original phases and raw individual-cylinder caps are retained. "
                 "No unused-budget padding is performed. The fixed weight and this raw "
                 "polynomial plus existing full-query hinge fail before removing "
                 "contained classes and succeed afterwards. The explicit survivor "
                 "prevents reading this as a covering example or survivor upper bound. "
                 "Overlap-aware, reweighted or alternative-source methods are not excluded.",
    }


def write_json(path, value):
    with Path(path).open("w", encoding="utf-8") as handle:
        json.dump(value, handle, indent=2)
        handle.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__)
    parser.add_argument("--allocation-certificate", type=Path,
                        default=here.with_name("mixed_numeric_slot_completion_certificate.json"))
    parser.add_argument("--certificate", type=Path,
                        default=here.with_name("raw_finite_slot_source_certificate.json"))
    parser.add_argument("--expected", type=Path, default=here.with_suffix(".json"))
    parser.add_argument("--write-certificate", type=Path)
    parser.add_argument("--write-result", type=Path)
    args = parser.parse_args()
    allocation = json.loads(args.allocation_certificate.read_text())
    if args.write_certificate:
        certificate = make_certificate(allocation)
        write_json(args.write_certificate, certificate)
    else:
        certificate = json.loads(args.certificate.read_text())
    # Keep replay counts independent of whether the input was just generated.
    global CHECKS
    CHECKS = 0
    result = calculate(certificate, allocation)
    if args.write_result:
        write_json(args.write_result, result)
    else:
        require(result == json.loads(args.expected.read_text()),
                "retained raw source result differs from actual finite replay")
    print(json.dumps({"status": result["status"], "originals": result["original_count"],
                      "checks": result["checks"], "raw": result["clipped_raw_decimal"],
                      "threshold": result["required_mass_decimal"], "gap": result["gap_decimal"],
                      "retained_originals": result["pruned"]["original_count"],
                      "retained_certificate": result["pruned"]["clipped_raw_decimal"],
                      "retained_query_upper": result["pruned"]["query_upper_decimal"]},
                     sort_keys=True))


if __name__ == "__main__":
    main()
