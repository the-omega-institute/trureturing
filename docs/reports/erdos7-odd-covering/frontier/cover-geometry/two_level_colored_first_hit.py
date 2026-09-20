#!/usr/bin/env python3
"""Exact finite counterexample and sharp cap-aware first-hit LP certificate.

No optimization package is used: a feasible source and a pointwise dual
prove the optimum. All classes retain their original numerical moduli.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
import json
import time


MODEL = {
    "original_modulus_residue_pairs": [[3, 0], [5, 0], [7, 0], [33, 22],
                                        [99, 11], [55, 1], [847, 484]],
    "old_period": 315,
    "current_prime": 11,
    "current_height": 2,
    "threshold": "1/11",
    "old7_conditional_atom_cap": "6/35",
    "perturbation": "1/35",
    "lp": "144 actual old survivor atoms; all pair-coordinate marginals "
          "equal pure-survivor product marginals; atom upper cap 1/140",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def enc(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): enc(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [enc(v) for v in value]
    return value


def digest(value):
    return sha256((json.dumps(value, sort_keys=True, separators=(",", ":"))
                   + "\n").encode()).hexdigest()


def main():
    parser = ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started = time.perf_counter()
    old_period = MODEL["old_period"]
    q = MODEL["current_prime"]
    current_period = q ** MODEL["current_height"]
    delta, u, epsilon = F(MODEL["threshold"]), F("6/35"), F("1/35")
    labels = [tuple(row) for row in MODEL["original_modulus_residue_pairs"]]
    require(len({d for d, _ in labels}) == len(labels), "Distinct numerical moduli")
    require(all(d > 1 and d % 2 and 0 <= a < d for d, a in labels),
            "Odd nonunit original labels with canonical residues")
    period = lcm(*(d for d, _ in labels))
    require(period == old_period * current_period, "Original exact full period")
    comparable_pairs = 0
    for (d, a), (e, b) in combinations(labels, 2):
        if d % e == 0 or e % d == 0:
            comparable_pairs += 1
            require((a-b) % gcd(d, e) != 0,
                    "Comparable original classes are disjoint: literal reduction")

    states = [x for x in range(old_period) if all(x % p for p in (3, 5, 7))]
    require(len(states) == 144, "Complete old survivor carrier")
    tuples = {x: (x % 9, x % 5, x % 7) for x in states}
    old_sets = {9: sorted({t[0] for t in tuples.values()}),
                5: list(range(1, 5)), 7: list(range(1, 7))}
    require(len(old_sets[9]) == 6, "Six actual ternary depth-two survivors")
    base = {x: F(1, 144) for x in states}

    def h3(x):
        return 1 if x % 3 == 1 else -1

    def h(x, p):
        return 1 if x % p == 1 else -1 if x % p == 2 else 0

    laws = {name: {x: base[x]*(1+sign*epsilon*h3(x)*h(x, 5)*h(x, 7))
                   for x in states}
            for name, sign in (("plus", 1), ("minus", -1))}
    laws["product"] = base

    def indicators(x):
        i1, i4 = int(x % 3 == 1), int(x % 9 == 2)
        return i1, i4, int(x % 5 == 1), int(x % 7 == 1)

    def pair_marginal(law, i, j):
        answer = {}
        for x in states:
            key = (tuples[x][i], tuples[x][j])
            answer[key] = answer.get(key, F(0)) + law[x]
        return answer

    pair_checks = 0
    for law in laws.values():
        require(sum(law.values()) == 1 and min(law.values()) > 0,
                "Positive normalized actual source")
        for i, j in combinations(range(3), 2):
            require(pair_marginal(law, i, j) == pair_marginal(base, i, j),
                    "Every full two-coordinate marginal is unchanged")
            pair_checks += len(pair_marginal(base, i, j))
        for x in states:
            require(law[x] <= F(1, 140), "Exact atom cap / conditional seven cap")
            require(24 * law[x] <= u, "Full-history seven conditional cap")
        for depth in (1, 2):
            for residue in range(3**depth):
                mass = sum(law[x] for x in states if x % (3**depth) == residue)
                require(mass <= F(2, 3**depth), "Every full-height ternary prefix cap")
        for old3 in old_sets[9]:
            for old5 in old_sets[5]:
                mass = sum(law[x] for x in states
                           if tuples[x][:2] == (old3, old5))
                require(mass/F(1,6) == F(1,4) <= F(4,15),
                        "Five cap conditional on the complete ternary coordinate")

    # Raw original-old indicators, including the identically zero earlier
    # pure forbidden classes on the source. All unary and pair moments agree.
    old_labels = [(d // (q ** (2 if d % q**2 == 0 else 1)), a)
                  for d, a in labels[3:]]
    def old_events(x):
        return tuple(int(x % p == 0) for p in (3, 5, 7)) + tuple(
            int(x % d == a % d) for d, a in old_labels)
    moment_rows = {}
    for name, law in laws.items():
        moments = []
        for i in range(len(labels)):
            moments.append(sum(law[x]*old_events(x)[i] for x in states))
            for j in range(i+1, len(labels)):
                moments.append(sum(law[x]*old_events(x)[i]*old_events(x)[j]
                                   for x in states))
        moment_rows[name] = moments
    require(moment_rows["plus"] == moment_rows["minus"] == moment_rows["product"],
            "All original-old-label unary and pair moments identical")
    require(all(indicators(x)[0]*indicators(x)[1] == 0 for x in states),
            "Nonvacuous fixed-color comparable-cofactor pair zero")

    inv = pow(old_period, -1, current_period)
    costs, additive_costs, triple, current_moments = {}, {}, {}, {}
    full_AP_patterns = {name: {mask: F(0) for mask in range(1 << len(labels))}
                        for name in laws}
    row_cost = {}
    for x in states:
        i1, i4, b, c = indicators(x)
        a = i1+i4
        covered = []
        event_vectors = []
        for y in range(current_period):
            integer = x + old_period * (((y-x)*inv) % current_period)
            events = tuple(int(integer % d == residue) for d, residue in labels)
            event_vectors.append(events)
            covered.append(any(events))
        alpha = F(sum(covered), current_period)
        require(alpha == F(a+b, q)+F((1-a)*c, q*q),
                "Literal original AP union equals the two-level colored formula")
        beta = max(F(0), alpha-delta)/(1-delta)
        require(beta == F(a*b, q-1)+F((1-a)*b*c, q*(q-1)),
                "Exact hinge / first-hit cost identity")
        row_cost[x] = beta
        kernel = []
        for is_bad in covered:
            if alpha <= delta:
                density = F(0) if is_bad else 1/(1-alpha)
            else:
                density = (alpha-delta)/(alpha*(1-delta)) if is_bad else 1/(1-delta)
            kernel.append(density/current_period)
        require(sum(kernel) == 1 and min(kernel) >= 0,
                "Normalized actual clipped current kernel")
        require(max(kernel) <= 1/((1-delta)*current_period), "Full current atom cap")
        require(sum(k for k, is_bad in zip(kernel, covered) if is_bad) == beta,
                "Actual ending event probability equals first-hit cost")
        scalar_alpha = F(a+b, q)+F(c, q*q)
        scalar_beta = max(F(0), scalar_alpha-delta)/(1-delta)
        require(scalar_beta-beta == F(a*c, q*(q-1)),
                "Pointwise charge saved by actual cross-depth containment")
        pattern_counts = Counter(sum(value << i for i, value in enumerate(row))
                                 for row in event_vectors)
        for name, law in laws.items():
            costs[name] = costs.get(name, F(0)) + law[x]*beta
            additive_costs[name] = additive_costs.get(name, F(0)) + law[x]*scalar_beta
            triple[name] = triple.get(name, F(0)) + law[x]*a*b*c
            for mask, count in pattern_counts.items():
                full_AP_patterns[name][mask] += law[x]*F(count, current_period)
            moments = current_moments.setdefault(name, [F(0)]*28)
            k = 0
            for i in range(len(labels)):
                moments[k] += law[x]*F(sum(row[i] for row in event_vectors), current_period)
                k += 1
                for j in range(i+1, len(labels)):
                    moments[k] += law[x]*F(sum(row[i]*row[j] for row in event_vectors), current_period)
                    k += 1
    require(current_moments["plus"] == current_moments["minus"] == current_moments["product"],
            "All full original AP unary/pair moments under source x current Haar identical")
    require(full_AP_patterns["plus"] == full_AP_patterns["minus"] == full_AP_patterns["product"],
            "The entire 128-pattern original-AP joint law is identical")
    nonzero_patterns = {mask: mass for mask, mass in full_AP_patterns["plus"].items()
                        if mass}
    require(set(nonzero_patterns) == {0,8,16,32,64,72,80},
            "Exactly seven patterns: empty, four singletons and two doubletons")
    require(all(bin(mask).count('1') <= 2 for mask in nonzero_patterns),
            "Every original AP intersection of order at least three is empty")

    # The primal LP has all actual coordinates, not abstract event patterns.
    # Four equality prices 1/10 use the fixed (old3,old5) row mass 1/24.
    # Two cap prices 1/110 use the genuine full-history bound atom <=1/140.
    # This coefficient identity checks EVERY one of its 144 columns.
    dual_constant = F(0)
    priced_rows, priced_caps = set(), []
    dual_slacks = []
    for x in states:
        i1, i4, b, c = indicators(x)
        a = i1+i4
        row_price = F(a*b, q-1)
        cap_price = F((1-a)*b*c, q*(q-1))
        if row_price:
            priced_rows.add(tuples[x][:2])
        if cap_price:
            priced_caps.append(x)
        dual_slacks.append(row_price+cap_price-row_cost[x])
    require(set(dual_slacks) == {F(0)}, "Every dual column is exact")
    dual_constant = len(priced_rows)*F(1,24)*F(1,q-1) + len(priced_caps)*F(1,140)*F(1,q*(q-1))
    require(len(priced_rows) == 4 and len(priced_caps) == 2, "Six sparse nonzero dual prices")
    require(all(laws["minus"][x] == F(1,140) for x in priced_caps), "Primal cap saturation")
    require(costs["minus"] == dual_constant == F(97,5775), "Exact attained capped LP optimum")
    require(costs["minus"]-costs["plus"] == F(1,138600), "Nonidentifiability gap")
    require(all(additive_costs[k]-costs[k] == F(1,990) for k in laws), "Joint union saving")

    # Pair-marginal-only control, with the conditional atom cap removed.
    # This is an actual CRT law, but it violates the seven cap. Its value
    # certifies sharpness of the weaker comparator, not admissibility above.
    uncapped = {}
    for x in states:
        i1, i4, b, c = indicators(x)
        a = i1+i4
        c_atom = F(0) if a and b else F(1,48) if b else F(1,108) if a else F(1,432)
        uncapped[x] = c_atom if c else (F(1,24)-c_atom)/5
    require(sum(uncapped.values()) == 1 and min(uncapped.values()) >= 0, "Uncapped feasible law")
    for i,j in combinations(range(3),2):
        require(pair_marginal(uncapped,i,j) == pair_marginal(base,i,j), "Uncapped identical pair marginals")
    uncapped_cost = sum(uncapped[x]*row_cost[x] for x in states)
    require(uncapped_cost == F(3,176), "Exact weaker pair-only LP optimum")
    require(max(uncapped.values()) > F(1,140), "Uncapped witness is explicitly inadmissible to capped LP")

    output = {
        "model": MODEL, "model_sha256": digest(MODEL),
        "producer_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "full_period": period, "old_survivor_atoms": len(states),
        "literal_current_fibres_checked": len(states),
        "literal_current_points_checked": len(states)*current_period,
        "comparable_original_pairs_checked_disjoint": comparable_pairs,
        "full_pair_marginal_cells_checked": pair_checks,
        "identical_old_unary_and_pair_moments": len(moment_rows["plus"]),
        "identical_full_AP_unary_and_pair_moments": len(current_moments["plus"]),
        "identical_full_AP_joint_pattern_count": len(full_AP_patterns["plus"]),
        "full_AP_joint_nonzero_pattern_probabilities": nonzero_patterns,
        "triple_ABC": triple, "first_hit_costs": costs,
        "literal_additive_row_costs": additive_costs,
        "first_hit_nonidentifiability_gap": costs["minus"]-costs["plus"],
        "two_layer_union_saving": F(1,990),
        "sharp_capped_LP_optimum": dual_constant,
        "sharp_uncapped_pair_LP_optimum": uncapped_cost,
        "strict_cap_gain": uncapped_cost-dual_constant,
        "dual_equality_rows": [list(row) for row in sorted(priced_rows)],
        "dual_equality_price": F(1,10),
        "dual_cap_atoms_old_CRT_residue": sorted(priced_caps),
        "dual_cap_price": F(1,110),
        "dual_columns_checked": len(dual_slacks),
        "scope": "Ordinary finite exact certificate; no Lean, no unrestricted "
                 "head bound, no claim that incoming kernels equal an earlier "
                 "prescribed BBMST policy. The plus, minus and product laws "
                 "are realized by normalized full-history kernels satisfying "
                 "the stated caps; the uncapped comparator explicitly violates "
                 "the seven cap.",
    }
    args.output.write_text(json.dumps(enc(output), sort_keys=True, indent=2)+"\n")
    print(json.dumps({"status":"PASS", "elapsed_seconds":time.perf_counter()-started,
                      "output_sha256":sha256(args.output.read_bytes()).hexdigest(),
                      "sharp_capped_LP_optimum":str(dual_constant)}))


if __name__ == "__main__":
    main()
