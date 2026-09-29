#!/usr/bin/env python3
"""An actual original-modulus counterexample to two-step uniform optimality.

All checks use explicit exceptions and survive -O. Finite verification only;
no source geometry, library theorem, or Lean certification is recomputed.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
import json
from math import gcd, prod
from pathlib import Path


def need(ok, why):
    if not ok:
        raise ValueError(why)


def crt(pairs):
    value, period = 0, 1
    for residue, modulus in pairs:
        need(gcd(period, modulus) == 1, "coprime CRT coordinates")
        value += period * (((residue - value) * pow(period, -1, modulus)) % modulus)
        period *= modulus
        value %= period
    return value, period


def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    K, q, r = 945, 23, 29
    Cq, Cr = Q(11, 5), Q(7, 3)
    old_primes = (3, 5, 7)
    divisors = [d for d in range(1, K + 1) if K % d == 0]
    need(len(divisors) == 16, "sixteen distinct original old cofactors")
    labels = [{"kind": "old", "modulus": p, "residue": 0} for p in old_primes]
    labels += [{"kind": "pure_q", "modulus": q, "residue": 0},
               {"kind": "pure_r", "modulus": r, "residue": 0}]
    axis_a, axis_m = crt([(1, 3), (2, q)])
    labels.append({"kind": "q_axis", "modulus": axis_m, "residue": axis_a})
    for j, d in enumerate(divisors, 1):
        a, m = crt([(1, d), (1, q), (j, r)])
        need(m == d * q * r, "original mixed numerical modulus")
        labels.append({"kind": "cross", "modulus": m, "residue": a,
                       "old_cofactor": d, "q_phase": 1, "r_phase": j})
    need(len(labels) == len({row["modulus"] for row in labels}) == 22,
         "distinct original numerical labels")
    need(all(row["modulus"] > 1 and row["modulus"] % 2 for row in labels),
         "odd nontrivial original moduli")
    old_support = [h for h in range(K) if all(h % p for p in old_primes)]
    need(len(old_support) == 432, "same full old survivor support")
    old_mass = Q(1, len(old_support))
    old_cap = Q(K, len(old_support))
    R = sum((max(Q(sum(h % d == a for h in old_support), len(old_support))
                 for a in range(d)) for d in divisors if d > 1), Q(0))
    need(old_cap == Q(35, 16) and R == Q(653, 432), "actual old-law scalar bounds")
    need(old_cap < 840 and R < Q(70871, 3375), "strong common-law scalar budgets")

    q_labels = [row for row in labels if row["modulus"] % q == 0
                and row["modulus"] % r != 0]
    r_labels = [row for row in labels if row["modulus"] % r == 0]
    baseline_total = Q(0)
    future_total = Q(0)
    mixture_total = Q(0)
    histogram = Counter()
    exceptional = []
    literal_point_checks = 0
    actual_survivor_count = 0
    private_points = {}
    for h in old_support:
        good_q = []
        later = {}
        for u in range(q):
            hu, _ = crt([(h, K), (u, q)])
            if any(hu % row["modulus"] == row["residue"] for row in q_labels):
                continue
            good_q.append(u)
            good_r = []
            bad_r = []
            for v in range(r):
                point, period = crt([(h, K), (u, q), (v, r)])
                need(period == K * q * r, "same full CRT carrier")
                hits = [i for i, row in enumerate(labels)
                        if point % row["modulus"] == row["residue"]]
                literal_point_checks += 1
                if len(hits) == 1:
                    private_points.setdefault(hits[0], point)
                if not hits:
                    good_r.append(v)
                elif v != 0:
                    bad_r.append(v)
            g = Q(len(good_r), r)
            survival = min(Q(1), Cr * g)
            # Explicit source current-loss optimizer at29. The kernel is
            # identical under both strategies; only the23 kernel differs.
            r_prob = [Q(0)] * r
            for v in good_r:
                r_prob[v] = survival / len(good_r)
            if survival < 1:
                need(bool(bad_r), "a feasible spill set at29")
                for v in bad_r:
                    r_prob[v] = (1 - survival) / len(bad_r)
            need(sum(r_prob) == 1 and r_prob[0] == 0
                 and all(0 <= r * mass <= Cr for mass in r_prob),
                 "same normalized capped29 kernel")
            need(sum(r_prob[v] for v in good_r) == survival,
                 "actual29 surviving mass")
            need(all(r_prob[v] > 0 for v in good_r),
                 "same29 kernel is positive on every original good point")
            actual_survivor_count += len(good_r)
            later[u] = survival
        need(len(good_q) == (21 if h % 3 == 1 else 22), "literal23 survivor set")
        safe_q = [u for u in good_q if later[u] == 1]
        need(safe_q and Q(q, len(good_q)) <= Cq and Q(q, len(safe_q)) <= Cq,
             "both normalized23 kernels satisfy cap11/5")
        baseline = sum(later.values(), Q(0)) / len(good_q)
        future = sum((later[u] for u in safe_q), Q(0)) / len(safe_q)
        baseline_q = [Q(1, len(good_q)) if u in good_q else Q(0)
                      for u in range(q)]
        future_q = [Q(1, len(safe_q)) if u in safe_q else Q(0)
                    for u in range(q)]
        mixture_q = [(a + b) / 2 for a, b in zip(baseline_q, future_q)]
        need(sum(mixture_q) == 1
             and all(0 <= q * mass <= Cq for mass in mixture_q)
             and all(mixture_q[u] > 0 for u in good_q)
             and all(mixture_q[u] == 0 for u in range(q) if u not in good_q),
             "half-mixture has the same cap, zero current loss and full good support")
        mixture = sum((mixture_q[u] * later[u] for u in good_q), Q(0))
        need(future == 1 and baseline <= future, "both current23 losses zero; future survives")
        baseline_total += old_mass * baseline
        future_total += old_mass * future
        mixture_total += old_mass * mixture
        histogram[(len(good_q), len(safe_q), str(baseline))] += 1
        if baseline < future:
            exceptional.append({"old_residue": h, "old_probability": old_mass,
                                "q_good": good_q, "q_safe": safe_q,
                                "later_survival": later, "baseline": baseline,
                                "future": future,
                                "source23_density": Q(q, len(good_q)),
                                "future23_density": Q(q, len(safe_q))})
    gain = future_total - baseline_total
    need(len(exceptional) == 1 and exceptional[0]["old_residue"] == 1,
         "one positive-mass old history has nonconstant future score")
    need(exceptional[0]["later_survival"][1] == Q(28, 29)
         and exceptional[0]["baseline"] == Q(608, 609), "actual cross-phase congestion")
    need(baseline_total == Q(263087, 263088) and future_total == 1
         and gain == Q(1, 263088), "strict two-step improvement at unchanged caps")
    need(mixture_total == Q(526175, 526176)
         and mixture_total - baseline_total == Q(1, 526176),
         "strict gain while retaining every actual original survivor")
    # Verify every cross and current-axis class has an actual private point.
    # For old and pure-q labels choose q=3, which avoids every mixed label.
    for i, row in enumerate(labels):
        if i not in private_points:
            old = 1
            if row["kind"] == "old":
                old, _ = crt([(0 if p == row["modulus"] else 1, p)
                              for p in old_primes])
            u = 0 if row["kind"] == "pure_q" else 2 if row["kind"] == "q_axis" else 3
            point, _ = crt([(old, K), (u, q), (0 if row["kind"] == "pure_r" else 28, r)])
            need([j for j, label in enumerate(labels)
                  if point % label["modulus"] == label["residue"]] == [i],
                 "each original label has a literal private point")
            private_points[i] = point
    for i, row in enumerate(labels):
        row["private_point"] = private_points[i]
    avoiding, _ = crt([(1, K), (3, q), (28, r)])
    need(all(avoiding % row["modulus"] != row["residue"] for row in labels),
         "actual family is noncovering")

    # Seven actual old primes: independent pure-survivor padding. The two
    # strategies remain on exactly the same law and retain exactly the gain.
    padding = (11, 13, 17, 19)
    padding_factor = prod(Q(p, p - 1) for p in padding)
    padded_cap = old_cap * padding_factor
    padded_R = (1 + R) * padding_factor - 1
    need(padded_cap < 840 and padded_R < Q(70871, 3375), "seven-prime common-law budgets")
    result = {
        "scope": "Actual finite original-modulus counterexample to the claim that the source's uniform-on-G current-loss optimizer maximizes two-step survival. It does not refute the source kernel lemma or prove a uniform gain for every original family or for its selected seven-core law.",
        "old_period": K, "full_period": K * q * r,
        "original_labels": labels,
        "old_law": {"definition": "uniform on the actual old survivors (nonzero modulo3,5,7)",
                    "support_size": len(old_support), "point_mass": old_mass,
                    "haar_density_cap": old_cap, "nonunit_query_sum": R},
        "caps": {"23": Cq, "29": Cr},
        "thresholds": {"23": 12, "29": 16},
        "literal_joint_point_checks": literal_point_checks,
        "actual_survivor_count": actual_survivor_count,
        "old_history_histogram": [{"q_good_count": k[0], "q_safe_count": k[1],
                                   "conditional_baseline_survival": k[2], "histories": v}
                                  for k, v in sorted(histogram.items())],
        "exceptional_histories": exceptional,
        "both_current23_losses": 0,
        "baseline_final_mass": baseline_total,
        "future_aware_final_mass": future_total,
        "strict_gain": gain,
        "half_mixture_full_support_strategy": {
            "final_mass": mixture_total,
            "strict_gain": mixture_total - baseline_total,
            "scope": "Average the two normalized23 kernels before the same29 kernel; positive on every actual original survivor, with unchanged caps."},
        "uncovered_integer": avoiding,
        "seven_actual_old_prime_padding": {
            "additional_original_classes": [{"modulus": p, "residue": 0} for p in padding],
            "old_law": "the same945 law times independent uniform nonzero added coordinates",
            "old_period": K * prod(padding),
            "original_class_count": len(labels) + len(padding),
            "haar_density_cap": padded_cap, "nonunit_query_sum": padded_R,
            "strict_gain": gain,
            "scope": "A separate actual seven-old-prime family, not identification with report466's particular construction."},
        "gain_input": "The joint old-history and23-prefix distribution of actual29 capped survivor fractions; separate stage moments do not determine it.",
        "general_quantile_result": "Existing weighted upper-quantile lemma; no new general theorem or Lean declaration is asserted."}
    output = json.dumps(encode(result), indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
        print("PASS: literal original phases, same old law, fixed caps, normalized kernels, all private labels, and strict two-step gain.")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
