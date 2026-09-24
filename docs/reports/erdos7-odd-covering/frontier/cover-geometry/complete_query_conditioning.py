#!/usr/bin/env python3
"""Exact complete-query comparator and three additional old pair towers.

Python 3 standard library only. The all-height actual-loss input is the
ordinary theorem JQ11 in report556; this program does not reprove that
theorem or run its optimizer. No original-period enumeration is used.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import prod
from pathlib import Path


def calculate():
    checks = {}

    def require(name, condition):
        if name in checks:
            raise ValueError("duplicate check: " + name)
        checks[name] = bool(condition)
        if not condition:
            raise ValueError(name)

    primes = (3, 5, 7, 11, 13, 17, 19)
    caps = {p: F(p - 1, p - 2) for p in primes}
    pure_mass = prod(1 / a for a in caps.values())
    mean = prod(1 + caps[p] / (p - 1) for p in primes)
    target = F(565, 51)
    fresh_factor = F(23, 22) * F(29, 28) - 1
    require("complete_mean", mean == F(4096, 935))
    require("pure_mass", pure_mass == F(935, 4096))
    require("fresh_factor", fresh_factor == F(51, 616))

    # Multiplicative convolution retains EXACT low-product probabilities.
    # Terms above the cutoff cannot return to it because every N_p >= 1.
    # Their first moment remains in 'mean', so no upper tail is discarded.
    limit = 10
    pmf = {1: F(1)}
    stage_counts = []
    for p in primes:
        law = {1: 1 - caps[p] / p}
        law.update({n: caps[p] * (p - 1) / p**n
                    for n in range(2, limit + 1)})
        next_pmf = {}
        for value, weight in pmf.items():
            for n, probability in law.items():
                if value * n <= limit:
                    at = value * n
                    next_pmf[at] = next_pmf.get(at, F(0)) + weight * probability
        pmf = next_pmf
        stage_counts.append(len(pmf))
    require("low_product_support", tuple(sorted(pmf)) == tuple(range(1, limit + 1)))
    require("positive_unretained_probability", F(0) < sum(pmf.values()) < 1)

    numerators = {}
    thresholds = {}
    for tau in range(limit + 1):
        threshold = tau + 1
        value = mean - threshold + sum((threshold - n) * pmf[n]
                                      for n in range(1, threshold))
        numerators[tau] = value
        thresholds[tau] = 1 - value / (target - tau)
    require("all_hinges_positive", all(b > 0 for b in numerators.values()))
    require("hinges_decrease", all(numerators[t + 1] < numerators[t]
                                   for t in range(limit)))
    require("hinge_first_difference", all(
        numerators[t] - numerators[t + 1] == 1 - sum(pmf[n] for n in range(1, t + 2))
        for t in range(limit)))

    tau = 5
    exact_b = numerators[tau]
    require("selected_exact_hinge", exact_b == F(
        19132074022251234990036997833948759259,
        18473247078046657922374787501704265625))
    upper_b = F(259, 250)
    require("simple_hinge_bound", exact_b < upper_b)
    require("selected_exact_loss_threshold", thresholds[tau] == F(
        93156290569797077871456808548959521991,
        112288364592048312861493806382908281250))
    require("tau5_best_threshold_in_checked_range", all(
        thresholds[tau] > thresholds[t] for t in thresholds if t != tau))

    uniform_loss = F(33, 40)
    uniform_survival = 1 - uniform_loss
    uniform_query = tau + upper_b / uniform_survival
    uniform_haar = pure_mass * uniform_survival
    uniform_reserve = 1 - (1 + uniform_query) * fresh_factor
    require("uniform_loss_below_exact_threshold", uniform_loss < thresholds[tau])
    require("uniform_query", uniform_query == F(273, 25) < target)
    require("uniform_haar", uniform_haar == F(1309, 32768))
    require("uniform_fresh_reserve", uniform_reserve == F(101, 7700))
    require("uniform_extended_haar", uniform_haar * uniform_reserve == F(1717, 3276800))

    # JQ11 is a cited all-height proof input, not a computed optimizer output.
    base_loss = F(1527182, 2044845)
    added_pairs = ((5, 11), (7, 11), (7, 13))
    tower_costs = {str(p) + "-" + str(q): caps[p] * caps[q] / ((p - 1) * (q - 1))
                   for p, q in added_pairs}
    require("complete_pair_tower_costs", tuple(tower_costs.values()) ==
            (F(1, 27), F(1, 45), F(1, 55)))
    loss = base_loss + sum(tower_costs.values())
    require("enlarged_all_height_loss", loss == F(1685537, 2044845))
    require("enlarged_loss_fits_uniform_threshold", uniform_loss - loss == F(11681, 16358760))
    survival = 1 - loss
    query = tau + upper_b / survival
    haar = pure_mass * survival
    reserve = 1 - (1 + query) * fresh_factor
    require("enlarged_query", query == F(195749971, 17965400) < target)
    require("enlarged_haar", haar == F(89827, 2239488))
    require("enlarged_extended_haar", haar * reserve == F(167202479, 275904921600))
    require("positive_fresh_reserve", reserve > 0)
    bounds_at_base = {t: t + b / (1 - base_loss) for t, b in numerators.items()}
    bounds_at_enlarged = {t: t + b / survival for t, b in numerators.items()}
    bounds_at_uniform = {t: t + b / uniform_survival for t, b in numerators.items()}
    require("tau3_best_for_base_in_checked_range", all(
        bounds_at_base[3] < value for t, value in bounds_at_base.items() if t != 3))
    require("tau5_best_for_enlarged_in_checked_range", all(
        bounds_at_enlarged[5] < value for t, value in bounds_at_enlarged.items() if t != 5))
    require("tau5_best_for_uniform_in_checked_range", all(
        bounds_at_uniform[5] < value for t, value in bounds_at_uniform.items() if t != 5))

    # Two different support families use earlier all-height source-loss
    # theorems. Their added inventories have disjoint supports from each base.
    broad_cases = {}
    specifications = (
        ("no_seven_in_higher_mixed_support", "report547 AS6", F(443407, 681615),
         (5, 11, 13, 17, 19), F(0), F(1384, 8415), F(50501, 61965),
         F(6075787, 573200), F(15763, 373248), F(13992863, 8360755200)),
        ("no_five_in_higher_mixed_support_plus357_and713", "report550 ST11", F(8564, 12393),
         (7, 11, 13, 17, 19), F(1, 55), F(194, 1683), F(561983, 681615),
         F(65215657, 5981600), F(7477, 186624), F(53605493, 91968307200)))
    for name, reference, loss_input, outside, old_cap, expected_cap, expected_loss, expected_query, expected_haar, expected_ext in specifications:
        weights = [F(1, p - 2) for p in outside]
        cap = prod(1 + w for w in weights) - 1 - sum(weights)
        broad_loss = loss_input + cap + old_cap
        broad_haar = pure_mass * (1 - broad_loss)
        broad_query = tau + upper_b / (1 - broad_loss)
        broad_reserve = 1 - (1 + broad_query) * fresh_factor
        require(name + "_complete_support_cap", cap == expected_cap)
        require(name + "_loss", broad_loss == expected_loss < uniform_loss)
        require(name + "_query", broad_query == expected_query < target)
        require(name + "_Haar", broad_haar == expected_haar)
        require(name + "_extended_Haar", broad_haar * broad_reserve == expected_ext > 0)
        broad_cases[name] = {"loss_input_reference": reference, "loss_input": loss_input,
                            "outside_prime_set": outside, "higher_support_cap": cap,
                            "additional_old_pair_cap": old_cap, "loss_upper": broad_loss,
                            "loss_margin": uniform_loss - broad_loss,
                            "query_upper": broad_query, "Haar_lower": broad_haar,
                            "extended_Haar_lower": broad_haar * broad_reserve}
    return {
        "primes": primes, "pure_caps": caps, "pure_mass_lower": pure_mass,
        "complete_comparator_mean": mean, "low_product_probabilities": pmf,
        "retained_product_cutoff": limit, "convolution_stage_state_counts": stage_counts,
        "hinges_by_tau": numerators, "target_loss_thresholds_by_tau": thresholds,
        "selected_tau": tau, "exact_hinge": exact_b, "rounded_hinge_upper": upper_b,
        "target": target, "fresh23_29_factor": fresh_factor,
        "uniform_loss_upper": uniform_loss, "uniform_query_upper": uniform_query,
        "uniform_Haar_lower": uniform_haar, "uniform_relative_reserve": uniform_reserve,
        "uniform_extended_Haar_lower": uniform_haar * uniform_reserve,
        "loss_input": {"reference": "report556 JQ11", "value": base_loss,
                       "verification": "cited ordinary theorem; optimizer not rerun"},
        "added_pair_tower_caps": tower_costs, "enlarged_loss_upper": loss,
        "enlarged_loss_margin": uniform_loss - loss,
        "enlarged_query_upper": query, "enlarged_Haar_lower": haar,
        "enlarged_relative_reserve": reserve, "enlarged_extended_Haar_lower": haar * reserve,
        "exact_query_bounds_at_base_loss": bounds_at_base,
        "exact_query_bounds_at_enlarged_loss": bounds_at_enlarged,
        "exact_query_bounds_at_uniform_loss": bounds_at_uniform,
        "broader_support_families": broad_cases,
        "checks": checks, "passed_count": len(checks), "Lean": "not run"}


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    result = calculate()
    args.output.write_text(json.dumps(result, indent=2, default=encode) + "\n", encoding="utf-8")
    print(json.dumps({"passed_count": result["passed_count"],
                      "exact_hinge": result["exact_hinge"],
                      "enlarged_query_upper": result["enlarged_query_upper"],
                      "enlarged_extended_Haar_lower": result["enlarged_extended_Haar_lower"],
                      "json_sha256": hashlib.sha256(args.output.read_bytes()).hexdigest()},
                     indent=2, default=encode))


if __name__ == "__main__":
    main()
