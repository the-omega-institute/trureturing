#!/usr/bin/env python3
"""Independent all-menu check of the induced-mask comparison expression.

Uses only the candidate JSON and the prior independently authored655
geometric-atom verifier. Never opens the new producer's Python source.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import isqrt, prod
from pathlib import Path
import json
import runpy


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--candidate", type=Path)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    candidate_path = args.candidate or args.directory / "induced_mask_hinge_boundary.json"
    candidate_bytes = candidate_path.read_bytes()
    candidate = json.loads(candidate_bytes)
    helper_path = args.directory / "five_parent_seventy_one_halfrow_independent.py"
    helper_bytes = helper_path.read_bytes()
    lib = runpy.run_path(str(helper_path), run_name="induced_mask_math_library")
    check = lib["check"]
    checks = lib["CHECKS"]
    complete_hinges = lib["complete_hinges"]
    check("candidate_pin", sha256(candidate_bytes).hexdigest() == "c84d1a686569781fd3cc4d5da71bca6c1b557b98a1c237c90cd01a501a5f403a")
    check("candidate_metadata", candidate["schema"] == "induced-mask-hinge-boundary-v1" and candidate["new_lean_verification"] is False and candidate["not_a_full_branch_max_certificate"] is True)
    check("prior_independent_helper_pin", sha256(helper_bytes).hexdigest() == "1567153cf05d74bf95646f688cc5a27c5fd8f49f0fdd374b22649b721d56d9da")
    sources = {}
    for filename, expected in candidate["source_sha256"].items():
        blob = (args.directory / filename).read_bytes()
        check("source_pin", sha256(blob).hexdigest() == expected)
        sources[filename] = json.loads(blob)
    source651 = sources["unqueried_head_four_parent_certificate.json"]
    source655 = sources["five_parent_seventy_one_halfrow_certificate.json"]
    check("source_chain", source655["source_sha256"] == candidate["source_sha256"]["unqueried_head_four_parent_certificate.json"])
    gamma = F(203129722400814193208791597, 20692505911553620784640000000)
    alpha = F(2673, 110656)
    type_i = F(1, 65536)
    for data in (candidate, source651, source655):
        check("source_gate", F(data["head_gate"]) == gamma)
        check("source_projection", F(data["projection_alpha"]) == alpha)
        check("source_typeI", F(data["ordinary_typeI_fee"]) == type_i)

    qset = (7, 11, 13, 17, 19)
    ds = {q: F(5, 6) if q == 7 else F(q - 2, q - 1) - F(2, q * (q - 2)) for q in qset}
    zs = dict(ds)
    zs[7] = F(157, 210)
    beta = {(q, s): F(1, q * (q - 2) * (s - 1)) + F(1, (q - 1) * s * (s - 2)) for q, s in combinations(qset, 2)}

    def response(u):
        return prod(ds[q] for q in u) - sum(beta[tuple(sorted((q, s)))] * prod(ds[w] for w in u if w not in (q, s)) for q, s in combinations(u, 2))

    lam = 1 - sum(b / (zs[q] * zs[s]) for (q, s), b in beta.items())
    check("lambda_direct_reconstruction", lam == F(candidate["lambda_lower"]) == F(328686693796069, 337134711943765))
    check("insert_three_payment", ds[7] * lam > F(4, 5))
    check("insert_five_payment", ds[11] * lam > F(5, 6))
    for q in qset:
        # Mean and shallow/deep endpoints suffice; subsequent ratios grow.
        check("insert_three_mean", F(4, 5) * 2 >= F(q - 1, q - 2))
        check("insert_three_shallow", F(4, 5) * F(2, 3) >= F(1, q - 1))
        check("insert_three_deep", F(4, 5) * F(2, 9) >= F(1, q * (q - 2)) and q >= 3)
        if q >= 11:
            check("insert_five_mean", F(5, 6) * F(4, 3) >= F(q - 1, q - 2))
            check("insert_five_shallow", F(5, 6) * F(4, 15) >= F(1, q - 1))
            check("insert_five_deep", F(5, 6) * F(4, 75) >= F(1, q * (q - 2)) and q >= 5)
    responses = {}
    for mask in range(32):
        u = tuple(q for j, q in enumerate(qset) if mask & (1 << j))
        hu = response(u)
        lu = hu / prod(ds[q] for q in u)
        check("induced_positive", hu > 0)
        check("induced_lambda_floor", lam <= lu <= 1)
        responses[str(mask)] = str(hu)
        for q in qset:
            if q in u:
                continue
            enlarged = tuple(sorted((*u, q)))
            ratio = response(enlarged) / hu
            check("induced_insertion_lower", ds[q] * lam <= ratio)
            check("induced_insertion_upper", ratio <= ds[q])
    for q, s in combinations(qset, 2):
        remaining = tuple(x for x in qset if x not in (q, s))
        for mask in range(8):
            w = tuple(x for j, x in enumerate(remaining) if mask & (1 << j))
            difference = response(tuple(sorted((*w, s)))) - response(tuple(sorted((*w, q))))
            expanded = (ds[s] - ds[q]) * response(w) + sum((beta[tuple(sorted((q, u)))] - beta[tuple(sorted((s, u)))]) * prod(ds[x] for x in w if x != u) for u in w)
            check("induced_exchange_identity", difference == expanded)
            check("induced_exchange_positive", expanded >= 0)
    h4 = response((13, 17, 19))
    h5 = response((17, 19))
    check("H4_exact", h4 == F(candidate["H4"]) == F(10660439701, 13568480640))
    check("H5_exact", h5 == F(candidate["H5"]) == F(20681057, 23721120))
    check("last_outside_multiplier", h4 / h5 <= ds[13])

    specs = {
        3: (3, F(2, 3), F(2)),
        5: (5, F(4, 15), F(4, 3)),
        7: (7, F(1, 6), F(7, 5)),
        11: (11, F(1, 10), F(11, 9)),
        13: (13, F(1, 12), F(13, 11)),
    }
    branches = {"four": (3, 5, 7, 11), "five": (3, 5, 7, 11, 13), "four_baseline": (7, 11), "five_baseline": (7, 11, 13)}
    expected_means = {"four": F(23, 9), "five": F(95, 33), "four_baseline": F(1, 3), "five_baseline": F(5, 11)}
    scale = 2**384
    max_t = 1236
    check("threshold_range", candidate["threshold_max"] == max_t)
    hinge = {}
    for name, parents in branches.items():
        ec, values = complete_hinges([specs[p] for p in parents], max_t, scale)
        check("branch_exact_mean", ec == expected_means[name] == F(candidate["branches"][name]["EC"]))
        check("branch_parent_set", list(parents) == candidate["branches"][name]["parents"])
        hinge[name] = values
    primes = [p for p in range(37, 1253, 2) if all(p % j for j in range(2, isqrt(p) + 1))]
    check("prime_census", len(primes) == 193 == candidate["finite_prime_count"] and candidate["finite_endpoint"] == 1253)
    independent_rows = {"4": [], "5": []}
    policy_mins = {}
    menu_count = 0
    for r, name, coefficient in ((4, "four", h4), (5, "five", h5)):
        rows = candidate["rows"][str(r)]
        check("row_prime_census", [row["owner"] for row in rows] == primes)
        # Subtraction uses opposite endpoints: C_lo-B_hi/15, C_hi-B_lo/15.
        masked = [(coefficient * (c[0] - b[1] / 15), coefficient * (c[1] - b[0] / 15)) for c, b in zip(hinge[name], hinge[name + "_baseline"])]
        unmasked = [(coefficient * c[0], coefficient * c[1]) for c in hinge[name]]
        for row in rows:
            p, selected = row["owner"], row["h"]
            d = p - 3
            check("adopted_row_legal", row["r"] == r and 10 <= selected <= d)
            best_lower = best_upper = best_unmasked_lower = best_unmasked_upper = None
            upper_h = lower_h = unmasked_h = None
            runner_lower = None
            for h in range(10, d + 1):
                t = d - h
                lo, hi = (q / h for q in masked[t])
                ulo, uhi = (q / h for q in unmasked[t])
                check("all_menu_interval", lo <= hi and ulo <= uhi and hi <= uhi)
                check("all_menu_cap", F(p - 1, h) < F(p, 10))
                menu_count += 1
                if best_lower is None or lo < best_lower:
                    best_lower, lower_h = lo, h
                if best_upper is None or hi < best_upper:
                    best_upper, upper_h = hi, h
                if best_unmasked_lower is None or ulo < best_unmasked_lower:
                    best_unmasked_lower = ulo
                if best_unmasked_upper is None or uhi < best_unmasked_upper:
                    best_unmasked_upper, unmasked_h = uhi, h
                if h != selected and (runner_lower is None or lo < runner_lower):
                    runner_lower = lo
            t = d - selected
            chosen_lo, chosen_hi = (q / selected for q in masked[t])
            unmasked_lo, unmasked_hi = (q / selected for q in unmasked[t])
            check("independent_upper_argmin", upper_h == selected)
            check("selected_interval_contained", F(row["fee_lower"]) <= chosen_lo <= chosen_hi <= F(row["fee_upper"]))
            check("selected_strictly_beats_other_menu_lowers", F(row["fee_upper"]) < runner_lower)
            check("independent_lower_minimum", F(row["minimum_lower_over_all_h"]) <= best_lower <= best_upper <= F(row["fee_upper"]))
            check("unmasked_same_h_upper", unmasked_hi <= F(row["unmasked_same_h"]))
            check("unmasked_argmin_at_selected", unmasked_h == selected)
            check("unmasked_minimum_upper", best_unmasked_upper <= F(row["minimum_unmasked_over_all_h"]) == F(row["unmasked_same_h"]))
            # Enclosures are far narrower than10^-60; disallow spurious loose metadata.
            check("unmasked_reported_rounding_width", F(row["unmasked_same_h"]) - unmasked_lo < F(1, 10**60))
            check("minimum_lower_reported_width", best_upper - F(row["minimum_lower_over_all_h"]) < F(1, 10**60))
            check("same_h_mask_saving_identity", F(row["mask_saving_at_h"]) == F(row["unmasked_same_h"]) - F(row["fee_upper"]))
            saving_lo, saving_hi = (coefficient * x / (15 * selected) for x in hinge[name + "_baseline"][t])
            check("same_h_mask_saving_bound", F(row["mask_saving_at_h"]) <= saving_hi and F(row["mask_saving_at_h"]) + F(1, 10**60) >= saving_lo)
            summary = {"owner": p, "r": r, "upper_argmin_h": upper_h, "lower_argmin_h": lower_h, "unmasked_argmin_h": unmasked_h, "minimum_lower": str(best_lower), "minimum_upper": str(best_upper), "chosen_lower": str(chosen_lo), "chosen_upper": str(chosen_hi), "unmasked_minimum_lower": str(best_unmasked_lower), "unmasked_minimum_upper": str(best_unmasked_upper)}
            independent_rows[str(r)].append(summary)
            policy_mins[(r, p)] = summary

    check("complete_menu_count", menu_count == 228114)
    check("single_policy", len(candidate["policies"]) == 1)
    policy = candidate["policies"][0]
    check("policy_scope", policy["five_start"] == 67 and policy["controlling_branch_only"] is True and policy["uniform_expression_failure"] is True)
    selected_rows = [row for r in (4, 5) for row in candidate["rows"][str(r)] if (row["owner"] < 67) == (r == 4)]
    reported_lower = sum(F(row["minimum_lower_over_all_h"]) for row in selected_rows)
    reported_upper = sum(F(row["fee_upper"]) for row in selected_rows)
    gain = sum(F(row["minimum_unmasked_over_all_h"]) - F(row["fee_upper"]) for row in selected_rows)
    check("policy_reported_lower_sum", reported_lower == F(policy["finite_lower"]))
    check("policy_reported_upper_sum", reported_upper == F(policy["finite_upper"]))
    check("policy_comparison_gain", gain == F(policy["additional_mask_gain"]))
    check("policy_reported_reserve", gamma - type_i - reported_upper == F(policy["reserve_after_typeI"]) < 0)
    independent_lower = sum(F(policy_mins[(4 if p < 67 else 5, p)]["minimum_lower"]) for p in primes)
    independent_upper = sum(F(policy_mins[(4 if p < 67 else 5, p)]["minimum_upper"]) for p in primes)
    check("policy_independent_interval", reported_lower <= independent_lower <= independent_upper <= reported_upper)
    reserve_upper = gamma - type_i - independent_lower
    check("policy_expression_failure_from_lower_fees", reserve_upper < 0 and gamma - type_i - reported_lower < 0)
    check("candidate_unchanged", candidate_path.read_bytes() == candidate_bytes)
    result = {
        "schema": "induced-mask-hinge-boundary-independent-v1", "status": "PASS", "new_lean_verification": False,
        "scope": "Independent all-height hinge enclosures and all228114 legal h choices for the two fixed branches with the old D=v-3 domain; failure of that67 sufficient comparison expression only, not tighter-domain obstructions, actual-loss lower bounds, global masked-branch maxima or impossibility of noncoverage",
        "candidate_sha256": sha256(candidate_bytes).hexdigest(), "source_sha256": candidate["source_sha256"],
        "helper_sha256": sha256(helper_bytes).hexdigest(), "verifier_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "producer_source_read": False, "interval_scale": str(scale), "lambda_lower": str(lam), "H_responses": responses,
        "H4": str(h4), "H5": str(h5), "exact_means": {k: str(v) for k, v in expected_means.items()},
        "finite_prime_count": len(primes), "complete_menu_count": menu_count, "rows": independent_rows,
        "policy67": {"finite_lower": str(independent_lower), "finite_upper": str(independent_upper), "reserve_upper": str(reserve_upper), "reported_expression_gain": str(gain)},
        "not_a_full_branch_max_certificate": True, "not_an_actual_loss_lower_bound": True,
        "checks": dict(checks), "check_count": sum(checks.values()),
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "check_count": result["check_count"], "candidate_sha256": result["candidate_sha256"], "output": str(args.output)}))


if __name__ == "__main__":
    main()
