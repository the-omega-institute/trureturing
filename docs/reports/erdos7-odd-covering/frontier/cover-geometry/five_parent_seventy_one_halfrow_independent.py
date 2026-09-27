#!/usr/bin/env python3
"""Independent exact/interval verification; never opens the producer source.

Rebuilds truncated product distributions from geometric atoms at 384 bits,
uses the exact full first moment for the infinite hinge complement, and
derives seventh moments using Stirling/falling-factorial geometric sums.
The finite Euler products themselves are computed exactly as Fractions.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from math import comb, factorial, isqrt, prod
from pathlib import Path
import json


CHECKS = Counter()


def check(name, condition):
    CHECKS[name] += 1
    if not condition:
        raise RuntimeError("independent check failed: " + name)


def rational(value):
    return F(str(value))


def ceildiv(n, d):
    return -((-n) // d)


def enclosure(q, scale):
    return q.numerator * scale // q.denominator, ceildiv(q.numerator * scale, q.denominator)


def tail(p, first, deep, e):
    if e == 0:
        return F(1)
    return first if e == 1 else deep / p**e


def atom(spec, x):
    p, first, deep = spec
    return tail(p, first, deep, x - 1) - tail(p, first, deep, x)


def first_moment(spec):
    p, first, deep = spec
    return 1 + first + deep / (p * (p - 1))


def complete_hinges(specs, max_t, scale):
    """Finite negative part + exact full mean; no positive-tail truncation."""
    lo = [0] * (max_t + 1)
    hi = [0] * (max_t + 1)
    lo[1] = hi[1] = scale
    for spec in specs:
        atoms = [None] + [enclosure(atom(spec, x), scale) for x in range(1, max_t + 1)]
        out_lo = [0] * (max_t + 1)
        out_hi = [0] * (max_t + 1)
        for u in range(1, max_t + 1):
            if hi[u] == 0:
                continue
            for x in range(1, max_t // u + 1):
                al, ah = atoms[x]
                out_lo[u * x] += lo[u] * al // scale
                out_hi[u * x] += ceildiv(hi[u] * ah, scale)
        lo, hi = out_lo, out_hi
        for x in range(1, max_t + 1):
            check("product_probability_enclosure_order", 0 <= lo[x] <= hi[x])
    ec = prod(first_moment(spec) for spec in specs) - 1
    answer = [(ec, ec)]
    cdf_lo = cdf_hi = correction_lo = correction_hi = 0
    for t in range(1, max_t + 1):
        cdf_lo += lo[t]
        cdf_hi += hi[t]
        correction_lo += cdf_lo
        correction_hi += cdf_hi
        lower = ec - t + F(correction_lo, scale)
        upper = ec - t + F(correction_hi, scale)
        check("full_hinge_enclosure_order", lower <= upper)
        answer.append((lower, upper))
    return ec, answer


def stirling2(n, k):
    row = [1]
    for _ in range(n):
        row = [0] + [j * (row[j] if j < len(row) else 0) + row[j - 1] for j in range(1, len(row) + 1)]
    return row[k] if k < len(row) else 0


def geometric_power(p, n):
    if n == 0:
        return F(1, p - 1)
    return sum(F(stirling2(n, k) * factorial(k) * p, (p - 1) ** (k + 1)) for k in range(1, n + 1))


def power_moment(spec, n):
    if n == 0:
        return F(1)
    p, first, deep = spec
    return 1 + deep * sum(comb(n, j) * geometric_power(p, j) for j in range(n)) + (first - deep / p) * (2**n - 1)


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def core_comparison_constants():
    d13 = F(1549, 1716)
    x3 = (3, F(2, 3), F(2))
    x13 = (13, F(1, 12), F(13, 11))
    xo = (37, F(1, 10), F(37, 10))
    mu1 = atom(x13, 1) - d13 * atom(xo, 1)
    negative = d13 * atom(xo, 2) - atom(x13, 2)
    positive = tail(*x13, 2) - d13 * tail(*xo, 2)
    check("signed_law_mu1", mu1 == F(1789, 17160))
    check("signed_law_negative", negative == F(3647, 317460))
    check("signed_law_positive_tail", positive == F(2891, 634920))
    check("signed_law_strict_gap", 3 * positive - negative == F(1379, 634920) > 0)
    expected = [F(167, 1716), F(3221, 51480), F(114641, 5714280), F(26853779, 8245706040), F(36528847721, 11898553815720), F(23037391749659, 17169613156083960)]
    # Product-probability buckets, rather than a separate hyperbolic sum per T.
    signed_buckets = [F(0) for _ in range(6)]
    for i in range(1, 6):
        for j in range(1, 6):
            if i * j < 6:
                signed_buckets[i * j] += atom(x3, i) * (atom(x13, j) - d13 * atom(xo, j))
    differences = []
    running = F(1) - d13
    for t in range(6):
        running -= signed_buckets[t]
        check("signed_product_small_threshold", running == expected[t] and running > 0)
        differences.append(str(running))
    return {"mu1": str(mu1), "negative_mass": str(negative), "positive_mass_above_two": str(positive), "gap": str(3 * positive - negative), "thresholds_zero_through_five": differences}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate", type=Path, default=Path(__file__).with_name("five_parent_seventy_one_halfrow_certificate.json"))
    parser.add_argument("--source", type=Path, default=Path(__file__).with_name("unqueried_head_four_parent_certificate.json"))
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    candidate_bytes = args.candidate.read_bytes()
    source_bytes = args.source.read_bytes()
    data = json.loads(candidate_bytes)
    source = json.loads(source_bytes)
    check("candidate_schema", data["schema"] == "five-parent-seventy-one-halfrow-v1")
    check("no_lean_claim", data["new_lean_verification"] is False)
    check("pinned_651_source", sha256(source_bytes).hexdigest() == data["source_sha256"] == "8bf5da7b70697b67e5f3df8b2787cbcac087841342423d028372ba4ebe903d2f")
    gamma = F(203129722400814193208791597, 20692505911553620784640000000)
    alpha = F(2673, 110656)
    check("source_gate", rational(data["head_gate"]) == rational(source["head_gate"]) == gamma)
    check("source_projection", rational(data["projection_alpha"]) == rational(source["projection_alpha"]) == alpha)
    check("policy_endpoints", data["first_five_parent_owner"] == 71 and data["finite_endpoint"] == 1253 and data["Euler_endpoint"] == 2187)
    primes = [p for p in range(3, 2188, 2) if all(p % q for q in range(2, isqrt(p) + 1))]
    finite_primes = [p for p in primes if 37 <= p < 1253]
    check("finite_prime_census", len(finite_primes) == 193)
    check("1253_composite", 7 * 179 == 1253 and 1253 not in primes)
    check("Euler_prime_census", len(primes) == 326)
    qset = (7, 11, 13, 17, 19)
    omitted = {7: F(5, 6)}
    omitted.update({q: F(q - 2, q - 1) - F(2, q * (q - 2)) for q in qset[1:]})
    z4 = prod(omitted[q] for q in (13, 17, 19))
    z5 = prod(omitted[q] for q in (17, 19))
    core = [(3, F(2, 3), F(2)), (5, F(4, 15), F(4, 3)), (7, F(1, 6), F(7, 5)), (11, F(1, 10), F(11, 9))]
    branch_specs = {"four": core, "five_head": core + [(13, F(1, 12), F(13, 11))], "five_outside": core + [(37, F(1, 10), F(37, 10))]}
    branch_factors = {"four": z4, "five_head": z5, "five_outside": z4}
    max_t = 1236
    scale = 2**384
    hinges = {}
    for name, specs in branch_specs.items():
        ec, tables = complete_hinges(specs, max_t, scale)
        params = data["branch_parameters"][name]
        check("branch_parents", params["parents"] == [spec[0] for spec in specs])
        check("branch_omission_factor", rational(params["factor"]) == branch_factors[name])
        check("branch_complete_first_moment", rational(params["exact_EC"]) == ec)
        hinges[name] = tables
    rows = data["finite_rows"]
    check("one_row_per_prime", [row["owner"] for row in rows] == finite_primes)
    independent_rows = []
    finite_lower = finite_upper = reported_upper_sum = F(0)
    finite_caps = {}
    for row in rows:
        p, h = row["owner"], row["h"]
        t = p - 3 - h
        roles = 4 if p < 71 else 5
        check("row_parameters", row["r"] == roles and row["D"] == p - 3 and row["N"] == 0 and row["t"] == t)
        check("row_domain", 10 <= h < p - 3 and 0 <= t <= max_t)
        cap = F(p - 1, h)
        check("row_same_source_cap", rational(row["cap"]) == cap and cap < F(p, 10))
        finite_caps[p] = cap
        names = ["four"] if roles == 4 else ["five_head", "five_outside"]
        branch_intervals = {name: tuple(branch_factors[name] * v / h for v in hinges[name][t]) for name in names}
        low = max(pair[0] for pair in branch_intervals.values())
        high = max(pair[1] for pair in branch_intervals.values())
        check("reported_fee_contains_independent_interval", rational(row["fee_lower"]) <= low <= high <= rational(row["fee_upper"]))
        expected_worst = "four" if roles == 4 else "five_head"
        check("row_worst_branch", row["worst_branch"] == expected_worst)
        if roles == 5:
            check("adopted_threshold_head_dominates_outside", branch_intervals["five_head"][0] >= branch_intervals["five_outside"][1])
        finite_lower += low
        finite_upper += high
        reported_upper_sum += rational(row["fee_upper"])
        independent_rows.append({"owner": p, "h": h, "t": t, "fee_lower": str(low), "fee_upper": str(high)})
    check("reported_finite_sum", reported_upper_sum == rational(data["finite_fee_upper"]))
    check("finite_sum_upper_verified", finite_upper <= reported_upper_sum)

    generic = core + [(13, F(1, 10), F(13, 10))]
    check("generic_reference_parameters", data["generic_reference"] == {"primes": [s[0] for s in generic], "first_caps": [str(s[1]) for s in generic], "deep_caps": [str(s[2]) for s in generic]})
    moments = [[power_moment(spec, j) for j in range(8)] for spec in generic]
    for i in range(5):
        for j in range(8):
            check("coordinate_geometric_moment", moments[i][j] == rational(data["coordinate_moments"][i][j]))
    count_moment7 = sum((-1)**(7 - j) * comb(7, j) * prod(moments[i][j] for i in range(5)) for j in range(8))
    check("complete_count_moment7", count_moment7 == rational(data["complete_fifth_role_count_moment7"]) > 0)
    sharp7 = F(2**7 * 6**6, 7**7)
    check("sharp_halfrow_scalar_constant", sharp7 == rational(data["sharp_halfrow_constant7"]))
    # All-integer padding: integrate (x-3)^(-7) from1252 to infinity.
    complete_tail = sharp7 * count_moment7 / (6 * 1249**6)
    check("complete_halfrow_tail", complete_tail == rational(data["complete_five_parent_tail"]))

    head_primes = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
    head_caps = (F(2), F(4, 3), F(7, 5), F(11, 9), F(13, 11), F(17, 15), F(19, 17), F(5, 3), F(20, 11), F(2))
    head_map = dict(zip(head_primes, head_caps))
    actual_head_first = {3: F(2, 3), 5: F(4, 15), **{q: F(1, q - 1) for q in qset}, 23: F(5, 69), 29: F(20, 319), 31: F(2, 31)}
    for head_index, p in enumerate(head_primes):
        for role in range(min(head_index + 1, 5)):
            rp, rf, rd = generic[role]
            check("generic_head_role_shallow", actual_head_first[p] <= rf)
            check("generic_head_role_deep", head_map[p] / p**2 <= rd / rp**2 and rp <= p)
    for rp, rf, rd in generic:
        check("generic_outside_role", F(1, 10) <= rf and F(1, 370) <= rd / rp**2 and rp <= 37)
    exact_m0 = exact_podd = F(1)
    census = Counter()
    factors = []
    for p in primes:
        if p in head_map:
            c = head_map[p]
            census["head"] += 1
        elif p < 1253:
            c = finite_caps[p]
            census["finite"] += 1
        else:
            c = F(2 * (p - 1), p - 3)
            census["half"] += 1
            check("actual_halfrow_cap", c < F(p, 10))
        factor = 1 + c * (F(3, p - 1) + F(2, (p - 1)**2))
        if p >= 1253:
            check("actual_halfrow_Euler_identity", factor == F((p + 1)**2, (p - 1) * (p - 3)))
        factors.append(factor)
        exact_podd *= F(p, p - 1)
    # Reverse exact multiplication, with no intermediate directed rounding.
    for factor in reversed(factors):
        exact_m0 *= factor
    check("actual_Euler_census", dict(census) == data["Euler_counts"] == {"head": 10, "finite": 193, "half": 123})
    m0lo, m0hi = rational(data["M0_lower"]), rational(data["M0_upper"])
    poddlo, poddhi = rational(data["Podd_lower"]), rational(data["Podd_upper"])
    check("exact_Euler_product_contained", m0lo <= exact_m0 <= m0hi)
    check("exact_Podd_product_contained", 0 < poddlo <= exact_podd <= poddhi)
    left = poly_mul(poly_mul([1, 2, 1], [-1, 1]), poly_mul(poly_mul([-1, 1], [-1, 1]), poly_mul([-1, 1], [-1, 1])))
    right = [0, 0, 0, 0] + poly_mul([-3, 1], [2, 0, 1])
    difference = [right[j] - left[j] for j in range(8)]
    check("Euler_polynomial_identity", difference == [1, -3, 1, 5, -11, 1, 0, 0])
    check("Euler_polynomial_positive_base", sum(difference[j] * 11**j for j in range(8)) > 0)
    check("complete_Euler_log_excess", rational(data["Gamma"]) == F(1, 2187) and 2187 % 2 == 1)
    ctail = F(2187, 2186)
    check("complete_Euler_exponential_bound", rational(data["Ctail"]) == ctail)
    type_i = F(1, 65536)
    check("ordinary_typeI_fee", rational(data["ordinary_typeI_fee"]) == type_i)
    fee_before = reported_upper_sum + complete_tail + type_i
    check("fee_before_arbitrary", rational(data["fee_before_arbitrary"]) == fee_before < gamma)

    policies = {}
    for name in ("RS_policy", "elementary_policy"):
        policy = data[name]
        k = policy["K"]
        v = 2**k
        check("policy_threshold", policy["arbitrary_threshold"] == v)
        if name == "RS_policy":
            check("RS_selected_policy", k == 46 and policy["density_denominator"] == 1250000)
            lower_log = F(1841, 240)
            check("RS_logarithmic_lower", lower_log == 7 * F(263, 240) and lower_log > 7)
            check("RS_ratio_constant", F(1, 1) + F(1, 98) == F(99, 98) and F(99, 98) / F(97, 98) == F(99, 97))
            polynomial_integral = sum(F(factorial(6), factorial(6 - j)) * F(7 * k, 10)**(6 - j) for j in range(7))
            fee = m0hi * ctail * F(99, 97)**6 * F(v, v - 3)**2 * polynomial_integral / (2 * (v - 1) * lower_log**6)
        else:
            check("elementary_selected_policy", k == 68 and policy["density_denominator"] == 6000000)
            ratio = F(1, 2) * F(k + 3, k + 2)**6
            check("elementary_tail_ratio", ratio < 1)
            fee = 2 * (m0hi * ctail / poddlo**6) * (4 * (k + 2))**6 * F(1, 2**k) / (1 - ratio)
        check("complete_arbitrary_parent_fee", rational(policy["fee"]) == fee)
        raw_margin = gamma - fee_before - fee
        projected = alpha * raw_margin
        check("same_source_raw_margin", rational(policy["raw_margin"]) == raw_margin > 0)
        check("same_source_projected_margin", rational(policy["projected_margin"]) == projected > F(1, policy["density_denominator"]))
        policies[name] = {"K": k, "fee": str(fee), "raw_margin": str(raw_margin), "projected_margin": str(projected), "density_denominator": policy["density_denominator"]}

    analytic_constants = core_comparison_constants()
    check("candidate_unchanged_during_verification", args.candidate.read_bytes() == candidate_bytes)
    mlo, mhi = enclosure(exact_m0, scale)
    plo, phi = enclosure(exact_podd, scale)
    check("independent_Euler_interval_contained", m0lo <= F(mlo, scale) <= F(mhi, scale) <= m0hi)
    check("independent_Podd_interval_contained", poddlo <= F(plo, scale) <= F(phi, scale) <= poddhi)
    report = {
        "schema": "five-parent-seventy-one-halfrow-independent-v1",
        "status": "PASS", "new_lean_verification": False,
        "scope": "Independent exact geometric-atom hinges, Stirling geometric seventh moments, exact finite Euler products, complete tail coefficients and both same-source density budgets; analytic source/comparison arguments remain ordinary mathematics",
        "candidate_sha256": sha256(candidate_bytes).hexdigest(),
        "source_sha256": sha256(source_bytes).hexdigest(),
        "verifier_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "producer_source_read": False,
        "interval_scale": str(scale), "finite_rows": independent_rows,
        "finite_fee_lower": str(finite_lower), "finite_fee_upper": str(finite_upper),
        "coordinate_moments": [[str(q) for q in row] for row in moments],
        "complete_moment7": str(count_moment7), "complete_halfrow_tail": str(complete_tail),
        "Euler_counts": dict(census),
        "M0_lower": str(F(mlo, scale)), "M0_upper": str(F(mhi, scale)),
        "Podd_lower": str(F(plo, scale)), "Podd_upper": str(F(phi, scale)),
        "signed_law_constants": analytic_constants,
        "policies": policies, "checks": dict(CHECKS), "check_count": sum(CHECKS.values()),
    }
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": "PASS", "check_count": report["check_count"], "candidate_sha256": report["candidate_sha256"], "output": str(args.output)}))


if __name__ == "__main__":
    main()
