#!/usr/bin/env python3
"""Independently enumerate the full negative part for three five-parent hinges.

No producer import. The exact infinite first moment supplies the entire tail.
The report proves reduction from real h to the integer endpoints checked here.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import prod
from pathlib import Path

PARENTS = (3, 5, 7, 11, 13)
FIRST = (F(2, 3), F(4, 15), F(1, 6), F(1, 10), F(1, 12))
DEEP = (F(2), F(4, 3), F(7, 5), F(11, 9), F(13, 11))
GUARANTEED_RESERVE = F(
    203129722400814193208791597, 20692505911553620784640000000
)
CHECKS = {}


def check(name, condition):
    if not condition:
        raise ArithmeticError(name)
    CHECKS[name] = CHECKS.get(name, 0) + 1


def atom(i, ell):
    p, k, d = PARENTS[i], FIRST[i], DEEP[i]
    if ell == 0:
        return 1 - k
    if ell == 1:
        return k - d / p**2
    return d * F(p - 1, p ** (ell + 1))


def negative_part(t):
    """Direct hyperbolic-cross sum of E(t-C)_+, C=product(L_i+1)-1."""
    def recurse(i, volume, probability):
        if i == len(PARENTS):
            return probability * (t + 1 - volume)
        return sum((
            recurse(i + 1, volume * x, probability * atom(i, x - 1))
            for x in range(1, t // volume + 1)
        ), F(0))
    return recurse(0, 1, F(1)) if t else F(0)


def verify(certificate):
    check("producer_passed", certificate["status"] == "PASS")
    check("comparison_scope", certificate["conclusion_kind"] == "fixed-comparison-budget-obstruction")
    check("no_new_lean_claim", certificate["new_lean_verification"] is False)
    check("fixed_parent_set", tuple(certificate["critical_parent_set"]) == PARENTS)
    check("fixed_guaranteed_reserve", F(certificate["guaranteed_head_reserve"]) == GUARANTEED_RESERVE)
    check("exact_primary_owners", tuple(r["owner"] for r in certificate["critical_owner_rows"]) == (37, 41, 43))
    ec = prod(1 + k + d / (p * (p - 1))
              for p, k, d in zip(PARENTS, FIRST, DEEP)) - 1
    zeta = (F(15, 16) - F(2, 17 * 15)) * (F(17, 18) - F(2, 19 * 17))
    check("complete_first_moment", ec == F(95, 33) == F(certificate["critical_first_moment"]))
    check("two_unqueried_mass_factors", zeta == F(4138163, 4744224) == F(certificate["critical_unqueried_factor"]))
    negative = {t: negative_part(t) for t in range(29)}
    total = F(0)
    rows = []
    for owner in (37, 41, 43):
        domain = owner - 3
        source = next(r for r in certificate["critical_owner_rows"] if r["owner"] == owner)
        check("complete_endpoint_interval", [e["h"] for e in source["integer_endpoints"]] == list(range(12, domain + 1)))
        candidates = []
        for h in range(12, domain + 1):
            t = domain - h
            hinge = ec - t + negative[t]
            check("exact_hinge_nonnegative", hinge >= 0)
            debit = zeta * hinge / h
            endpoint = source["integer_endpoints"][h - 12]
            check("independent_exact_endpoint", endpoint["threshold"] == t and F(endpoint["debit"]) == debit)
            candidates.append((debit, h))
        fee, h = min(candidates)
        check("independent_full_minimum", F(source["exact_minimum"]) == fee and source["h"] == h)
        local = next(r for r in certificate["localization"]["owner_rows"] if r["owner"] == owner)
        check("same_critical_parent_union", tuple(local["worst_parents"]) == PARENTS)
        check("common_policy_matches_fixed_parent", F(local["fee"]) == fee and local["h"] == h)
        total += fee
        rows.append(dict(owner=owner, h=h, exact_minimum=str(fee),
                         minimum_decimal=float(fee), number_of_integer_endpoints=len(candidates)))
    check("independent_exact_sum", F(certificate["critical_sum"]) == total)
    check("independent_exact_excess", F(certificate["critical_excess"]) == total - GUARANTEED_RESERVE)
    check("three_owners_exceed_guaranteed_reserve", total > GUARANTEED_RESERVE)
    check("simple_rational_lower_bound", total > F(2861, 250000) > GUARANTEED_RESERVE)
    check("reported_simple_bound", F(certificate["simple_rational_lower_bound"]) == F(2861, 250000))
    return dict(
        status="PASS", conclusion_kind="fixed-comparison-budget-obstruction",
        new_lean_verification=False,
        scope=("The three complete fixed-parent hinge minima over integer endpoints; "
               "the report separately proves real-h and arbitrary unit-cost selection "
               "reductions. No actual violation-loss lower bound is asserted."),
        parents=PARENTS, reference_first_caps=list(map(str, FIRST)),
        reference_deep_caps=list(map(str, DEEP)), complete_first_moment=str(ec),
        unqueried_factor=str(zeta), rows=rows, sum=str(total), sum_decimal=float(total),
        guaranteed_head_reserve=str(GUARANTEED_RESERVE),
        excess=str(total - GUARANTEED_RESERVE),
        check_count=sum(CHECKS.values()), checks=CHECKS,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    source = args.directory / "five_parent_branch_hinge_certificate.json"
    raw = source.read_bytes()
    result = verify(json.loads(raw))
    result["certificate_sha256"] = sha256(raw).hexdigest()
    result["verifier_sha256"] = sha256(Path(__file__).read_bytes()).hexdigest()
    output = args.output if args.output else args.directory / "five_parent_hinge_independent.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in (
        "status", "conclusion_kind", "check_count", "sum_decimal",
        "guaranteed_head_reserve",
    )}, indent=2))


if __name__ == "__main__":
    main()
