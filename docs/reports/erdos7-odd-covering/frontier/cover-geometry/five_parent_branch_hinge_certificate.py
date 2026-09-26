#!/usr/bin/env python3
"""Exact five-parent comparison debits, with complete infinite first moments.

The fixed-parent obstruction is primary; 638 comparison types localize it.
This certificate does not lower-bound actual loss or upper-bound head mass.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
from math import isqrt, prod
from pathlib import Path

Q = (7, 11, 13, 17, 19)
HEAD = (3, 5) + Q + (23, 29, 31)
OUT = (37, 41, 43, 47, 53)
CRITICAL = (3, 5, 7, 11, 13)
CRITICAL_OWNERS = (37, 41, 43)
GUARANTEED_RESERVE = F(
    203129722400814193208791597, 20692505911553620784640000000
)
K1 = {
    3: F(2, 3), 5: F(4, 15), **{q: F(1, q - 1) for q in Q},
    23: F(5, 69), 29: F(20, 319), 31: F(2, 31),
    **{p: F(1, 12) for p in OUT},
}
DEEP = {
    3: F(2), 5: F(4, 3), **{q: F(q, q - 2) for q in Q},
    23: F(5, 3), 29: F(20, 11), 31: F(2),
    **{p: F(p, 12) for p in OUT},
}
Z = {
    7: F(5, 6),
    **{q: F(q - 2, q - 1) - F(2, q * (q - 2)) for q in Q if q != 7},
}
MAX_OWNER = 113
MAX_THRESHOLD = MAX_OWNER - 15
CHECKS = {}


def check(name, condition):
    if not condition:
        raise ArithmeticError(name)
    CHECKS[name] = CHECKS.get(name, 0) + 1


for p in HEAD + OUT:
    check("valid_decreasing_tail", 1 >= K1[p] >= DEEP[p] / p**2 > 0)
EM = {p: 1 + K1[p] + DEEP[p] / (p * (p - 1)) for p in HEAD + OUT}


@lru_cache(None)
def distribution(parents):
    """P(product(L_i+1)=m), exactly, for every needed m."""
    if not parents:
        return (F(0), F(1)) + (F(0),) * (MAX_THRESHOLD - 1)
    before = distribution(parents[:-1])
    p = parents[-1]
    atom = [F(0)] * (MAX_THRESHOLD + 1)
    for j in range(1, MAX_THRESHOLD + 1):
        ell = j - 1
        if ell == 0:
            atom[j] = 1 - K1[p]
        elif ell == 1:
            atom[j] = K1[p] - DEEP[p] / p**2
        else:
            atom[j] = DEEP[p] * F(p - 1, p ** (ell + 1))
    result = [F(0)] * (MAX_THRESHOLD + 1)
    for i in range(1, MAX_THRESHOLD + 1):
        for j in range(1, MAX_THRESHOLD // i + 1):
            result[i * j] += before[i] * atom[j]
    return tuple(result)


def calculate():
    branches = []
    for outside_count in range(6):
        for head in combinations(HEAD, 5 - outside_count):
            parents = tuple(sorted(head + OUT[:outside_count]))
            missing = tuple(q for q in Q if q not in head)
            zeta = prod((Z[q] for q in missing), start=F(1))
            mask = F(14, 15) if 3 not in head and 5 not in head else F(1)
            factor = zeta * mask
            ec = prod(EM[p] for p in parents) - 1
            dist = distribution(parents)
            psum = msum = F(0)
            hinges = []
            for t in range(MAX_THRESHOLD + 1):
                if t:
                    psum += dist[t]
                    msum += t * dist[t]
                # Full infinite positive part from its exact first moment.
                hinge = ec - t + (t + 1) * psum - msum
                check("full_hinge_nonnegative", hinge >= 0)
                if hinges:
                    check("full_hinge_decreases", factor * hinge <= hinges[-1])
                hinges.append(factor * hinge)
            branches.append(dict(
                parents=parents, head=head, outside_count=outside_count,
                missing_Q=missing, zeta=zeta, mask=mask, factor=factor,
                EC=ec, hinges=hinges,
            ))
    check("comparison_type_count", len(branches) == 638)
    critical = next(b for b in branches if b["parents"] == CRITICAL)
    check("critical_complete_first_moment", critical["EC"] == F(95, 33))
    check("critical_unqueried_factor", critical["zeta"] == F(4138163, 4744224))
    check("critical_central_mask", critical["mask"] == 1)

    critical_rows = []
    critical_sum = F(0)
    for owner, expected_h in zip(CRITICAL_OWNERS, (12, 15, 12)):
        domain = owner - 3
        endpoints = [dict(
            h=h, threshold=domain - h,
            debit=str(critical["hinges"][domain - h] / h),
        ) for h in range(12, domain + 1)]
        debit, h = min((F(e["debit"]), e["h"]) for e in endpoints)
        check("critical_minimizing_h", h == expected_h)
        check("critical_parent_precedes_owner", max(CRITICAL) < owner)
        check("critical_endpoint_coverage", len(endpoints) == domain - 11)
        critical_sum += debit
        critical_rows.append(dict(
            owner=owner, h=h, exact_minimum=str(debit),
            minimum_decimal=float(debit), integer_endpoints=endpoints,
        ))
    check("critical_sum_exceeds_guaranteed_reserve", critical_sum > GUARANTEED_RESERVE)
    check("simple_rational_lower_bound", critical_sum > F(2861, 250000))
    check("simple_rational_lower_bound_exceeds_reserve", F(2861, 250000) > GUARANTEED_RESERVE)

    primes = [p for p in range(37, MAX_OWNER + 1)
              if all(p % d for d in range(2, isqrt(p) + 1))]
    rows = []
    feesum = F(0)
    for owner in primes:
        eligible = [b for b in branches if not b["outside_count"]
                    or OUT[b["outside_count"] - 1] < owner]
        domain = owner - 3
        candidates = []
        for h in range(12, domain + 1):
            fee, index = max((b["hinges"][domain - h] / h, j)
                             for j, b in enumerate(eligible))
            candidates.append((fee, h, index))
        fee, h, wi = min(candidates)
        worst = eligible[wi]
        cap = F(owner - 1, h)
        check("one_fixed_actual_row_invariant", cap < F(owner, 12))
        # Localization only: these separate optima do not define the policy.
        separate, si = max(
            (min((b["hinges"][domain - hh] / hh, hh)
                 for hh in range(12, domain + 1)), j)
            for j, b in enumerate(eligible)
        )
        check("critical_controls_common_row", worst["parents"] == CRITICAL)
        feesum += fee
        row = dict(
            owner=owner, h=h, cap=str(cap), fee=str(fee), fee_decimal=float(fee),
            cumulative_fee=str(feesum), eligible_comparison_types=len(eligible),
            worst_parents=worst["parents"], worst_zeta=str(worst["zeta"]),
            worst_mask=str(worst["mask"]), worst_EC=str(worst["EC"]),
            max_of_separate_branch_minima=str(separate[0]),
            separate_branch_worst_h=separate[1],
            separate_branch_worst_parents=eligible[si]["parents"],
        )
        if owner in CRITICAL_OWNERS:
            primary = next(r for r in critical_rows if r["owner"] == owner)
            check("common_row_equals_fixed_parent_minimum",
                  fee == F(primary["exact_minimum"]) and h == primary["h"])
            groups = []
            for has3, has5 in ((True, True), (True, False), (False, True), (False, False)):
                group = [b for b in eligible
                         if (3 in b["head"]) == has3 and (5 in b["head"]) == has5]
                val, gi = max((b["hinges"][domain - h] / h, j)
                              for j, b in enumerate(group))
                branch = group[gi]
                groups.append(dict(
                    has3=has3, has5=has5, comparison_type_count=len(group),
                    max_at_common_h=str(val), decimal=float(val),
                    worst_parents=branch["parents"], missing_Q=branch["missing_Q"],
                    outside_count=branch["outside_count"],
                ))
            check("central_partition_complete",
                  sum(g["comparison_type_count"] for g in groups) == len(eligible))
            row["central_groups_at_common_h"] = groups
            qb = next(b for b in eligible if b["parents"] == Q)
            row["all_five_Q_at_common_h"] = str(qb["hinges"][domain - h] / h)
        rows.append(row)

    return dict(
        status="PASS", conclusion_kind="fixed-comparison-budget-obstruction",
        new_lean_verification=False,
        scope=("Completed cofactor count; unit cost per selected nonunit pattern; "
               "fixed auxiliary envelopes and omitted-coordinate factors; "
               "all real 12 <= h <= v-3-|S|. The inequality concerns comparison "
               "debits against a guaranteed head reserve, not actual losses."),
        source_policy=("One sequential law; globally fixed originals and phases; "
                       "normalized rows on every complete prior history, including "
                       "dead fibres; full-history density caps (v-1)/h < v/12."),
        producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        guaranteed_head_reserve=str(GUARANTEED_RESERVE),
        critical_parent_set=CRITICAL, critical_first_moment=str(critical["EC"]),
        critical_unqueried_factor=str(critical["zeta"]),
        critical_owner_rows=critical_rows, critical_sum=str(critical_sum),
        critical_sum_decimal=float(critical_sum),
        critical_excess=str(critical_sum - GUARANTEED_RESERVE),
        simple_rational_lower_bound=str(F(2861, 250000)),
        reference_k1={str(p): str(x) for p, x in K1.items()},
        reference_deep={str(p): str(x) for p, x in DEEP.items()},
        unqueried_coordinate_factors={str(p): str(x) for p, x in Z.items()},
        localization=dict(
            comparison_type_count=len(branches),
            enumeration_scope="Head subsets and outside counts, not actual sources or histories",
            owner_rows=rows, early_sum=str(feesum), early_sum_decimal=float(feesum),
        ),
        check_count=sum(CHECKS.values()), checks=CHECKS,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    result = calculate()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in (
        "status", "conclusion_kind", "check_count", "critical_sum_decimal",
        "guaranteed_head_reserve",
    )}, indent=2))


if __name__ == "__main__":
    main()
