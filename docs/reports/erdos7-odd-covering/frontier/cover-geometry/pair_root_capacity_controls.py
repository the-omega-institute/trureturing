#!/usr/bin/env python3
"""Exact controls for the pair-conflict capacity certificate; standard library only."""
from fractions import Fraction
from itertools import combinations
from math import isqrt
import json


def primes_upto(limit):
    return [
        p for p in range(2, limit + 1)
        if all(p % d for d in range(2, isqrt(p) + 1))
    ]


def family_counts(ps):
    # Originals: prime classes at 3,5 and every p in ps;
    # 1 mod 5p; 4 mod p^2; 3 mod pq; CRT roots (1,2,2) mod 5pq.
    quotient_sum = sum(
        (Fraction(2, p) + Fraction(1, p*p) for p in ps), Fraction()
    ) + sum((Fraction(2, p*q) for p, q in combinations(ps, 2)), Fraction())
    no_prime_sum = sum(
        (Fraction(1, 4*(p-1)) + Fraction(1, p*(p-1)) for p in ps), Fraction()
    ) + sum(
        (Fraction(5, 4*(p-1)*(q-1)) for p, q in combinations(ps, 2)), Fraction()
    )
    original_sum = sum(
        (Fraction(1, p) for p in [3, 5, *ps]), Fraction()
    ) + sum(
        (Fraction(1, 5*p) + Fraction(1, p*p) for p in ps), Fraction()
    ) + sum((Fraction(6, 5*p*q) for p, q in combinations(ps, 2)), Fraction())
    return {
        "prime_list": ps,
        "prime_count": len(ps),
        "original_class_count": 2 + 3*len(ps) + len(ps)*(len(ps)-1),
        "quotient_reciprocal": str(quotient_sum),
        "quotient_reciprocal_decimal": float(quotient_sum),
        "original_reciprocal": str(original_sum),
        "no_prime_S0": str(no_prime_sum),
        "no_prime_S0_decimal": float(no_prime_sum),
    }, quotient_sum, no_prime_sum


small, q4, s4 = family_counts([7, 11, 13, 17])
assert q4 == Fraction(253544736, 289578289) < 1
assert s4 == Fraction(8706619, 39207168) < 1
small["quotient_union_bound_excludes"] = q4 < 1
small["original_no_prime_union_bound_excludes"] = s4 < 1

large, q71, s71 = family_counts([p for p in primes_upto(373) if p >= 7])
assert large["prime_count"] == 71
assert large["original_class_count"] == 5185
assert Fraction(501, 500) < s71 < Fraction(401, 400)
assert Fraction(153, 50) < q71 < Fraction(307, 100)
large["exact_S0_bracket"] = "501/500 < S0 < 401/400"
large["exact_quotient_bracket"] = "153/50 < reciprocal sum < 307/100"
large["quotient_union_bound_excludes"] = q71 < 1
large["original_no_prime_union_bound_excludes"] = s71 < 1

# All restrictions below are literal original residues.
# Fixed fibre x=1 mod5; exclude pure quotient classes from originals
# 7,25,35,49, and independently exclude the original prime-3 class.
period = 3*25*49
W = [
    x for x in range(period)
    if x % 3 != 0 and x % 5 == 1 and x % 25 != 1
    and x % 7 != 0 and x % 35 != 16 and x % 49 != 4
]
intersection = [x for x in W if x % 175 == 11]
assert len(W) == 272 and len(intersection) == 12
w_mass = Fraction(len(W), period)
kappa = Fraction(len(intersection), period)
assert w_mass == Fraction(2, 15)*Fraction(4, 5)*Fraction(34, 49)
assert kappa == Fraction(2, 15)*Fraction(1, 5)*Fraction(6, 49)
residual_five = {
    "original_classes_residue_modulus": [
        [0, 3], [0, 5], [0, 7], [1, 25], [16, 35], [4, 49], [11, 175]
    ],
    "period": period,
    "quotient_pure_first_roots": {"5": [0], "7": [3, 4]},
    "quotient_pure_49_residue": 30,
    "unmatched_quotient_35_residue": 2,
    "W_count": len(W),
    "intersection_175_count": len(intersection),
    "W_mass": str(w_mass),
    "W_mass_factorization": "(2/15)*(4/5)*(34/49)",
    "kappa_175": str(kappa),
    "kappa_175_factorization": "(2/15)*(1/5)*(6/49)",
}

# Full-height assignment control for the general multiplicity-two input.
# These are quotient classes, not claimed to be distinct original moduli.
mixed = [(a, b, r) for a in range(1, 4) for b in range(1, 4) for r in (2, 3)]
def assigned_prime(label):
    a, b, r = label
    return 5 if (a, b, r) == (1, 1, 2) or a == 3 or (a, b) == (2, 1) else 7
weighted_load_5 = sum((Fraction(1, 5**(a-1)) for a, b, r in mixed
                       if assigned_prime((a,b,r)) == 5), Fraction())
weighted_load_7 = sum((Fraction(1, 7**(b-1)) for a, b, r in mixed
                       if assigned_prime((a,b,r)) == 7), Fraction())
assert weighted_load_5 == Fraction(41,25) < 2
assert weighted_load_7 == Fraction(81,49) < 4
V5 = [x for x in range(125) if x % 5 not in (0,1)
      and all(x % 5**a != r for a,b,r in mixed if assigned_prime((a,b,r)) == 5)]
V7 = [x for x in range(343) if x % 7 not in (0,1)
      and all(x % 7**b != r for a,b,r in mixed if assigned_prime((a,b,r)) == 7)]
weighted_period = 125*343
V5set, V7set = set(V5), set(V7)
weighted_W = [x for x in range(weighted_period) if x % 125 in V5set and x % 343 in V7set]
all_classes = [(0,5),(1,5),(0,7),(1,7)] + [(r,5**a*7**b) for a,b,r in mixed]
assert len(V5) == 45 and len(V7) == 189 and len(weighted_W) == 8505
assert all(all(x % m != r for r,m in all_classes) for x in weighted_W)
rho5 = 1-(2+weighted_load_5)/5
rho7 = 1-(2+weighted_load_7)/7
assert rho5 == Fraction(34,125) and rho7 == Fraction(164,343)
assert weighted_period*rho5*rho7 == 5576
weighted_control = {
    "scope": "multiplicity-two quotient input; fixed empty pair tables",
    "pure_classes_residue_modulus": [[0,5],[1,5],[0,7],[1,7]],
    "mixed_classes_a_b_residue": mixed,
    "assigned_to_5": [v for v in mixed if assigned_prime(v) == 5],
    "assigned_to_7": [v for v in mixed if assigned_prime(v) == 7],
    "period": weighted_period,
    "input_class_count": len(all_classes),
    "count_capacity_sum": 6,
    "exception_count": len(mixed),
    "weighted_load_5": str(weighted_load_5),
    "weighted_load_7": str(weighted_load_7),
    "rho_5": str(rho5),
    "rho_7": str(rho7),
    "V5_count": len(V5),
    "V7_count": len(V7),
    "W_count": len(weighted_W),
    "uniform_branch_count_lower_bound": 5576,
    "every_W_residue_avoids_every_input_class": True,
}
print(json.dumps({
    "four_prime_control": small,
    "seventy_one_prime_control": large,
    "residual_five_control": residual_five,
    "weighted_assignment_control": weighted_control,
}, indent=2))
