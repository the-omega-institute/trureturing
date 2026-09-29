#!/usr/bin/env python3
"""Exact arithmetic for the six-direction unbounded-field hinge interface.

This consumes the already independently enclosed six-unary scalar gate.
It does not reconstruct that enclosure, find an arbitrary-height source,
or claim Lean verification.  Pinned source results supply the previously verified fixed data.
"""

import argparse
from hashlib import sha256
from fractions import Fraction as F
from itertools import combinations
import json
from math import prod
from pathlib import Path


R = (28, 30, 36, 40, 42, 46)
M = tuple(r - 1 for r in R)
KAPPA = F(1, 5000)
TARGET = F(19000)
T = (1, 8, 10, 12, 16, 20, 24, 32, 40, 48, 64, 80,
     96, 128, 160, 192, 256, 384)
UT = (1, 8, 10, 12, 16, 20, 24, 32, 40)
COEFFICIENTS = (
    (0, 12634, 52898, 34342, 41801, 0, 0, 0, 0),
    (0, 15374, 0, 60271, 58710, 0, 0, 0, 0),
    (0, 6885, 0, 24801, 28063, 34776, 25472, 0, 0),
    (0, 6385, 0, 16214, 19003, 12339, 49940, 0, 0),
    (0, 4735, 0, 15737, 15922, 7199, 51748, 0, 0),
    (0, 0, 5894, 11911, 11324, 0, 22024, 52293, 0),
)
Y_DEN = 242237485035
Y_NUM = (70591716887, 4617831060, 99883711989, 40776235983,
         676677240, 19109010499, 4156249250, 48436920, 2007332794,
         239722674, 1695060, 117799876, 7286909, 23220,
         3618837, 90558, 45279)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def hinge(x, threshold):
    return max(F(0), F(x) - threshold)


def unary(i, x):
    return sum((F(c, 100) * hinge(x, t)
                for c, t in zip(COEFFICIENTS[i], UT)), F(0))


def g_extended(x):
    x = F(x)
    require(x >= 1, "g is only used on [1,infinity)")
    for a, b in zip(T, T[1:]):
        if x <= b:
            return F(a * a) + (a + b) * (x - a)
    return F(384 * 384) + 640 * (x - 384)


def conjugate(s):
    s = F(s)
    require(0 <= s <= 640, "finite extended conjugate requires s <= 640")
    return max(s * v - v * v for v in T)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


DEPENDENCIES={'fibre_credit_depth_two_six_fresh_heights.json': '0f2d3de762fe183103ba4a01165f6138f59dfc1991a8d40831423ce16e06db35', 'fibre_credit_depth_two_conditioned_convex_source.json': '2b74e5eb1fbcacf2b9f9493affdc1df9ff17af6c8096df46a23d678d491df8a3'}

def calculate():
    directory=Path(__file__).resolve().parent
    loaded={}
    for name,digest in DEPENDENCIES.items():
        raw=(directory/name).read_bytes()
        require(sha256(raw).hexdigest()==digest,'pinned inherited six-direction/source result: '+name)
        loaded[name]=json.loads(raw)
    six=loaded['fibre_credit_depth_two_six_fresh_heights.json']
    source=loaded['fibre_credit_depth_two_conditioned_convex_source.json']
    fixed=six['fixed_penalties']
    require(tuple(fixed['capacities'])==R and tuple(fixed['Y_knots'])==T
            and tuple(fixed['thresholds'])==UT
            and tuple(tuple(row) for row in fixed['unary_hinge_coefficient_numerators'])==COEFFICIENTS,
            'unchanged previously enclosed six-unary gate')
    require(F(fixed['kappa'])==KAPPA and fixed['target']==TARGET
            and fixed['coefficient_denominator']==100,'fixed gate constants')
    require([(row['value'],F(row['probability'])) for row in source['Y']]
            ==[(v,F(n,Y_DEN)) for v,n in zip(T[1:],Y_NUM)],'same full comparator law')
    axes = tuple(range(6))
    pairs = list(combinations(axes, 2))
    higher = [j for size in range(3, 7) for j in combinations(axes, size)]
    outside = lambda j: prod(M[i] for i in axes if i not in j)
    higher_coefficient = sum(outside(j) for j in higher)
    pair_argument_caps = {",".join(str(i + 1) for i in j): KAPPA * outside(j)
                          for j in pairs}
    smax = max(pair_argument_caps.values())
    require(len(pairs) == 15 and len(higher) == 42, "support inventory")
    require(higher_coefficient == 934878, "higher-support coefficient")
    require(smax == F(100737, 200) < 640, "restricted dual argument bound")
    require(640 - smax == F(27263, 200), "strict tail dual slack")

    slopes = tuple(a + b for a, b in zip(T, T[1:]))
    require(all(a < b for a, b in zip(slopes, slopes[1:])), "convex secant slopes")
    require(slopes[-1] == 640, "terminal continuation slope")
    g_hinges = {T[0]: F(slopes[0])}
    for k in range(1, len(T) - 1):
        g_hinges[T[k]] = F(slopes[k] - slopes[k - 1])
    require(len(g_hinges) == 17 and sum(g_hinges.values()) == 640,
            "finite global hinge representation")
    check_points = tuple(F(t) for t in T) + tuple(F(a + b, 2) for a, b in zip(T, T[1:]))
    check_points += (F(385), F(1000), F(10**6))
    for x in check_points:
        represented = 1 + sum(c * hinge(x, t) for t, c in g_hinges.items())
        require(represented == g_extended(x), "piecewise-affine hinge identity")
    dual_points = (F(0), smax) + tuple(F(s) for s in slopes if s <= smax)
    for s in dual_points:
        for x in check_points:
            require(s * x - g_extended(x) <= conjugate(s), "Fenchel check")
        # On x>=384 the slope of sx-g(x) is exactly s-640<0.
        require(s - 640 < 0, "unbounded affine ray is decreasing")

    require(sum(Y_NUM) == Y_DEN and len(Y_NUM) == len(T) - 1, "Y probability law")
    ey = lambda f: sum((F(n, Y_DEN) * f(v) for v, n in zip(T[1:], Y_NUM)), F(0))
    mean = ey(F)
    square = ey(lambda x: F(x * x))
    unary_cost = sum(ey(lambda x, i=i: unary(i, x)) for i in axes)
    pair_cost = 15 * ey(g_extended)
    higher_cost = KAPPA * higher_coefficient * mean
    budget = unary_cost + pair_cost + higher_cost
    margin = TARGET - budget
    require(mean == F(354870451028, 26915276115), "reference mean")
    require(square == F(1940069387744, 8971758705), "reference square")
    require(ey(g_extended) == square, "reference law remains at square knots")
    require(unary_cost == F(72243007727020441, 6055937125875), "reference unary fee")
    require(budget == F(2670385906653884932, 151398428146875), "reference total fee")
    require(margin == F(206184228136740068, 151398428146875) > 0,
            "available aggregate excess")

    # For one common finite measure nu and H_nu(t)=sup_L integral(L-t)+,
    # this yields constant*nu(1) + sum_t profile_coeff[t]*H_nu(t).
    profile_coeff = {t: 15 * c for t, c in g_hinges.items()}
    for i in axes:
        for c, t in zip(COEFFICIENTS[i], UT):
            if c:
                profile_coeff[t] = profile_coeff.get(t, F(0)) + F(c, 100)
    profile_coeff[1] += KAPPA * higher_coefficient
    constant = 15 + KAPPA * higher_coefficient
    require(len(profile_coeff) == 17 and all(c > 0 for c in profile_coeff.values()),
            "17 positive finite hinge charges")
    profile_cost = constant + sum(c * ey(lambda x, t=t: hinge(x, t))
                                  for t, c in profile_coeff.items())
    require(profile_cost == budget, "reference finite-profile accounting")
    # An exact all-x identity gives the aggregate fee of replacing all fields by x.
    for x in check_points:
        joint = sum(unary(i, x) for i in axes) + 15 * g_extended(x)
        joint += KAPPA * higher_coefficient * x
        require(joint == constant + sum(c * hinge(x, t) for t, c in profile_coeff.items()),
                "aggregate common-field hinge identity")

    # One common abstract field law genuinely exceeds384 and still passes.
    # This witnesses strict weakening of a scalar condition, not arithmetic
    # realizability by old congruence queries.
    epsilon = F(1, 100000)
    atom1000_fee = sum(unary(i, 1000) for i in axes) + 15 * g_extended(1000)
    atom1000_fee += KAPPA * higher_coefficient * 1000
    relaxed_budget = (1 - epsilon) * budget + epsilon * atom1000_fee
    relaxed_margin = TARGET - relaxed_budget
    require(relaxed_margin > 0, "strictly weaker abstract unbounded-field example")
    require(epsilon * (1000 - 384) > 0, "old hard cap and Y-ICX both fail")

    density_coefficient = 1 / (KAPPA * prod(R))
    old_h = F(104726, 6084351)
    old_density = old_h * margin * density_coefficient
    require(old_density == F(2699106184481030045171, 53817625874009626674318000),
            "recovered shallow reference density")
    require(old_density > F(1, 20000), "reference density comparison")
    result = {
        "scope": "Exact arithmetic for an ordinary conditional all-height interface; existing six-variable enclosure is reused, not rerun.",
        "arbitrary_old_height_source_budget_proved": False,
        "lean_verification": False,
        "capacities": R, "kappa": KAPPA, "target": TARGET,
        "max_pair_conjugate_argument": smax,
        "terminal_g_slope": 640,
        "strict_slope_slack": 640 - smax,
        "individual_pair_argument_caps": pair_argument_caps,
        "g_hinge_coefficients": g_hinges,
        "uniform_profile_constant": constant,
        "uniform_profile_hinge_coefficients": dict(sorted(profile_coeff.items())),
        "reference_Y_stoploss": {t: ey(lambda x, t=t: hinge(x, t)) for t in profile_coeff},
        "reference_unary_cost": unary_cost,
        "reference_pair_cost": pair_cost,
        "reference_higher_support_cost": higher_cost,
        "reference_total_budget": budget,
        "strict_allowed_aggregate_excess": margin,
        "strict_weakening_abstract_example": {
            "all_fields_share_one_random_variable": True,
            "arithmetic_realizability_claimed": False,
            "law": "(1-epsilon)Y + epsilon*delta_1000",
            "epsilon": epsilon,
            "atom1000_aggregate_fee": atom1000_fee,
            "aggregate_budget": relaxed_budget,
            "positive_target_margin": relaxed_margin,
            "positive_stoploss_at384": epsilon * (1000 - 384),
        },
        "density_coefficient_for_h_times_target_minus_budget": density_coefficient,
        "recovered_shallow_density": old_density,
        "finite_piecewise_test_points": len(check_points),
        "finite_dual_test_points": len(dual_points),
        "proof_obligation": "Construct ONE actual supported measure nu<=Haar with target*nu(1) exceeding the actual summed fee, uniformly over all stated old heights/phases."
    }
    result['dependency_hashes']=DEPENDENCIES
    result['inherited_enclosure_replayed']=False
    return encode(result)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        require(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
                'retained result agrees with unbounded-field hinge interface')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)


if __name__=='__main__':main()
