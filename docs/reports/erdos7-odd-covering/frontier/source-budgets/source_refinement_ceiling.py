#!/usr/bin/env python3
"""A fixed actual test bounds improvement of the current source comparison.

Reconstruct one actual endpoint, its complete tensor357 hinge integrals,
and the pinned49 numerator at that endpoint. No source-vertex scan or
threshold search is performed. Profile55 supplies the universal comparison
and limiting arguments. The reported lower bound is on a certifiable
upper target in a specified comparison family, never on actual K.
Read-only by default; --output writes standalone exact rational JSON.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/source-budgets/source_cost_endpoint_attainment.py': '860816267cfc11da898d207f1eb48486c6630d1dd3d00a785417a244188af47d',
    'certificates/source_norms/source-budgets/full_linear_carrier_frontier.json': '98631aaec7edbf0bbec41befad13df4ae9bcab2f6163675da10d8d7c9273c44c',
    'certificates/source_norms/comparison-bounds/allocated_seven_thresholds.json': 'ec6c4cf8b2c2f53179eead3d0a7499ca69fb796d57df6b65a91b0d672745a1b5',
}
BASELINE = (1, 1, 2, 2, 3)
WEIGHTS, CARRIER = (1, 2, 0, 0, 0), (0, 1)
EXPECTED_FLOOR = F(85359535508429362403462912894296348843645007,
                   168825936155207478969705582638937789792000)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def hinge(t, value):
    return max(F(value)-t, F(0))


def deep(fn, baseline, entrance, slope):
    count = max(0, entrance-baseline)
    require(fn(baseline+count+1)-fn(baseline+count) ==
            fn(baseline+count+2)-fn(baseline+count+1) == slope,
            'Actual test integral has the stated ternary affine entrance')
    return sum(F(1, 3**(k+3))*(fn(baseline+k+1)-fn(baseline+k)) for k in range(count)) + (
        slope*F(1, 2*3**(count+2)))


def actual_integral(source, dat, fn, cutoff, slope):
    """Direct actual tensor35 integral; no source-envelope maximum occurs."""
    d, n, eta, _, _ = dat
    value = sum(n[l]*fn(l, BASELINE[l]) for l in range(5))
    value += d[4]*deep(lambda v: fn(4, v), 3, cutoff, slope)
    for j in range(1, cutoff):
        increment = sum(eta[l]*(fn(l, (j+1)*BASELINE[l])-fn(l, j*BASELINE[l]))
                        for l in range(5))
        high = deep(lambda v: fn(4, (j+1)*v), 3, source.ceilq(F(cutoff, j+1)), (j+1)*slope)
        low = deep(lambda v: fn(4, j*v), 3, source.ceilq(F(cutoff, j)), j*slope)
        value += F(1, 5**j)*(increment+high-low)
    mean_three = sum(eta[l]*BASELINE[l] for l in range(5))+F(1, 18)
    return value+source.geom(5, cutoff)[0]*slope*mean_three


def finite_seven_law(height):
    period = 7**height
    allowed = [True]*period
    for e in range(1, height+1):
        for x in range(6*7**(e-1), period, 7**e):
            allowed[x] = False
    count = sum(allowed)
    mass = F(count, period)
    require(mass == (5+F(1, 7**height))/6, 'Actual finite pure7 source mass')
    tails = []
    for e in range(1, height+1):
        points = list(range(4, period, 7**e))
        require(all(allowed[x] for x in points), 'Nested original-seven test cylinder is source-free')
        tail = F(len(points), count)
        require(tail == F(1, 7**e)/mass, 'Exact actual finite nested-test probability')
        tails.append(tail)
    pmf = {1: 1-tails[0]}
    pmf.update({e+1: tails[e-1]-tails[e] for e in range(1, height)})
    pmf[height+1] = tails[-1]
    require(sum(pmf.values()) == 1 and min(pmf.values()) >= 0, 'Complete finite seven-count law')
    return pmf


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Certificate IO source identity')
    io = module('ceiling_io', base/'certificate_io.py')
    used = dict(PINS)
    for name, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin, 'Pinned input: '+name)
    old49 = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/full_linear_carrier_frontier.json'))
    current53 = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/allocated_seven_thresholds.json'))
    require(old49['schema'] == 'erdos7-full-linear-carrier-frontier-v1'
            and current53['schema'] == 'erdos7-allocated-seven-thresholds-v1', 'Exact comparison schemas')
    inherited = current53['source_sha256'] | current53['helper_sha256']

    def inherited_read(name):
        raw = io.read_artifact_bytes(base/name)
        require(name in inherited and sha256(raw).hexdigest() == inherited[name], 'Inherited input pin: '+name)
        used[name] = inherited[name]
        return json.loads(raw)

    old46 = inherited_read('certificates/source_norms/moments-survival/joint_survival_carriers.json')
    old39 = inherited_read('certificates/source_norms/source-budgets/shared_source_deficits.json')
    for name, pin in ((
            'frontier/comparison-bounds/verify_allocated_seven_thresholds.py', current53['verifier_sha256']), (
            'frontier/source-budgets/verify_full_linear_carrier_frontier.py', old49['verifier_sha256']),
            *current53['helper_sha256'].items()):
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Current comparison implementation: '+name)
        used[name] = pin
    require(current53['source_sha256']['certificates/source_norms/source-budgets/full_linear_carrier_frontier.json'] ==
            PINS['certificates/source_norms/source-budgets/full_linear_carrier_frontier.json'], 'Same fixed49 comparison')
    parent = module('ceiling_actual_attainment', base/'frontier/source-budgets/source_cost_endpoint_attainment.py')
    for name, pin in parent.PINS.items():
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Actual-family helper pin: '+name)
        used[name] = pin
    source = parent.load(base, 'verify_joint_frontier.py', 'ceiling_source')
    constructor = parent.load(base, 'frontier/source-budgets/sharp_source_mass_endpoints.py', 'ceiling_constructor')
    dat = source.data(list(source.vertices())[404])
    d, n, eta, s, D = dat
    require((s, D) == (F(1, 4), F(3, 20)) and source.BASES[9] == BASELINE,
            'Same actual off-diagonal endpoint and original tensor test')
    carrier_index = list(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4))).index(CARRIER)
    survival_row = next(r for a in old46['joint_survival']['row_blocks'] for b in a for r in b
                        if r['index'] == 404)
    survival = survival_row['conditional'][carrier_index]
    refined = next(r for a in old49['frontier']['row_blocks'] for r in a if r['index'] == 404)
    require(tuple(survival['carrier']) == CARRIER and F(survival['D_c']) == D,
            'Identical original carrier and actual mass endpoint')

    # Small actual-family checks, independent of the limiting integral formula.
    finite_checks = []
    for height in (3, 4):
        pmf = finite_seven_law(height)
        histogram, period = parent.finite_histogram(constructor, height)
        for t in (4, 5):
            class FiniteCost:
                @staticmethod
                def g(weight, v):
                    return sum(prob*hinge(F(t), k*v) for k, prob in pmf.items()) - (
                        F(weight, 5)*min(F(1), hinge(F(t), v)))
            direct = sum(F(count, period)*FiniteCost.g(WEIGHTS[l], z)
                         for (l, z), count in histogram.items())
            formula = parent.finite_formula(source, height, FiniteCost, WEIGHTS)
            require(direct == formula, 'Actual finite tensor357 source histogram and closed formula agree')
            finite_checks.append({'height': height, 'threshold': t, 'integral': direct})

    omega = tuple(F(w, 5) for w in WEIGHTS)
    w = tuple(9*x for x in eta)
    rest = (max(d)/18+(sum(w)+max(sum(w[:2]), sum(w[2:]))+max(w))/36+F(1, 72))/5
    hA = sum(omega[l]*n[l] for l in range(5))
    require(D == s-rest-hA, 'Unchanged complete deletion and carrier mass identity')
    integrate = lambda fn, cutoff, slope: actual_integral(source, dat, fn, cutoff, slope)
    require(integrate(lambda l, v: F(1), 2, F(0)) == s, 'Constant source integral')
    mean = integrate(lambda l, v: F(v), 2, F(1))
    costs, Mupper = [], F(survival['m25'])/22
    for t in (4, 5):
        tail0, tail1 = (F(36, 5)*x for x in source.geom(7, t)[:2])
        require(sum(source.zero7_probability(k) for k in range(1, t))+tail0 == 1,
                'Complete limiting seven probability')
        require(sum(k*source.zero7_probability(k) for k in range(1, t))+tail1 == F(6, 5),
                'Complete limiting seven first moment')
        cost = lambda v: sum(source.zero7_probability(k)*hinge(F(t), k*v) for k in range(1, t)) + (
            tail1*v-t*tail0)
        clip = lambda l, v: omega[l]*min(F(1), hinge(F(t), v))
        actual = integrate(lambda l, v: cost(v)-clip(l, v), t+1, F(6, 5))
        raw = integrate(lambda l, v: cost(v), t+1, F(6, 5))
        clipped = integrate(clip, t+1, F(0))
        require(actual == raw-clipped, 'Absorbed integral splits into its two actual integrals')
        separate = sum(source.zero7_probability(k)*integrate(
            lambda l, v: hinge(F(t), k*v), t+1, F(k)) for k in range(1, t)) + (
            tail1*mean-t*tail0*s)
        require(separate == raw, 'Independent order of exact seven expectation and actual35 integration')
        credit = F(4, 405*5**t)
        margin_upper = D-actual+credit
        gain = margin_upper-F(survival['m'+str(t)])
        require(gain == {4: F(611, 205800), 5: F(9841, 7203000)}[t], 'Exact old-source slack on the fixed actual test')
        Mupper += {4: F(1, 6), 5: F(4, 33)}[t]*margin_upper
        costs.append({'threshold': t, 'raw_hinge_integral': raw, 'clipped_integral': clipped,
                      'absorbed_integral': actual, 'margin_upper': margin_upper,
                      'old_margin': F(survival['m'+str(t)]), 'maximum_margin_gain': gain,
                      'retained_credit': credit})
    outside = F(old39['source_profiles']['quadratic_tail_weight'])
    require(outside > 0 and outside == F(old39['square_barrier_refinement']['quadratic_tail_weight']),
            'Pinned complete quadratic complement')
    independent = sum(F(row['independent_margin']) for row in refined['quadratic_directions'])
    square_margin = (F(refined['old_Mquad'])-independent)/outside
    require(square_margin == F(5701, 3888), 'Fixed square margin recovered from its pinned49 aggregate')
    H16, H41, A81, cG = (F(old49[key]) for key in ('H16', 'H41', 'A81', 'cG'))
    require(all(old49[key] == current53[key] for key in ('H16', 'H41', 'A81', 'cG')),
            'The published53 comparison keeps the same numerator constants')
    Mq = F(refined['conditional_Mquad'][carrier_index])
    Ml = F(refined['conditional_M41'][carrier_index])
    finite, tails = source.ap_product_distribution(((11, F(5, 3)), (13, F(12, 7))), 9)
    require(cG == tails[2]+sum(v*v*finite[v] for v in (7, 8)), 'Complete fixed square-tail coefficient')
    raw81 = sum(prob*v*v*source.square357(F(81, v*v), dat) for v, prob in finite.items() if v < 7)
    correction = source.AC*Mq+Ml+cG*square_margin-raw81
    numerator = (source.AC*H16+H41+A81)*D-correction
    denominator = F(23, 42)*D+Mupper
    require(numerator > 0 and denominator > 0, 'Positive fixed numerator and maximum available denominator')
    floor = source.WHOLE_CONST+numerator/denominator
    old_value = source.WHOLE_CONST+numerator/(F(23, 42)*D+F(survival['M']))
    require(old_value == F(old49['combined']), 'Same fixed404/A numerator exactly reproduces profile49 K')
    require(floor == EXPECTED_FLOOR and 403 < floor < F(current53['combined']),
            'Exact family obstruction and remaining published53 improvement room')
    return {'schema': 'erdos7-source-refinement-ceiling-v1', 'source_vertex': 404,
            'carrier': CARRIER, 's': s, 'D': D, 'Trest': rest, 'shallow_payment': hA,
            'tensor_mean35': mean, 'finite_actual_integral_checks': finite_checks,
            'costs': costs, 'fixed_h25_margin': F(survival['m25']),
            'fixed_square_margin': square_margin, 'M_upper': Mupper,
            'denominator_upper': denominator, 'fixed_numerator': numerator,
            'offset': source.WHOLE_CONST, 'certifiable_K_lower_bound': floor,
            'gap_above403': floor-403, 'maximum_gain_from49': F(old49['combined'])-floor,
            'remaining_possible_gain_from53': F(current53['combined'])-floor,
            'published53_K': F(current53['combined']), 'source_sha256': used,
            'scope': ('Lower bound on a certifiable upper target with fixed49 numerator, h25, '
                      'actual-mass bounds, deep deletion remainder and conditional27/81 credits. '
                      'Covers threshold allocation and any uniform source+shallow bound admitting '
                      'the stated actual endpoint limit. Not a lower bound on actual K, '
                      'an unrestricted impossibility theorem, or a Lean verification.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2],
                        help='Report root containing the pinned source helpers and certificates')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(args.base)
    if args.output is not None:
        args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    print('PASS:4 actual finite tensor integrals, complete3/5/7 tails, pinned404/A numerator and credits.')
    print('Any valid upper target in this comparison family is at least '+str(float(result['certifiable_K_lower_bound']))+'.')
    print('This is a comparison-family obstruction, not a lower bound on actual K; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    main()
