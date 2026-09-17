#!/usr/bin/env python3
"""Exact actual survival bounds the unchanged three-hinge comparison.

Reconstruct complete finite source and removed-load histograms, integrate
the limiting actual tensor357 law in two orders, and recover the pinned49
numerator at404/A. Profile56 supplies the all-depth ordinary proof. The
reported lower bound concerns certifiable upper targets in that comparison
family, not actual K. Read-only unless --output is supplied.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/exact_survival_comparison_boundary.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
    'frontier/sharp_source_mass_endpoints.py': '79bb947d96c36895069f58568d7a5de2c22aa561753f03352e9eb741313147d9',
    'certificates/source_norms/full_linear_carrier_frontier.json': '237ed11241550037c69c855742d3f6e0a3a9c362ae2a861a173d3450e32375c0',
    'certificates/source_norms/allocated_seven_thresholds.json': '9400e4fae0a400edcc7ee7459103af677e512592823b683f67e7c896f8d345b8',
}
THRESHOLDS = (F(5, 2), F(4), F(5))
WEIGHTS = (F(1, 22), F(1, 6), F(4, 33))
BARRIERS = (F(7, 2), F(1), F(1))
CARRIER = (0, 1)
EXPECTED = {
    F(5, 2): (F(53959, 147000), F(1831, 18000), F(45803, 176400)),
    F(4): (F(3321163, 15435000), F(1777, 33750), -F(115939, 9261000)),
    F(5): (F(269853023, 1620675000), F(75899, 2025000), F(5098909, 243101250)),
}
EXPECTED_FLOOR = F(86218021264866661646394378315020528544556307,
                   208581453821091931839882213739521773400000)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def ceil(value):
    return -(-value.numerator // value.denominator)


def hinge(threshold, value):
    return max(F(value)-threshold, F(0))


def geom(base, start):
    """Complete zeroth and first moments of base**(-k), k>=start."""
    mass = F(1, base**(start-1)*(base-1))
    return mass, mass*(start+F(1, base-1))


def hinge_tail(base, start, threshold, multiplier=F(1)):
    entrance = max(start, ceil(threshold/multiplier))
    mass, moment = geom(base, entrance)
    return multiplier*moment-threshold*mass


def eta_hinge(threshold, multiplier):
    return (hinge(threshold, multiplier)/6+F(2, 9)*hinge(threshold, 2*multiplier)
            +2*hinge_tail(3, 3, threshold, multiplier))


def source_hinge(threshold, multiplier):
    """First integrate h_t(multiplier*Z) against the actual35 mass law."""
    value = (F(11, 120)*hinge(threshold, multiplier)+hinge(threshold, 2*multiplier)/40
             +F(3, 5)*hinge_tail(3, 3, threshold, multiplier))
    entrance = max(2, ceil(threshold/multiplier))
    value += sum(F(4, 5**m)*eta_hinge(threshold, multiplier*m) for m in range(2, entrance))
    mass, moment = geom(5, entrance)
    return value+4*(multiplier*moment-threshold*mass/2)


def pre_deletion_hinge(threshold):
    entrance = max(2, ceil(threshold))
    value = F(29, 35)*source_hinge(threshold, F(1))
    value += sum(F(36, 5*7**n)*source_hinge(threshold, F(n)) for n in range(2, entrance))
    mass, moment = geom(7, entrance)
    return value+F(36, 5)*(F(17, 24)*moment-threshold*mass/4)


def nu_hinge(threshold, multiplier):
    return (F(5, 18)*hinge(threshold, multiplier)+F(4, 9)*hinge(threshold, 2*multiplier)
            +5*hinge_tail(3, 3, threshold, multiplier))


def removed_hinge(threshold):
    """First integrate the cofactor-weighted ternary law, then the five law."""
    require(threshold >= 1, 'The omitted load-one term has zero hinge')
    entrance = max(2, ceil(threshold))
    value = F(4, 3)*hinge_tail(5, 2, threshold)
    value += sum(F(4, 5**m)*nu_hinge(threshold, F(m)) for m in range(2, entrance))
    mass, moment = geom(5, entrance)
    value += 4*(F(77, 36)*moment-threshold*mass)+nu_hinge(threshold, F(1))/20
    return value/5


def actual_source_integral(fn, cutoff, slope, intercept):
    """Independent integration order: combine the complete seven cost first."""
    def ternary(multiplier):
        entrance = max(3, ceil(F(cutoff, multiplier)))
        mass, moment = geom(3, entrance)
        return (sum(F(1, 3**k)*fn(k*multiplier) for k in range(3, entrance))
                +multiplier*slope*moment+intercept*mass)

    def eta(multiplier):
        return fn(multiplier)/6+F(2, 9)*fn(2*multiplier)+2*ternary(multiplier)

    mass, moment = geom(5, cutoff)
    return (F(11, 120)*fn(1)+fn(2)/40+F(3, 5)*ternary(1)
            +sum(F(4, 5**m)*eta(m) for m in range(2, cutoff))
            +4*(slope*moment+intercept*mass/2))


def reverse_removed_hinge(threshold):
    """First integrate all positive-five loads, then the cofactor ternary law."""
    five = lambda k: 4*hinge_tail(5, 2, threshold, F(k))
    cost = lambda k: five(k)+hinge(threshold, k)/20
    entrance = max(3, ceil(threshold))
    mass, moment = geom(3, entrance)
    return (five(1)/3+F(5, 18)*cost(1)+F(4, 9)*cost(2)
            +sum(F(5, 3**k)*cost(k) for k in range(3, entrance))
            +5*(moment/2-threshold*mass/4))/5


def actual_load_mass(value):
    """One exact atom of the raw actual357 survivor distribution."""
    eta = lambda k: F(1, 6) if k == 1 else F(2, 9) if k == 2 else F(2, 3**k)
    nu = lambda k: F(5, 18) if k == 1 else F(4, 9) if k == 2 else F(5, 3**k)

    def source(z):
        outside = F(11, 120) if z == 1 else F(1, 40) if z == 2 else F(3, 5*3**z)
        return outside+sum(F(4, 5**m)*eta(z//m) for m in range(2, z+1) if z % m == 0)

    cofactor = (F(11, 60) if value == 1 else F(4, 3*5**value))+nu(value)/20
    cofactor += sum(F(4, 5**m)*nu(value//m) for m in range(2, value+1) if value % m == 0)
    probability = lambda n: F(29, 35) if n == 1 else F(36, 5*7**n)
    result = sum(probability(n)*source(value//n) for n in range(1, value+1) if value % n == 0)-cofactor/5
    require(result >= 0, 'Nonnegative actual survivor load atom')
    return result


def exact_dilation_boundary(numerator, offset, denominator, surviving_four):
    """Remove only the n>=2 AP11 dilation compression, keeping the same caps."""
    masses = {value: actual_load_mass(value) for value in range(1, 5)}
    require((masses[1], masses[2]) == (F(23, 630), F(949, 29400)), 'Two actual low-load masses')
    probability = lambda n: F(28, 33) if n == 1 else F(50, 3*11**n)
    require(probability(1)+F(50, 3)*geom(11, 2)[0] == 1, 'Complete AP11 count probability')
    require(probability(1)+F(50, 3)*geom(11, 2)[1] == F(7, 6), 'Complete AP11 first moment')
    gap_one = (sum(probability(n)*(F(5, 2)*n-5) for n in range(3, 6))
               +25*geom(11, 6)[1])
    gap_two = F(25, 3)*geom(11, 3)[1]
    require((gap_one, gap_two) == (F(6653, 175692), F(31, 1452)), 'Complete dilation gaps at loads one and two')
    gain = (masses[1]*gap_one+masses[2]*gap_two)/7
    require(gain == F(32101757, 108472240800), 'Exact weighted raw survival gain')
    improved = denominator+gain
    mean = F(3, 20)+pre_deletion_hinge(F(1))-removed_hinge(F(1))
    require(mean == F(41, 72), 'Exact raw actual survivor first moment')

    def dilated_cost(n):
        return n*mean-5*F(3, 20)+sum(mass*(5-n*value) for value, mass in masses.items() if n*value < 5)

    tail0, tail1 = (F(50, 3)*v for v in geom(11, 5))
    exact_bad_cost = sum(probability(n)*dilated_cost(n) for n in range(1, 5))+tail1*mean-5*tail0*F(3, 20)
    require(improved == F(3, 20)-surviving_four/6-exact_bad_cost/7,
            'Independent exact AP11 dilation functional has the same boundary')
    require(improved == F(4044603032429, 42710944815000), 'Exact improved witness denominator')
    floor = offset+numerator/improved
    needed = numerator/(403-offset)-denominator
    require(floor == F(5072478916121259734553727325478823117587871,
                      12307961740440067066961922810098815200000) and floor > 403 and gain < needed,
            'Restoring the dilation alone still cannot reach403 with the fixed numerator')
    return {'physical_caps': ((11, F(5, 3)), (13, F(12, 7))), 'actual_low_load_masses': masses,
            'compression_gap_at_one': gap_one, 'compression_gap_at_two': gap_two,
            'raw_denominator_gain': gain, 'required_gain_for403': needed,
            'raw_survivor_first_moment': mean, 'exact_dilated_bad_cost': exact_bad_cost,
            'denominator_upper': improved, 'certifiable_K_lower_bound': floor,
            'scope': ('Only restores the full AP11 count dilation before the AP13/T5 bound. '
                      'The physical caps and profile49 numerator remain fixed; all original '
                      'blocks may choose the same actual tensor test. This is still a boundary '
                      'of a sufficient comparison, not an actual K lower bound.')}


def finite_laws(height):
    """Complete source and removed-cofactor distributions, including load one."""
    q = sum(F(1, 5**b) for b in range(1, height+1))
    t = sum(F(1, 3**a) for a in range(3, height+1))
    eta = {1: F(2, 9)-t, 2: F(2, 9),
           **{k: F(2, 3**k) for k in range(3, height+1)}, height+1: F(1, 3**height)}
    lam = {1: (1-q)*(F(2, 9)-t), 2: (2-5*q)/9-t*q,
           **{k: (1-2*q)*F(2, 3**k) for k in range(3, height+1)},
           height+1: (1-2*q)*F(1, 3**height)}
    five = {**{m: F(4, 5**m) for m in range(2, height+1)}, height+1: F(1, 5**height)}
    nu = {1: F(1, 3)-t, 2: F(4, 9),
          **{k: F(5, 3**k) for k in range(3, height+1)}, height+1: F(2, 3**height)}
    require(sum(nu.values()) == 1, 'Finite cofactor-weighted ternary mass is one')
    source, removed = defaultdict(F), defaultdict(F)
    for k in eta:
        source[k] += lam[k]-eta[k]/5
        removed[k] += nu[k]*(q-F(1, 5))
        for m, probability in five.items():
            source[k*m] += probability*eta[k]
            removed[k*m] += probability*nu[k]
    for m, probability in five.items():
        removed[m] += probability/3
    removed[1] += (F(4, 5)-q)/3
    return source, removed


def finite_seven_law(height):
    period = 7**height
    allowed = bytearray(b'\1')*period
    for e in range(1, height+1):
        allowed[6*7**(e-1)::7**e] = b'\0'*7**(height-e)
    count = sum(allowed)
    normalizer = F(count, period)
    require(normalizer == (5+F(1, period))/6, 'Exact finite pure7 normalizer')
    for e in range(1, height+1):
        require(all(allowed[x] for x in range(4, period, 7**e)), 'Original-seven test avoids pure7 deletion')
        for j in (1, 2, 3, 5):
            require(all(x % 7 != 4 and allowed[x] for x in range(j*7**(e-1), period, 7**e)),
                    'Every mixed7 deletion is pure7-allowed and has original test count one')
    tails = {e: F(1, 7**e)/normalizer for e in range(1, height+1)}
    probabilities = {1: 1-tails[1],
                     **{n: tails[n-1]-tails[n] for n in range(2, height+1)},
                     height+1: tails[height]}
    require(sum(probabilities.values()) == 1 and min(probabilities.values()) > 0,
            'Entire finite original-seven test distribution')
    kappa = sum(F(1, 7**e) for e in range(1, height+1))/normalizer
    return probabilities, kappa


def finite_check(constructor, height):
    """Independently enumerate actual masks; compare every load, not selected costs."""
    three, five = 3**height, 5**height
    all_five = (1 << five)-1
    state = [all_five]*three
    classes = {j: [0]*three for j in (1, 2, 3, 5)}
    cache = {}

    def cylinder(depth, residue):
        if (depth, residue) not in cache:
            cache[depth, residue] = sum(1 << y for y in range(residue, five, 5**depth))
        return cache[depth, residue]

    for a, b in product(range(height+1), repeat=2):
        if a+b == 0:
            continue
        aa, ra, bb, rb = constructor.source(a, b, 'off-diagonal')
        removed = cylinder(bb, rb)
        for x in range(ra, three, 3**aa):
            state[x] &= all_five ^ removed
        j, aa, ra, bb, rb = constructor.mixed(a, b, 'off-diagonal')
        cofactor = cylinder(bb, rb)
        for x in range(ra, three, 3**aa):
            require(not(classes[j][x] & cofactor), 'Old carriers are disjoint within each seven class')
            classes[j][x] |= cofactor
    nested = [cylinder(b, 4) for b in range(1, height+1)]
    strata = ([all_five ^ nested[0]]+[nested[j-1] ^ nested[j] for j in range(1, height)]
              +[nested[-1]])
    source, removed = defaultdict(F), defaultdict(F)
    for x in range(three):
        load_three = 1+sum(x % 3**a == 7 % 3**a for a in range(1, height+1))
        for load_five, mask in enumerate(strata, 1):
            z = load_three*load_five
            source[z] += F((state[x] & mask).bit_count(), three*five)
            removed[z] += sum(F((state[x] & mask & classes[j][x]).bit_count(), three*five)
                              for j in classes)
    expected_source, expected_removed = finite_laws(height)
    positive = lambda law: {z: value for z, value in law.items() if value}
    require(positive(source) == positive(expected_source), 'Entire actual finite source histogram')
    require(positive(removed) == positive(expected_removed), 'Entire actual finite removed-cofactor histogram')
    probabilities, kappa = finite_seven_law(height)
    source_mass, cofactor_mass = sum(source.values()), sum(removed.values())
    survivor_mass = source_mass-kappa*cofactor_mass
    q = sum(F(1, 5**b) for b in range(1, height+1))
    t = sum(F(1, 3**a) for a in range(3, height+1))
    require(source_mass == F(5, 9)-t-q and cofactor_mass == F(1, 3)+2*q/3,
            'Actual finite source and cofactor totals')
    rows = []
    for threshold, barrier in zip(THRESHOLDS, BARRIERS):
        pre = sum(mass*sum(prob*hinge(threshold, n*z) for n, prob in probabilities.items())
                  for z, mass in source.items())
        deletion = kappa*sum(mass*hinge(threshold, z) for z, mass in removed.items())
        rows.append({'threshold': threshold, 'pre_deletion_hinge': pre, 'deleted_hinge': deletion,
                     'actual_margin': barrier*survivor_mass-pre+deletion})
    return {'height': height, 'period35': three*five, 'source_mass': source_mass,
            'cofactor_mass': cofactor_mass, 'survivor_mass': survivor_mass, 'kappa': kappa,
            'carrier_weight': 1-F(1, 7**height), 'empty_weight': F(1, 7**height),
            'source_histogram': positive(source), 'removed_cofactor_histogram': positive(removed),
            'costs': rows}


def pinned_comparison(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Certificate IO source identity')
    io = module('exact_survival_io', base/'certificate_io.py')
    used = dict(PINS)
    for name, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin, 'Pinned input: '+name)
    old49 = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/full_linear_carrier_frontier.json'))
    current53 = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/allocated_seven_thresholds.json'))
    require(old49['schema'] == 'erdos7-full-linear-carrier-frontier-v1'
            and current53['schema'] == 'erdos7-allocated-seven-thresholds-v1', 'Exact comparison schemas')
    inherited = current53['source_sha256'] | current53['helper_sha256']

    def inherited_read(name):
        raw = io.read_artifact_bytes(base/name)
        require(name in inherited and sha256(raw).hexdigest() == inherited[name], 'Inherited pin: '+name)
        used[name] = inherited[name]
        return json.loads(raw)

    old46 = inherited_read('certificates/source_norms/joint_survival_carriers.json')
    old39 = inherited_read('certificates/source_norms/shared_source_deficits.json')
    for name, pin in (('frontier/verify_allocated_seven_thresholds.py', current53['verifier_sha256']),
                      ('frontier/verify_full_linear_carrier_frontier.py', old49['verifier_sha256']),
                      *current53['helper_sha256'].items()):
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Current comparison implementation: '+name)
        used[name] = pin
    require(current53['source_sha256']['certificates/source_norms/full_linear_carrier_frontier.json'] ==
            PINS['certificates/source_norms/full_linear_carrier_frontier.json'], 'Same fixed49 numerator input')
    source = module('exact_survival_source', base/'verify_joint_frontier.py')
    constructor = module('exact_survival_constructor', base/'frontier/sharp_source_mass_endpoints.py')
    dat = source.data(list(source.vertices())[404])
    require(dat[3:] == (F(1, 4), F(3, 20)), 'Same actual off-diagonal source endpoint')
    index = list(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4))).index(CARRIER)
    survival_row = next(r for a in old46['joint_survival']['row_blocks'] for b in a for r in b
                        if r['index'] == 404)
    survival = survival_row['conditional'][index]
    refined = next(r for a in old49['frontier']['row_blocks'] for r in a if r['index'] == 404)
    require(tuple(survival['carrier']) == CARRIER and F(survival['D_c']) == dat[4],
            'Same original carrier and actual mass endpoint')
    outside = F(old39['source_profiles']['quadratic_tail_weight'])
    require(outside > 0 and outside == F(old39['square_barrier_refinement']['quadratic_tail_weight']),
            'Pinned complete quadratic complement')
    independent = sum(F(row['independent_margin']) for row in refined['quadratic_directions'])
    square_margin = (F(refined['old_Mquad'])-independent)/outside
    require(square_margin == F(5701, 3888), 'Fixed square margin recovered from pinned49 aggregate')
    H16, H41, A81, cG = (F(old49[key]) for key in ('H16', 'H41', 'A81', 'cG'))
    require(all(old49[key] == current53[key] for key in ('H16', 'H41', 'A81', 'cG')),
            'The published53 comparison keeps the same numerator constants')
    Mq, Ml = F(refined['conditional_Mquad'][index]), F(refined['conditional_M41'][index])
    finite, tails = source.ap_product_distribution(((11, F(5, 3)), (13, F(12, 7))), 9)
    require(cG == tails[2]+sum(v*v*finite[v] for v in (7, 8)), 'Complete physical AP square-tail coefficient')
    raw81 = sum(prob*v*v*source.square357(F(81, v*v), dat) for v, prob in finite.items() if v < 7)
    correction = source.AC*Mq+Ml+cG*square_margin-raw81
    numerator = (source.AC*H16+H41+A81)*dat[4]-correction
    old_value = source.WHOLE_CONST+numerator/(F(23, 42)*dat[4]+F(survival['M']))
    require(old_value == F(old49['combined']), 'Recovered endpoint numerator exactly reproduces profile49 K')
    return io, constructor, numerator, source.WHOLE_CONST, square_margin, used


def calculate(base):
    io, constructor, numerator, offset, square_margin, used = pinned_comparison(base)
    finite = [finite_check(constructor, height) for height in (3, 4, 5, 6)]
    require(actual_source_integral(lambda v: F(1), 2, F(0), F(1)) == F(1, 4), 'Actual source total')
    require(actual_source_integral(lambda v: F(v), 2, F(1), F(0)) == F(17, 24), 'Actual source first moment')
    require(F(5, 18)+F(4, 9)+5*geom(3, 3)[0] == 1, 'Limiting cofactor-weighted ternary mass')
    require(F(5, 18)+F(8, 9)+5*geom(3, 3)[1] == F(77, 36), 'Limiting cofactor-weighted ternary moment')
    costs = []
    for threshold, barrier in zip(THRESHOLDS, BARRIERS):
        pre, deletion = pre_deletion_hinge(threshold), removed_hinge(threshold)
        entrance = max(2, ceil(threshold))
        tail0, tail1 = (F(36, 5)*v for v in geom(7, entrance))
        probability = lambda n: F(29, 35) if n == 1 else F(36, 5*7**n)
        cost = lambda v: sum(probability(n)*hinge(threshold, n*v) for n in range(1, entrance)) + (
            tail1*v-threshold*tail0)
        require(pre == actual_source_integral(cost, entrance, F(6, 5), -threshold),
                'Both complete orders of actual pre-deletion integration agree')
        require(deletion == reverse_removed_hinge(threshold), 'Both complete orders of deleted-hinge integration agree')
        margin = barrier*F(3, 20)-pre+deletion
        require((pre, deletion, margin) == EXPECTED[threshold], 'Exact simultaneous actual survivor costs')
        costs.append({'threshold': threshold, 'barrier': barrier, 'pre_deletion_hinge': pre,
                      'deleted_hinge': deletion, 'surviving_hinge': pre-deletion, 'actual_margin': margin})
    M = sum(weight*row['actual_margin'] for weight, row in zip(WEIGHTS, costs))
    denominator = F(23, 42)*F(3, 20)+M
    require(denominator == F(919, 924)*F(3, 20)-sum(
        weight*row['surviving_hinge'] for weight, row in zip(WEIGHTS, costs)), 'Same original AP survival functional')
    require(denominator == F(12117093811, 128357460000) and numerator > 0, 'Positive exact comparison boundary')
    floor = offset+numerator/denominator
    require(floor == EXPECTED_FLOOR and floor > 403, 'Exact fixed-numerator comparison obstruction')
    dilation = exact_dilation_boundary(numerator, offset, denominator, costs[1]['surviving_hinge'])
    return {'schema': 'erdos7-exact-survival-comparison-boundary-v1', 'source_vertex': 404,
            'carrier': CARRIER, 'source_mass': F(1, 4), 'survivor_mass': F(3, 20),
            'finite_actual_histograms': finite, 'complete_actual_costs': costs,
            'survival_weights': WEIGHTS, 'q': F(23, 42), 'combined_margin_upper': M,
            'denominator_upper': denominator, 'fixed_square_margin': square_margin,
            'fixed_numerator': numerator, 'offset': offset, 'certifiable_K_lower_bound': floor,
            'gap_above403': floor-403, 'exact_AP11_dilation': dilation, 'source_sha256': used,
            'scope': ('Lower bound on a certifiable upper target with the fixed49 numerator and unchanged '
                      'three-hinge survival functional. Uniform lower margins must apply to the whole actual '
                      'carrier mixture and admit its limiting endpoint, for example by lower semicontinuity '
                      'of that whole mixture margin. Actual source and mixed7 deletion costs are exact; no '
                      'separate deletion credits are added. Not a lower bound on actual K, not a Lean result, '
                      'and not a resolution of unrestricted Erdos7.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--output', type=Path)
    mode.add_argument('--check', action='store_true', help='Also compare the current canonical result artifact')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    if args.check:
        io = module('exact_survival_check_io', args.base/'certificate_io.py')
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical result matches reconstruction')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS:8 entire actual finite histograms,12 finite hinge costs, complete3/5/7 tails in two orders and pinned49 numerator.')
    print('The unchanged three-hinge comparison with that numerator has upper-target floor '+str(float(EXPECTED_FLOOR))+'.')
    print('Restoring exact AP11 dilation alone lowers that floor only to '+str(float(F(
        result['exact_AP11_dilation']['certifiable_K_lower_bound'])))+'.')
    print('This is not a lower bound on actual K; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    main()
