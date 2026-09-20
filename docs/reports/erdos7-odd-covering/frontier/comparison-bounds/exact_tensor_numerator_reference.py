#!/usr/bin/env python3
"""Exact AP-transformed cost reference on one actual357 tensor witness.

Evaluate the46 independent original-test costs and every low raw81 term
by two methods: direct complete tensor tails, and low-load atoms plus
complete moments. This reference is not a uniform numerator bound or
an attainment claim for the complete physical AP numerator. Profile61
states the ordinary distribution and convergence argument.
Read-only unless --output is explicitly supplied.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/exact_tensor_numerator_reference.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/moments-survival/exact_survival_comparison_boundary.py': 'e84d2f45275a8be328a7bb8bdcb0ef0d6d413148231517d9f457aeb278e7dd79',
    'certificates/source_norms/moments-survival/exact_survival_comparison_boundary.json': '23fa4a41ee72adafa5df06c2313d2234bde2031f3282cd234593665019b29dda',
    'certificates/source_norms/source-budgets/full_linear_carrier_frontier.json': 'e5f648527358ae4dc421a220e651a41a91f0d4995d8e78df7b4d4b5a05367529',
    'frontier/cover-geometry/ap_schedule.py': '40b6138fc9d0fc1d540880e8a4abb1933d1dcd1b2c5dbf54646008c3f2e62b9f',
    'frontier/comparison-bounds/fixed_cost.py': '2df5ca217aced5823c6c9d88324737091b11318c9625f73503ca7cd35db8c21d',
    'certificates/ap_schedule_norms.json': '7cbb82bb2ea8691136fe74779632ffb821f78dd3b0c498ea1625f84a3866d9d8',
}
CAPS = ((11, F(5, 3)), (13, F(12, 7)))
EXPECTED_NUMERATOR = F(23094865026612742148637380191186516404121,
                       809513462087178042210684534266400000000)
EXPECTED_REFERENCE = F(121572514359610080325508696442387688309540973,
                       375446616877965477311787984731139192120000)


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


def geometric_moment(base, start, degree):
    require(degree in (0, 1, 2), 'Complete moments through degree two')
    mass = F(1, base**(start-1)*(base-1))
    factors = (F(1), start+F(1, base-1),
               start*start+F(2*start, base-1)+F(base+1, (base-1)**2))
    return mass*factors[degree]


def actual_moments():
    """Closed actual source/cofactor moments, independently of low-load atoms."""
    records = []
    for degree in range(3):
        tail3 = geometric_moment(3, 3, degree)
        eta = F(1, 6)+F(2, 9)*2**degree+2*tail3
        lam = F(1, 8)+F(5, 72)*2**degree+tail3
        positive5 = 4*geometric_moment(5, 2, degree)
        source = lam+(F(4, 5)+positive5-1)*eta
        nu = F(5, 18)+F(4, 9)*2**degree+5*tail3
        cofactor = F(11, 60)+positive5/3+nu*(positive5+F(1, 20))
        seven = F(29, 35)+F(36, 5)*geometric_moment(7, 2, degree)
        survivor = source*seven-cofactor/5
        records.append({'degree': degree, 'eta_moment': eta, 'lambda_moment': lam,
                        'source35_moment': source, 'cofactor_moment': cofactor,
                        'normalized_pure7_moment': seven, 'survivor_moment': survivor})
    require([row['survivor_moment'] for row in records] == [F(3, 20), F(41, 72), F(331, 80)],
            'Exact raw actual357 survivor moments')
    return records


def direct_source_integral(fn, degree, leading, constant, cutoff):
    """Full actual35 tensor distribution integrated with complete polynomial tails."""
    cutoff = max(2, cutoff)

    def ternary(multiplier):
        entrance = max(3, ceil(F(cutoff, multiplier)))
        return (sum(F(1, 3**k)*fn(k*multiplier) for k in range(3, entrance))
                +leading*multiplier**degree*geometric_moment(3, entrance, degree)
                +constant*geometric_moment(3, entrance, 0))

    def eta(multiplier):
        return fn(multiplier)/6+F(2, 9)*fn(2*multiplier)+2*ternary(multiplier)

    eta_moment = F(1, 6)+F(2, 9)*2**degree+2*geometric_moment(3, 3, degree)
    return (F(11, 120)*fn(1)+fn(2)/40+F(3, 5)*ternary(1)
            +sum(F(4, 5**m)*eta(m) for m in range(2, cutoff))
            +4*(leading*eta_moment*geometric_moment(5, cutoff, degree)
                +constant*geometric_moment(5, cutoff, 0)/2))


def direct_removed_integral(fn, degree, leading, constant, cutoff):
    """Whole actual deleted integral; its load-one term is retained."""
    def five(multiplier):
        entrance = max(2, ceil(F(cutoff, multiplier)))
        return (sum(F(4, 5**m)*fn(multiplier*m) for m in range(2, entrance))
                +4*(leading*multiplier**degree*geometric_moment(5, entrance, degree)
                    +constant*geometric_moment(5, entrance, 0)))

    term = lambda k: five(k)+fn(k)/20
    entrance = max(3, cutoff)
    tail_leading = leading*(4*geometric_moment(5, 2, degree)+F(1, 20))
    tail_constant = constant/4
    return (F(11, 60)*fn(1)+five(1)/3+F(5, 18)*term(1)+F(4, 9)*term(2)
            +sum(F(5, 3**k)*term(k) for k in range(3, entrance))
            +5*(tail_leading*geometric_moment(3, entrance, degree)
                +tail_constant*geometric_moment(3, entrance, 0)))/5


def direct_actual_integral(source, tag):
    degree, leading, constant, cutoff = source.zero5_cost_metadata(tag)
    fn = lambda value: source.zero5_cost(tag, value)
    tail0 = F(36, 5)*geometric_moment(7, cutoff, 0)
    taild = F(36, 5)*geometric_moment(7, cutoff, degree)
    combined = lambda value: sum(source.zero7_probability(n)*fn(n*value) for n in range(1, cutoff)) + (
        leading*taild*value**degree+constant*tail0)
    total_moment = sum(source.zero7_probability(n)*n**degree for n in range(1, cutoff))+taild
    return (direct_source_integral(combined, degree, leading*total_moment, constant, cutoff)
            -direct_removed_integral(fn, degree, leading, constant, cutoff))


def atom_actual_integral(source, witness, moments, tag):
    """Independent finite correction to the complete polynomial moments."""
    degree, leading, constant, cutoff = source.zero5_cost_metadata(tag)
    fn = lambda value: source.zero5_cost(tag, value)
    require(degree in (1, 2) and cutoff >= 2, 'Supported actual transformed-cost tail')
    require(all(fn(value) == leading*value**degree+constant for value in range(cutoff, cutoff+3)),
            'Pinned transformed cost agrees with its complete polynomial tail')
    return (leading*moments[degree]+constant*moments[0]
            +sum(witness.actual_load_mass(value)*(fn(value)-leading*value**degree-constant)
                 for value in range(1, cutoff)))


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned certificate IO source')
    io = module('tensor_numerator_io', base/'certificate_io.py')
    used = dict(PINS)
    for name, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin, 'Pinned input: '+name)
    read = lambda name: json.loads(io.read_artifact_bytes(base/name))
    survival = read('certificates/source_norms/moments-survival/exact_survival_comparison_boundary.json')
    old49 = read('certificates/source_norms/source-budgets/full_linear_carrier_frontier.json')
    require(survival['schema'] == 'erdos7-exact-survival-comparison-boundary-v1'
            and old49['schema'] == 'erdos7-full-linear-carrier-frontier-v1', 'Exact49/56 schemas')
    for name, pin in survival['source_sha256'].items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin, 'Inherited56 input: '+name)
        used[name] = pin
    require(used['certificates/source_norms/source-budgets/full_linear_carrier_frontier.json'] ==
            PINS['certificates/source_norms/source-budgets/full_linear_carrier_frontier.json'], 'Same49 comparison')
    source = module('tensor_numerator_source', base/'verify_joint_frontier.py')
    witness = module('tensor_numerator_witness', base/'frontier/moments-survival/exact_survival_comparison_boundary.py')
    schedule = module('tensor_numerator_schedule', base/'frontier/cover-geometry/ap_schedule.py')
    fixed = module('tensor_numerator_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    specs, _, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    row = next(item for block in old49['frontier']['row_blocks'] for item in block if item['index'] == 404)
    carrier = old49['frontier']['carriers'].index([0, 1])
    D = F(survival['survivor_mass'])
    moment_records = actual_moments()
    moments = [item['survivor_moment'] for item in moment_records]
    require(D == moments[0] and F(survival['exact_AP11_dilation']['raw_survivor_first_moment']) == moments[1],
            'Same actual source mass and first moment as56')
    for threshold_row in survival['complete_actual_costs']:
        tag = ('h', F(threshold_row['threshold']))
        require(atom_actual_integral(source, witness, moments, tag) == F(threshold_row['surviving_hinge']),
                'Independent atom/moment method reproduces each actual survival cost')

    def actual(tag):
        value = atom_actual_integral(source, witness, moments, tag)
        require(value == direct_actual_integral(source, tag), 'Both complete integration methods agree')
        return value

    records = []
    M41 = Mquad = F(0)
    linear_values = quadratic_values = linear_barriers = quadratic_barriers = F(0)
    tuple_identity = lambda value: None if value is None else tuple(value)
    for index, spec in enumerate(specs):
        record = row['linear_directions'][index] if index < 41 else row['quadratic_directions'][index-41]
        require(tuple_identity(record['tuple']) == tuple_identity(spec['tuple']), 'Same original AP tuple')
        if index < 41:
            require(record['name'] == spec['name'], 'Same named linear cost')
        value, barrier = actual(spec['tag']), F(record['constant'])
        margin, old_margin = barrier*D-value, F(record['conditional'][carrier])
        weight = F(record['weight']) if index < 41 else F(1)
        require(margin >= old_margin, 'Actual transformed-cost margin exceeds its valid49 lower bound')
        if index < 41:
            M41 += weight*margin
            linear_values += weight*value
            linear_barriers += weight*barrier
        else:
            Mquad += margin
            quadratic_values += value
            quadratic_barriers += barrier
        degree, leading, constant, cutoff = source.zero5_cost_metadata(spec['tag'])
        records.append({'index': index, 'name': spec['name'], 'tuple': spec['tuple'], 'tag': spec['tag'],
                        'barrier': barrier, 'weight': weight, 'degree': degree,
                        'tail_leading': leading, 'tail_constant': constant, 'tail_entrance': cutoff,
                        'actual_integral': value, 'actual_margin': margin, 'old49_margin': old_margin,
                        'margin_gain': margin-old_margin})
    square = actual(('s', F(0)))
    square_barrier = F(45)
    square_margin = square_barrier*D-square
    require(square == F(331, 80) and square_margin == F(209, 80), 'Current signed square barrier45')
    old39 = read('certificates/source_norms/source-budgets/shared_source_deficits.json')
    outside = F(old39['source_profiles']['quadratic_tail_weight'])
    require(outside == F(1600217, 12882870) > 0, 'Complete quadratic complement')
    Mquad += outside*square_margin
    H16, H41, A81, cG = (F(old49[key]) for key in ('H16', 'H41', 'A81', 'cG'))
    finite, tails = source.ap_product_distribution(CAPS, 9)
    require(cG == tails[2]+sum(prob*n*n for n, prob in finite.items() if n in (7, 8)),
            'Same complete raw81 square coefficient, including atoms7 and8')
    dat = source.data(list(source.vertices())[404])
    raw81_terms = []
    for n, probability in sorted(finite.items()):
        if n >= 7:
            continue
        threshold = F(81, n*n)
        value, old = actual(('s', threshold)), source.square357(threshold, dat)
        require(value <= old, 'Actual square-hinge cost below the inherited raw source envelope')
        raw81_terms.append({'count': n, 'probability': probability, 'square_threshold': threshold,
                           'actual_raw_cost': value, 'old_raw_bound': old,
                           'actual_weighted_cost': probability*n*n*value,
                           'old_weighted_bound': probability*n*n*old})
    raw81 = sum(term['actual_weighted_cost'] for term in raw81_terms)
    old_raw81 = sum(term['old_weighted_bound'] for term in raw81_terms)
    N = (source.AC*H16+H41+A81)*D-source.AC*Mquad-M41-cG*square_margin+raw81
    residual_slope = (source.AC*(H16-quadratic_barriers-45*outside)
                      +(H41-linear_barriers)+(A81-45*cG))
    expanded = (residual_slope*D+source.AC*quadratic_values+linear_values
                +(source.AC*outside+cG)*square+raw81)
    require(expanded == N == EXPECTED_NUMERATOR, 'Independent expanded numerator identity and exact reference')
    old_M41, old_Mquad = F(row['conditional_M41'][carrier]), F(row['conditional_Mquad'][carrier])
    old_square_margin = F(survival['fixed_square_margin'])
    Nfixed = ((source.AC*H16+H41+A81)*D-source.AC*old_Mquad-old_M41
              -cG*old_square_margin+old_raw81)
    require(Nfixed == F(survival['fixed_numerator']), 'Same fixed numerator that forces the56 boundary')
    gains = {'linear41': M41-old_M41, 'quadratic5_and_complement': source.AC*(Mquad-old_Mquad),
             'raw81_square_tail': cG*(square_margin-old_square_margin), 'raw81_low_costs': old_raw81-raw81}
    require(min(gains.values()) >= 0 and sum(gains.values()) == Nfixed-N, 'Complete nonnegative numerator gap decomposition')
    denominator = F(survival['denominator_upper'])
    reference = source.WHOLE_CONST+N/denominator
    require(reference == EXPECTED_REFERENCE and reference < 403, 'Actual transformed-cost reference lies below403')
    require(len(records) == 46 and len(raw81_terms) == 6, 'All46 directions and six low raw81 terms')
    max_cutoff = max([record['tail_entrance'] for record in records]+[source.rootceil(F(81))])
    return {'schema': 'erdos7-exact-tensor-numerator-reference-v1', 'source_vertex': 404,
            'carrier': (0, 1), 'physical_caps': CAPS, 'survivor_moments': moment_records,
            'actual_low_load_masses': {value: witness.actual_load_mass(value) for value in range(1, max_cutoff)},
            'rows': records, 'actual_square': square, 'normalized_actual_square': square/D,
            'square_barrier': square_barrier, 'actual_square_margin': square_margin,
            'quadratic_complement_weight': outside, 'actual_M41': M41, 'actual_Mquad': Mquad,
            'raw81_low_terms': raw81_terms, 'raw81_square_coefficient': cG,
            'raw81_old': old_raw81, 'raw81_actual': raw81,
            'expanded_numerator_residual_slope': residual_slope, 'fixed_numerator': Nfixed,
            'tensor_numerator': N, 'numerator_gap': Nfixed-N, 'numerator_gap_components': gains,
            'denominator': denominator, 'offset': source.WHOLE_CONST, 'tensor_comparison': reference,
            'source_sha256': used,
            'scope': ('One actual357 tensor witness evaluated in all46 AP-transformed independent '
                      'cost directions and complete raw81 terms with the current signed square barrier45. '
                      'The resulting323.8077 reference is neither attainment of the full physical AP '
                      'numerator nor a uniform bound on K. It shows this witness does not force a403 '
                      'obstruction once the numerator comparison is also changed. No Lean result or '
                      'resolution of unrestricted Erdos7 is claimed.')}


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
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--output', type=Path)
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    if args.check:
        io = module('tensor_numerator_check_io', args.base/'certificate_io.py')
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical reference matches reconstruction')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS:complete moments,46 transformed costs in two independent integration methods,six raw81 costs and barrier45.')
    print('One actual357 tensor gives numerator '+str(float(EXPECTED_NUMERATOR))+' and comparison reference '+str(float(EXPECTED_REFERENCE))+'.')
    print('This is neither a uniform bound nor attainment of the complete physical numerator; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    main()
