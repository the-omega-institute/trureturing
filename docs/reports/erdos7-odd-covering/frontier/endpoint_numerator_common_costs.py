#!/usr/bin/env python3
"""Exact all-load majorants for the complete endpoint AP numerator.

The rational coefficients below are certificate inputs, not solver claims.
Every majorant is checked on the whole unbounded integer domain using the
pinned exact polynomial tails. No numerical optimizer is used by this program.
Only explicit --output writes; --check reconstructs the canonical certificate.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint_numerator_common_costs.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/exact_tensor_numerator_reference.py': 'a21c89792d50fba9fa66172bd3570f7df625606e8425eb216e987dcbeb0dd536',
    'frontier/endpoint_linear_numerator.py': '5c83f0a6277079323120ce0a31ac220c884f92ff555506f9dcaf926d3335e133',
    'certificates/source_norms/endpoint_linear_numerator.json': '1d5c0a6a2e9ba8e4d615f6963caa717f35e803ff531ab798420929d1d39bb981',
    'frontier/endpoint_square_common_pure3.py': '0e8f5204d947d3652178ff060be6c10539185a7f15666738249f67e3e229b4df',
    'certificates/source_norms/endpoint_square_common_pure3.json': '8b23c3cc87d5ddc40c0084ce42d6464f3c18d295451b5da994fa828cd21f1b69',
}
MAJORANTS = (
    (2, '0', ((2, '1'),)),
    (3, '-30784757/500000000', ((0, '30784757/500000000'), (25, '134728593/125000000'))),
    (4, '-235447359/1000000000', ((0, '235447359/1000000000'), (25, '45125929/1000000000'))),
    (5, '-3374161/125000000', ((0, '3374161/125000000'), (25, '2016613/1000000000'))),
    (6, '-614761/250000000', ((0, '614761/250000000'), (25, '4623/50000000'))),
    (7, '-26093/125000000', ((0, '26093/125000000'), (25, '781/200000000'))),
    (8, '-4283/250000000', ((0, '4283/250000000'), (25, '1/8000000'))),
    (9, '-55127/7812500', ((0, '55127/7812500'), (25, '624422193/500000000'))),
    (10, '-666198037/1000000000', ((0, '666198037/1000000000'), (25, '13932693/250000000'))),
    (11, '-13838099/200000000', ((0, '13838099/200000000'), (25, '1348183/1000000000'))),
    (12, '-63029389/200000000', ((0, '63029389/200000000'), (25, '62024209/1000000000'))),
    (13, '-16354117/200000000', ((0, '16354117/200000000'), (25, '1593307/1000000000'))),
    (14, '-21496339/500000000', ((0, '21496339/500000000'), (25, '657919/200000000'))),
    (15, '-92939/20000000', ((0, '92939/20000000'), (25, '35621/200000000'))),
    (16, '-467157/1000000000', ((0, '467157/1000000000'), (25, '887/100000000'))),
    (17, '-9073/200000000', ((0, '9073/200000000'), (25, '333/1000000000'))),
    (18, '0', ((18, '1'),)),
    (19, '-11531427/250000000', ((0, '11531427/250000000'), (25, '861710233/1000000000'), (34, '6505103/1000000000'))),
    (20, '-18811127/100000000', ((0, '18811127/100000000'), (25, '9035283/250000000'))),
    (21, '-21581173/1000000000', ((0, '21581173/1000000000'), (25, '323099/200000000'))),
    (22, '-122901/62500000', ((0, '122901/62500000'), (25, '37051/500000000'))),
    (23, '-83477/500000000', ((0, '83477/500000000'), (25, '3131/1000000000'))),
    (24, '-1713/125000000', ((0, '1713/125000000'), (25, '1/10000000'))),
    (25, '0', ((25, '1'),)),
    (26, '-532580943/1000000000', ((0, '532580943/1000000000'), (25, '1116161/25000000'))),
    (27, '-55338301/1000000000', ((0, '55338301/1000000000'), (25, '216171/200000000'))),
    (28, '-125889569/500000000', ((0, '125889569/500000000'), (25, '49674791/1000000000'))),
    (29, '-6539981/100000000', ((0, '6539981/100000000'), (25, '638687/500000000'))),
    (30, '-17186063/500000000', ((0, '17186063/500000000'), (25, '1317641/500000000'))),
    (31, '-185799/50000000', ((0, '185799/50000000'), (25, '142743/1000000000'))),
    (32, '-2919/7812500', ((0, '2919/7812500'), (25, '889/125000000'))),
    (33, '-567/15625000', ((0, '567/15625000'), (25, '267/1000000000'))),
    (34, '0', ((34, '1'),)),
    (35, '-8566127/125000000', ((0, '8566127/125000000'), (25, '2593289/250000000'))),
    (36, '-100579/12500000', ((0, '100579/12500000'), (25, '343493/1000000000'))),
    (37, '-18037/25000000', ((0, '18037/25000000'), (25, '9631/1000000000'))),
    (38, '-77980601/1000000000', ((0, '77980601/1000000000'), (25, '18817/1562500'))),
    (39, '-9183349/500000000', ((0, '9183349/500000000'), (25, '264217/1000000000'))),
    (40, '-10889649/1000000000', ((0, '10889649/1000000000'), (25, '472393/1000000000'))),
    (41, '-11571/10000000', ((0, '11571/10000000'), (25, '7787/500000000'))),
    (42, '0', ((0, '1'),)),
    (43, '-687618737/1000000000', ((1, '687618737/1000000000'), (49, '645714597/1000000000'))),
    (44, '-1795989/6250000', ((1, '1795989/6250000'), (48, '1/1000000000'), (49, '33154581/1000000000'))),
    (45, '-8881539/250000000', ((1, '8881539/250000000'), (49, '962997/1000000000'))),
    (46, '-325047831/1000000000', ((1, '325047831/1000000000'), (48, '1/1000000000'), (49, '38588533/1000000000'))),
    (47, '-11870507/250000000', ((1, '11870507/250000000'), (49, '658829/500000000'))),
    (48, '0', ((48, '1'),)),
    (49, '0', ((49, '1'),)),
    (50, '-116883117/200000000', ((1, '116883117/200000000'), (49, '12987013/31250000'))),
    (51, '-788961039/1000000000', ((1, '788961039/1000000000'), (49, '105519481/500000000'))),
    (52, '-220909091/250000000', ((1, '220909091/250000000'), (49, '116363637/1000000000'))),
    (53, '-116883117/125000000', ((1, '116883117/125000000'), (48, '1/1000000000'), (49, '12987013/200000000'))),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def verify_majorant(index, alpha, weights, functions, metadata, bounds, mass):
    require(0 <= index < len(functions) and len(weights) == len({i for i, _ in weights}),
            'Unique valid majorant indices')
    require(all(0 <= i < len(functions) and w >= 0 for i, w in weights),
            'Every upper-bound multiplier is nonnegative')
    active = [metadata[index]]+[metadata[i] for i, _ in weights]
    cutoff = max(row[3] for row in active)
    def polynomial(row):
        degree, leading, constant, _ = row
        require(degree in (1, 2), 'Exact affine or quadratic tail')
        return constant, leading if degree == 1 else F(0), leading if degree == 2 else F(0)
    target = polynomial(metadata[index])
    coefficients = [F(alpha) if j == 0 else F(0) for j in range(3)]
    for i, weight in weights:
        row = polynomial(metadata[i])
        coefficients = [a+weight*b for a, b in zip(coefficients, row)]
    constant, linear, quadratic = [a-b for a, b in zip(coefficients, target)]
    require(quadratic >= 0 and (quadratic > 0 or linear >= 0), 'Complete tail cannot fall to minus infinity')
    critical = {cutoff}
    if quadratic > 0:
        vertex = -linear/(2*quadratic)
        floor = vertex.numerator//vertex.denominator
        critical.update((max(cutoff, floor), max(cutoff, floor+1)))
    tail_values = {n: constant+linear*n+quadratic*n*n for n in sorted(critical)}
    low = [alpha+sum(w*functions[i](n) for i, w in weights)-functions[index](n)
           for n in range(1, cutoff)]
    require(min(low+list(tail_values.values())) >= 0, 'Exact majorant for every positive integer load')
    value = alpha*mass+sum(w*bounds[i] for i, w in weights)
    return {'target': index, 'mass_coefficient': alpha, 'weights': weights,
            'low_load_gaps': low, 'tail_entrance': cutoff,
            'tail_gap_polynomial': (constant, linear, quadratic),
            'tail_critical_values': tail_values, 'bound': value}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('common_cost_io', base/'certificate_io.py')
    used = dict(PINS)
    for name, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin, 'Pinned input: '+name)
    read = lambda name: json.loads(io.read_artifact_bytes(base/name))
    reference_module = module('common_cost_reference', base/'frontier/exact_tensor_numerator_reference.py')
    for name, pin in reference_module.PINS.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin, 'Inherited61 input: '+name)
        used[name] = pin
    square_path = 'certificates/source_norms/endpoint_square_common_pure3.json'
    require(square_path in PINS, 'The complete common-pure3 theorem must be pinned before delivery')
    square_input = read(square_path)
    require(square_input['source_vertex'] == 404 and square_input['carrier'] == [0, 1]
            and square_input['barrier'] == 45 and F(square_input['full_square_upper']) == F(469, 100),
            'Same actual endpoint class and proved square bound')
    linear = read('certificates/source_norms/endpoint_linear_numerator.json')
    require(linear['source_vertex'] == 404 and linear['carrier'] == [0, 1], 'Same linear endpoint class')
    D, L, Q = F(linear['endpoint']['surviving_mass']), F(linear['endpoint']['linear_numerator_upper']), F(square_input['full_square_upper'])
    require((D, L, Q) == (F(3, 20), F(1157, 1800), F(469, 100)), 'Actual mass and uniform moment caps')
    old = read('certificates/source_norms/full_linear_carrier_frontier.json')
    witness = read('certificates/source_norms/exact_survival_comparison_boundary.json')
    for name, pin in witness['source_sha256'].items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin, 'Inherited56 input: '+name)
        used[name] = pin
    source = module('common_cost_source', base/'verify_joint_frontier.py')
    schedule = module('common_cost_schedule', base/'frontier/ap_schedule.py')
    fixed = module('common_cost_fixed', base/'frontier/fixed_cost.py')
    specs, _, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    row = next(r for block in old['frontier']['row_blocks'] for r in block if r['index'] == 404)
    carrier = old['frontier']['carriers'].index([0, 1])
    records = row['linear_directions']+row['quadratic_directions']
    require(len(records) == len(specs) == 46, 'Complete original AP inventory')
    tags = [('h', F(0)), ('s', F(0))]+[spec['tag'] for spec in specs]
    bounds = [L, Q]+[F(record['constant'])*D-F(record['conditional'][carrier]) for record in records]
    finite, tails = source.ap_product_distribution(schedule.CAPS, 9)
    dat = source.data(list(source.vertices())[404])
    raw_specs = [(n, probability) for n, probability in sorted(finite.items()) if n < 7]
    require([n for n, _ in raw_specs] == list(range(1, 7)), 'All six low raw81 terms')
    for n, _ in raw_specs:
        threshold = F(81, n*n)
        tags.append(('s', threshold))
        bounds.append(source.square357(threshold, dat))
    metadata = [source.zero5_cost_metadata(tag) for tag in tags]
    functions = [lambda n, tag=tag: source.zero5_cost(tag, n) for tag in tags]
    require(tuple(item[0] for item in MAJORANTS) == tuple(range(2, 54)), 'Every46 cost and six raw81 targets')
    verified = [verify_majorant(i, F(a), [(j, F(w)) for j, w in weights], functions, metadata, bounds, D)
                for i, a, weights in MAJORANTS]
    new = [min(bounds[i], verified[i-2]['bound']) for i in range(2, 54)]
    old_m41 = F(row['conditional_M41'][carrier])
    old_mquad = F(row['conditional_Mquad'][carrier])
    M41 = sum(F(record['weight'])*(F(record['constant'])*D-new[i]) for i, record in enumerate(records[:41]))
    outside = F(read('certificates/source_norms/shared_source_deficits.json')['source_profiles']['quadratic_tail_weight'])
    require(outside == F(1600217, 12882870), 'Same complete quadratic complement')
    square_margin = 45*D-Q
    require(square_margin == F(103, 50), 'Signed square barrier45 retained')
    Mquad = sum(F(records[i]['constant'])*D-new[i] for i in range(41, 46))+outside*square_margin
    raw81 = sum(probability*n*n*new[46+k] for k, (n, probability) in enumerate(raw_specs))
    old_raw81 = sum(probability*n*n*bounds[48+k] for k, (n, probability) in enumerate(raw_specs))
    H16, H41, A81, cG = [F(old[key]) for key in ('H16', 'H41', 'A81', 'cG')]
    require(source.AC >= 0 and outside >= 0 and cG >= 0
            and all(F(r['weight']) >= 0 for r in records[:41]),
            'All cost upper bounds enter the numerator with nonnegative coefficients')
    require(cG == tails[2]+sum(p*n*n for n, p in finite.items() if n in (7, 8)), 'Complete raw81 square tail')
    N = (source.AC*H16+H41+A81)*D-source.AC*Mquad-M41-cG*square_margin+raw81
    old_square = F(witness['fixed_square_margin'])
    oldN = (source.AC*H16+H41+A81)*D-source.AC*old_mquad-old_m41-cG*old_square+old_raw81
    require(oldN == F(witness['fixed_numerator']), 'Unchanged fixed49 comparison')
    components = {'linear41': M41-old_m41, 'quadratic5_and_complement': source.AC*(Mquad-old_mquad),
                  'square_raw81_tail': cG*(square_margin-old_square), 'six_raw81_costs': old_raw81-raw81}
    require(min(components.values()) >= 0 and sum(components.values()) == oldN-N, 'Disjoint exact numerator improvement')
    # Expand the signed-barrier expression back into positive cost coefficients.
    Clinear = sum(F(r['weight'])*F(r['constant']) for r in records[:41])
    Cquad = sum(F(r['constant']) for r in records[41:])
    residual = source.AC*(H16-Cquad-45*outside)+(H41-Clinear)+(A81-45*cG)
    expanded = (residual*D+sum(F(r['weight'])*new[i] for i, r in enumerate(records[:41]))
                +source.AC*sum(new[41:46])+(source.AC*outside+cG)*Q+raw81)
    require(expanded == N, 'Independent positive-cost expansion of the whole numerator')
    denominator = F(witness['denominator_upper'])
    benchmark = source.WHOLE_CONST+N/denominator
    require(benchmark < 403, 'Endpoint numerator passes the specified actual-witness benchmark')
    # This denominator is a witness value, never a universal lower bound.
    return {'schema': 'erdos7-endpoint-numerator-common-costs-v1', 'source_vertex': 404, 'carrier': (0, 1),
            'source_sha256': used, 'mass': D, 'linear_upper': L, 'square_upper': Q,
            'universal_cost_constraint_bounds': bounds, 'majorants': verified, 'new_cost_bounds': new,
            'M41': M41, 'Mquad': Mquad, 'signed_square_margin': square_margin,
            'raw81': raw81, 'fixed_numerator': oldN, 'numerator_upper': N,
            'improvement_components': components, 'total_numerator_improvement': oldN-N,
            'positive_cost_residual_slope': residual, 'witness_denominator': denominator,
            'offset': source.WHOLE_CONST, 'witness_denominator_benchmark': benchmark,
            'benchmark_slack_below403': 403-benchmark,
            'scope': ('Uniform endpoint upper bound for the AP-transformed numerator over independent '
                      'original tests. The ratio using the specified actual tensor denominator is only '
                      'a benchmark; that denominator is not a universal lower bound. No global K '
                      'improvement, Lean verification or unrestricted Erdos7 resolution is claimed.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('common_cost_output_io', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical exact all-cost certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:52 majorants on all integer loads,46 independent numerator costs,six raw81 costs and complete tails.')
    print('Endpoint numerator upper '+str(float(F(result['numerator_upper'])))+
          '; specified witness-denominator benchmark '+str(float(F(result['witness_denominator_benchmark'])))+'.')
    print('The witness denominator is not a uniform lower bound; global K and unrestricted Erdos7 remain open.')


if __name__ == '__main__':
    main()
