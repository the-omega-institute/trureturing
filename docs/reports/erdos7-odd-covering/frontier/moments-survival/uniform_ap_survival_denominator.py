#!/usr/bin/env python3
"""Complete AP11/AP13 survival denominator on one actual K-source neighborhood."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/uniform_ap_survival_denominator.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/comparison-bounds/uniform_k_neighborhood_cost.py': '365265347aca1ee5a179df991be2316219f0cb4dbe7a5606a020664c3a56723b',
    'frontier/comparison-bounds/uniform_mean_cost_portfolio.py': 'ac23f83b0b99ff97bbff947826aff3c170aa4279517d3f440550f9277b769238',
    'certificates/source_norms/moments-survival/whole_block_mean_survival.json': 'cbccfcf1f81cf5d2185494f1a3a46674148a9d574ab3abebba0f6f0f3ba7eabd',
    'certificates/source_norms/endpoint-bounds/endpoint_k_face_forced27.json': '59202ce65324295b32b028f6b67f90e4a7b8bbba5f62608a43f9bc4979dc8e79',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def complete_error_tail(prime, start, envelope, error):
    """Exact infinite sum of min(error, envelope * prime ** -n)."""
    require(prime > 1 and start >= 0 and envelope >= 0 and error >= 0,
            'Nonnegative geometric error inputs')
    geometric = F(1, prime**start)/(1-F(1, prime))
    if error == 0 or envelope == 0:
        return {'crossing': None, 'geometric_sum': geometric, 'error_sum': F(0)}
    cut = start
    while envelope*F(1, prime**cut) > error:
        cut += 1
    require(envelope*F(1, prime**cut) <= error
            and (cut == start or envelope*F(1, prime**(cut-1)) > error),
            'Exact geometric crossing, including equality')
    total = (cut-start)*error+envelope*F(1, prime**cut)/(1-F(1, prime))
    return {'crossing': cut, 'geometric_sum': geometric, 'error_sum': total}


def uniform_H1(par):
    """Transport75's adopted cylinder caps; H1 excludes the unit mass S."""
    delta, rho = par['delta'], par['rho']
    require(0 <= delta <= F(2, 27) and 0 <= rho <= F(1, 2600),
            'H1 source transport lies inside the audited forcing domain')
    finite_data = ((3, F(7, 90), 2, 8), (9, F(1, 18), 2, 8),
                   (5, F(14, 225), 3, 23), (15, F(8, 225), 2, 21),
                   (45, F(4, 225), 2, 21))
    bounded = []
    for modulus, face, cd, cr in finite_data:
        transported = face+cd*delta+cr*rho
        bounded.append({'modulus': modulus, 'face': face, 'delta_coefficient': cd,
                        'rho_coefficient': cr, 'transported_upper': transported,
                        'raw_haar_cap': F(1, modulus), 'upper': min(transported, F(1, modulus))})
    errors = (par['kbar']*rho, rho+delta/240, rho, rho)
    tails = []
    for name, prime, start, c, H, error in zip(('pure3', 'pure5', 'root5', 'cell5'),
                                             (3, 5, 5, 5), (3, 2, 2, 2),
                                             par['c'], par['H'], errors):
        row = complete_error_tail(prime, start, H, error)
        row.update({'name': name, 'prime': prime, 'start': start, 'reference_coefficient': c,
                    'envelope': H, 'error': error, 'upper': c*row['geometric_sum']+row['error_sum']})
        tails.append(row)
    mixed = F(1, 72)
    positive7 = F(11, 72)+119*delta/360
    upper = sum(row['upper'] for row in bounded)+sum(row['upper'] for row in tails)+mixed+positive7
    if delta == rho == 0:
        require(upper == F(443, 900), 'Exactly the adopted75 H1 face value')
    return {'upper': upper, 'face_upper': F(443, 900), 'excess': upper-F(443, 900),
            'bounded_labels': bounded, 'complete_exponent_tails': tails,
            'deep_mixed_upper': mixed, 'complete_positive7_upper': positive7}


def exact_zero_tail(affine, record, par):
    require(par['delta'] == par['rho'] == 0, 'Exact zero-defect face tail')
    constant, details = F(0), {}
    for t, a in record['coefficients'].items():
        details[t] = {}
        for j, (name, prime, start) in enumerate(zip(affine.FAMILIES, (3, 5, 5, 5), (3, 2, 2, 2))):
            row = affine.punctured_support(prime, start, affine.omissions(name, record['prefix'][t]), start)
            constant += a*par['c'][j]*row['remaining_geometric']
            details[t][name] = row['remaining_geometric']
        constant += a*(F(1, 72)+par['positive7'])
    return {'constant': constant, 'slopes': (F(0),)*4, 'cuts': None, 'complete_geometric_sums': details}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('denominator_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    uniform = module('denominator_uniform', base/'frontier/comparison-bounds/uniform_k_neighborhood_cost.py')
    portfolio = module('denominator_portfolio', base/'frontier/comparison-bounds/uniform_mean_cost_portfolio.py')
    cost = module('denominator_cost', base/'frontier/comparison-bounds/complete_off_face_cost.py')
    pins = {**PINS, **uniform.PINS, **portfolio.PINS, **cost.PINS}
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned complete source '+path)
    finite = module('denominator_finite', base/'frontier/retained-transport/finite_source_face_transport.py')
    affine = module('denominator_affine', base/'frontier/source-budgets/shared_budget_affine_tail.py')
    mean = module('denominator_mean', base/'frontier/retained-transport/joint_deep_mean_transport.py')
    source = module('denominator_source', base/'verify_joint_frontier.py')
    capacity = module('denominator_capacity', base/'frontier/endpoint-bounds/broad_weighted_identity_source.py')
    old = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/moments-survival/whole_block_mean_survival.json'))
    par, zero = uniform.parameters(F(1, 10000), F(1, 100000)), uniform.parameters(F(0), F(0))
    face = cost.face_case(finite, source)
    upper_point, _ = uniform.enlarged_point(face['point'], par)
    qvertices = finite.defect_vertices(par['gap'], par['gap'], par['rho'])
    base_rows = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, par)
    zero_rows = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, zero)
    errors = (par['kbar']*par['rho'], par['rho']+par['delta']/240, par['rho'], par['rho'])
    cuts = tuple(uniform.crossing(p, b, H, e) for p, b, H, e in zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], errors))
    candidates = sorted(set((cuts, (10,)*4, (12,)*4)))
    specifications = [{'name': 'AP11_B'+str(r['block']),
                       'coefficients': {int(t): F(a) for t, a in r['hinge_coefficients'].items()},
                       'weight': F(1, 7), 'face_upper': F(r['joint_mean_upper'])}
                      for r in old['block_results']]
    require(len(specifications) == 4, 'All four original AP11 blocks')
    specifications.append({'name': 'AP13_U4', 'coefficients': {4: F(1)},
                           'weight': F(1, 6), 'face_upper': 6*F(old['standalone_hinge4_penalty'])})
    results = []
    for spec in specifications:
        record = finite.prepare(spec['coefficients'])
        a1 = record['coefficients'].get(1, F(0))
        rows = tuple((layout, a1*reference, tuple(a1*p for p in prices)) for layout, reference, prices in base_rows)
        zrows = tuple((layout, a1*reference, tuple(a1*p for p in prices)) for layout, reference, prices in zero_rows)
        vertices = [uniform.exhaustive_vertex(cost, finite, capacity, record, face, upper_point, par, rows, q)
                    for q in qvertices]
        supports = [uniform.apply_support(record, par, uniform.fixed_tail(affine, record, par, c), vertices)
                    for c in candidates]
        selected = min(supports, key=lambda row: row['upper'])
        zvertex = uniform.exhaustive_vertex(cost, finite, capacity, record, face, face['point'], zero, zrows, (F(0), F(0)))
        zsupport = uniform.apply_support(record, zero, exact_zero_tail(affine, record, zero), [zvertex])
        require(zsupport['upper'] == spec['face_upper'], 'Exact111 zero-radius recovery '+spec['name'])
        require(selected['upper'] >= spec['face_upper'], 'Uniform rectangle contains the face')
        results.append({**spec, 'at_one': F(0), 'exhaustive_vertices': vertices,
                        'candidate_supports': supports, 'selected_support': selected,
                        'zero_vertex': zvertex, 'zero_support': zsupport,
                        'uniform_excess': selected['upper']-spec['face_upper']})
        print(spec['name']+': '+str(float(selected['upper']))+'; zero-radius recovered', flush=True)
    common = portfolio.shared_maximum(results)
    H1, H1zero = uniform_H1(par), uniform_H1(zero)
    tail0, tail1 = F(5, 43923), F(17, 29282)
    tail_H1, tail_S = tail1-4*tail0, tail1-5*tail0
    require((tail_H1, tail_S) == (F(1, 7986), F(1, 87846)), 'Complete remaining AP11 count tail')
    require(F(old['full_count_tail']['remaining_hinge1_coefficient']) == tail_H1
            and F(old['full_count_tail']['whole_constant_coefficient']) == tail_S, 'Original111 count-tail identities')
    mass_coefficient = 1-tail_S/7
    S_lower = F(53, 360)-101*par['delta']/180
    d_lower = mass_coefficient*S_lower-common['upper']-tail_H1*H1['upper']/7
    face_cost = sum(row['weight']*row['face_upper'] for row in results)
    d_face = mass_coefficient*F(53, 360)-face_cost-tail_H1*H1zero['upper']/7
    require(mass_coefficient > 0 and d_lower > 0, 'Correct mass direction and positive complete denominator')
    require(d_face == F(old['uniform_denominator_lower']) == F(50511415637, 632754738000),
            'Exact111 denominator at zero radius, including all infinite tails')
    count = sum(v['original_head_evaluations'] for r in results for v in r['exhaustive_vertices'])
    zcount = sum(r['zero_vertex']['original_head_evaluations'] for r in results)
    checks = sum(v['rational_comparisons'] for r in results for v in r['exhaustive_vertices'])
    zchecks = sum(r['zero_vertex']['rational_comparisons'] for r in results)
    require((count, zcount, checks, zchecks) == (1875000, 625000, 60, 20), 'Every head and zero-radius recovery')
    return uniform.encode({'schema': 'erdos7-uniform-ap-survival-denominator-v1', 'source_sha256': pins,
                           'parameters': par, 'coordinates': uniform.COORDINATES, 'fixed_cut_candidates': candidates,
                           'cost_results': results, 'shared_finite_cost': common, 'H1': H1, 'zero_H1': H1zero,
                           'full_count_tail': {'probability': tail0, 'first_moment': tail1,
                                               'remaining_H1_coefficient': tail_H1, 'remaining_S_coefficient': tail_S},
                           'S_lower': S_lower, 'combined_mass_coefficient': mass_coefficient,
                           'uniform_denominator_lower': d_lower, 'zero_denominator_lower': d_face,
                           'uniform_denominator_loss': d_face-d_lower, 'positive_head_evaluations': count,
                           'zero_head_evaluations': zcount, 'rational_comparisons': checks+zchecks,
                           'scope': 'Complete source-uniform AP11/AP13 denominator on134 actual K neighborhood, both orientations and whole beta face. Four AP11 blocks, separate AP13 U4, all count and exponent tails retained. Five costs share one q and one residual coordinate. H1 transports75 adopted label caps. Exact111 denominator recovered at zero radius. Ordinary proof plus rational verification; no Lean, full numerator, global K or unrestricted Erdos7 claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('denominator_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact uniform denominator certificate')
    print('PASS: complete uniform denominator '+result['uniform_denominator_lower'])
    print('H1 upper '+result['H1']['upper'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
