#!/usr/bin/env python3
"""Joint pure-three moments on complete existing source rectangles."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/pure_three_joint_source_comparison.json'
INPUTS = ('budgeted_coefficient_source_transport', 'fresh_full_slot_source_comparison',
          'wide_fresh_full_slot_source_comparison', 'transported_source_complete_comparison')
ROOT = (0, 0, 1, 1, 1)
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/budgeted_coefficient_source_transport.py': '1bca0f1815cd01872537d91594c610937b1ba127df4717a73c2fe0185541672c', 'certificates/source_norms/budgeted_coefficient_source_transport.json': '03b5c44da39e992145383a855d268788a6cc5946bb5eb00fb26786ad184a4a11', 'frontier/fresh_full_slot_source_comparison.py': 'c3ccb8c17195bbcd6e56d7a4edcfe841ab32551617e13bb0a60b1005dbb8e8a4', 'certificates/source_norms/fresh_full_slot_source_comparison.json': '4404dabd9fe4f30cd50e5878df69b9862c7cb257a2129d6ce22789cc7dc6d334', 'frontier/wide_fresh_full_slot_source_comparison.py': '8b92c7eda87c06ca763d50015b5dd6078730cdb3c7af81aa8a46c989ba3f425d', 'certificates/source_norms/wide_fresh_full_slot_source_comparison.json': '7e8ba6cbd1fa404bf9274cd32e102fa40bf9b7bc7c4ad4c46c2b42b71a61a71a', 'frontier/transported_source_complete_comparison.py': 'f1ae240968de56400d9a49b5220c05291b744d4557fbdd939daec58dda587a4c', 'certificates/source_norms/transported_source_complete_comparison.json': 'b184a3b2ef13033a99df580b5ea081e0251e14c4cfd9ba482ebeb847a7c17200', 'frontier/uniform_shallow_indicator_transport.py': 'bdeacf5b810a3c9d4738752e1b15e0044eaddd0b5e471ff609b61d5f4fd44c1c', 'certificates/source_norms/uniform_shallow_indicator_transport.json': 'edb1a2de1d2662d15eca2d867adf4e1e48c72df984187263be2953dea3260416', 'frontier/whole_quadratic_same_head.py': 'd447341c1887a1be5aae4ce46aa3405f594617929d7c8aa776a4b6032668d7a2', 'certificates/source_norms/whole_quadratic_same_head.json': 'b77b50ff8961dcfafaefdb004b538a1a2409e69944f894048ae25b1ae0bede3a', 'profile-notes/125-the-complete-off-face-omitted-tails-recover-every-face-constant.md': 'cbe1fc88855354bd58e7a11ff22574bd8f9f9f94dceb57612c3ac8b1d943df17', 'profile-notes/134-one-complete-cost-is-uniform-on-a-nonzero-k-neighborhood.md': '34faadac8c86d5ae038a88fa2f70c0eb29bd2400c72881d3032d183182d4a60e', 'profile-notes/152-independent-shallow-indicators-sharpen-the-complete-mean-and-square.md': '97e9f4404693ffd269ec5c9b8e37ca10d721d1a195d5cd7deae43013ba6d1a2f', 'profile-notes/165-the-pure-five-joint-envelope-enters-both-complete-comparisons.md': '871c9dd951bcef3fa9a3130ee7221d22aaf45b5586bdbf06177938f362c95b69', 'profile-notes/171-the-pure-three-path-has-a-joint-complete-moment-bound.md': '40ecf8df6f26cf71b55f0dfc48e4204e9b9d7d2abc3befec4f5df2a0b91dcfbb'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def weighted_error(error, envelope):
    """Exact sum of (2a+1) min(error,envelope*3^-a), over every a>=3."""
    require(error >= 0 and envelope >= 0, 'Nonnegative common excess measure')
    if error == 0 or envelope == 0:
        return {'crossing': None, 'upper': F(0)}
    cut = 3
    while envelope/F(3**cut) > error:
        cut += 1
    require(envelope/F(3**cut) <= error
            and (cut == 3 or envelope/F(3**(cut-1)) > error), 'Exact infinite-tail crossing')
    finite = (cut*cut-9)*error
    infinite = envelope*F(cut+1, 3**(cut-1))
    require(sum(2*a+1 for a in range(3, cut)) == cut*cut-9,
            'The finite part retains every original deepest-exponent multiplicity')
    return {'crossing': cut, 'finite_part': finite, 'infinite_part': infinite,
            'upper': finite+infinite}


def shared_error_maximum(prices, kappa, rho, envelope):
    """Exact three-class simplex maximum, with all infinite geometric knots."""
    require(len(prices) == 9 and min(prices) >= 0 and kappa > 1 and rho >= 0 and envelope > 0,
            'The original nine nonnegative defect coordinates and positive common envelope')
    groups = ((2, 3), (0, 4, 6, 7), (1, 5, 8))
    grouped = (max(F(0), *(prices[i] for i in groups[0])),
               max(prices[i] for i in groups[1]), max(prices[i] for i in groups[2]))
    weights = (F(0), F(1), kappa)
    if rho == 0:
        return {'grouped_prices': grouped, 'weights': weights, 'segments': [], 'upper': F(0)}
    points = tuple((rho*w, rho*p) for w, p in zip(weights, grouped))
    segments = []
    for left, right in ((0, 1), (0, 2), (1, 2)):
        a, pa = points[left]
        b, pb = points[right]
        slope = (pb-pa)/(b-a)
        knots, n, omitted_slope = {a, b}, 3, None
        while True:
            error = envelope/F(3**n)
            if a <= error <= b:
                knots.add(error)
            if a > 0 and error < a:
                break
            if a == 0 and error <= b and n*n-9+slope >= 0:
                omitted_slope = n*n-9+slope
                break
            n += 1
        rows = []
        for error in sorted(knots):
            t = (error-a)/(b-a)
            shallow = (1-t)*pa+t*pb
            tail = weighted_error(error, envelope)
            require(0 <= t <= 1 and shallow == pa+slope*(error-a),
                    'Each candidate has a literal feasible two-class residual allocation')
            rows.append({'error_mass': error, 'right_budget_fraction': t,
                         'shallow_error': shallow, 'complete_deep_error': tail,
                         'upper': shallow+tail['upper']})
        require(a > 0 or omitted_slope is not None and omitted_slope >= 0,
                'Every omitted near-zero segment increases toward a retained knot')
        segments.append({'classes': (left, right), 'source_points': (points[left], points[right]),
                         'slope': slope, 'last_geometric_exponent': n,
                         'omitted_near_zero_slope_lower': omitted_slope,
                         'knots': rows, 'upper': max(r['upper'] for r in rows)})
    return {'grouped_prices': grouped, 'weights': weights, 'segments': segments,
            'upper': max(r['upper'] for r in segments)}


def joint_transport(par, shallow, old_rows):
    delta, rho, kappa = par['delta'], par['rho'], par['kbar']
    require(0 <= delta <= F(1, 18) and rho >= 0 and par['gap'] > 0,
            'Inherited complete first-label guards on the claimed source domain')
    source_upper = (F(3, 4)+delta/4,)*2+(F(1, 2)+delta/2,)*3
    attenuation_upper = (F(1),)+((4+delta)/5,)*4
    caps = tuple(a*d-F(1+r, 20) for a, d, r in zip(attenuation_upper, source_upper, ROOT))
    require(caps == (F(7, 10)+delta/4, F(11, 20)+7*delta/20+delta*delta/20)
            +(F(3, 10)+delta/2+delta*delta/10,)*3 and max(caps) == F(par['c'][0]),
            'Uniform cell references retain the actual OT3 attenuation before taking maxima')
    raw = F(3, 4)+delta/4
    envelope = raw-min(caps)
    require(0 < min(caps) <= max(caps) < raw and kappa == (6-delta)/(3-2*delta),
            'One actual positive excess has the common density envelope and wrong-root price')
    originals = {(row['first_beta'], tuple(row['label'])): row for row in old_rows}
    shallow_rows, candidates = [], []
    for beta in (2, 3, 4):
        indicators = {}
        for label in ([(3, r, None) for r in range(2)]+[(9, j, None) for j in range(5)]):
            row = shallow.one_label_bound(label, beta, par)
            require(encode(row) == originals[beta, label], 'The exact inherited shallow row, including all residual prices')
            source = row['finite_transport']['finite_upper']-row['reference']+row['source_delta_price']*delta
            prices = tuple(row['coordinate_prices'])+(row['q_sum_price']/par['gap'],)*2
            require(source >= 0 and max(prices) == row['shared_residual_price']
                    and source+max(prices)*rho == row['upper'], 'Separate the zero-residual term before maximizing')
            entry = {'first_beta': beta, 'label': label, 'source_upper': source, 'prices': prices}
            shallow_rows.append(entry)
            indicators[label] = entry
        for root, cell in product(range(2), range(5)):
            first, second = indicators[3, root, None], indicators[9, cell, None]
            coefficient = 3+2*int(ROOT[cell] == root)
            counts = tuple(int(ROOT[c] == root)+int(c == cell) for c in range(5))
            deep = tuple(c*(n+2)/9 for c, n in zip(caps, counts))
            prices = tuple(3*a+coefficient*b for a, b in zip(first['prices'], second['prices']))
            shared = shared_error_maximum(prices, kappa, rho, envelope)
            source = 3*first['source_upper']+coefficient*second['source_upper']
            candidates.append({'first_beta': beta, 'first_root': root, 'second_cell': cell,
                               'shallow_source_upper': source, 'deep_Bellman_candidates': deep,
                               'shallow_prices': prices, 'shared_error': shared,
                               'upper': source+max(deep)+shared['upper']})
    upper = max(r['upper'] for r in candidates)
    require(len(shallow_rows) == 21 and len(candidates) == 30, 'Every independent shallow choice and first-beta case')
    return {'source_density_upper': source_upper, 'attenuation_upper': attenuation_upper,
            'cell_reference_caps': caps, 'raw_density_upper': raw, 'common_error_envelope': envelope,
            'shallow_rows': shallow_rows, 'candidate_rows': candidates, 'joint_upper': upper,
            'maximizers': [(r['first_beta'], r['first_root'], r['second_cell'])
                           for r in candidates if r['upper'] == upper]}


def calculate(base):
    require(PINS, 'Pin every complete original rectangle before consumption')
    io = module('joint_three_source_io', base/'certificate_io.py')
    read = lambda n: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(n+'.json')))
    inputs = {name: read(name) for name in INPUTS}
    old_square = read('whole_quadratic_same_head')
    pins = dict(PINS)
    for data in (*inputs.values(), old_square):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    shallow = module('joint_three_source_shallow', base/'frontier/uniform_shallow_indicator_transport.py')
    face_par = shallow.get('uniform_k_neighborhood_cost').parameters(F(0), F(0))
    face_rows = [encode(shallow.one_label_bound(label, beta, face_par))
                 for beta in (2, 3, 4)
                 for label in ([(3, r, None) for r in range(2)]+[(9, j, None) for j in range(5)])]
    face = joint_transport(face_par, shallow, face_rows)
    require(face['joint_upper'] == F(34, 45), 'The joint off-face argument recovers171 exactly')
    cS, cQ = F(old_square['signed_mass_coefficient']), F(old_square['complete_square_weight'])
    mass, cE = F(53, 360), 1-F(1, 614922)
    require(cS < 0 < cQ, 'Retain both complete signed complement coefficients')
    outputs = []
    for name, data in inputs.items():
        par = {k: F(v) if isinstance(v, str) else v for k, v in data['parameters'].items()}
        joint = joint_transport(par, shallow, data['complete_H1']['layout_rows'])
        old, square, heads = data['comparison'], data['complete_square'], data['complete_heads']
        block = (sum(F(r['weighted_upper']) for r in square['bounded_cylinders'] if r['modulus'] in (3, 9))
                 +sum(F(r['upper']) for r in square['complete_weighted_tails'] if r['family'] == 'pure3'))
        saving = block-joint['joint_upper']
        require(saving > 0, 'A strict complete pure-three block improvement on this entire source rectangle')
        indices = ([r['index'] for r in heads['mean_costs']+heads['quadratic_costs']+old['simple_costs']]
                   +[0, 16, 46, 47])
        require(sorted(indices) == old['all_original_indices'] == list(range(52)), 'All52 original independent tests, each once')
        N, denominator, M, offset = (F(old[k]) for k in
            ('signed_endpoint', 'denominator_at_mass_floor', 'mass_coefficient', 'offset'))
        groups = {k: F(v) for k, v in old['cost_groups'].items()}
        require(N == cS*mass+sum(groups.values())
                and denominator == cE*mass-F(heads['denominator_shared']['upper'])-F(data['complete_H1']['upper'])/55902
                and denominator > 0 and offset+N/denominator == F(old['comparison_upper']),
                'Reconstruct the full original signed numerator and complete AP denominator')
        require(groups['square_at_mass_floor'] == cQ*(mass+F(square['full_square_upper'])-F(square['mass_upper'])),
                'The changed square block is present exactly once with its actual unit mass')
        groups['square_at_mass_floor'] -= cQ*saving
        new_N = N-cQ*saving
        target = offset+new_N/denominator
        remaining = (target-offset)*cE-M
        require(new_N == cS*mass+sum(groups.values()) > 0 and remaining > 0
                and 403 < target < F(old['comparison_upper']), 'A full signed comparison for every actual mass, still above403')
        outputs.append({'input': name, 'parameters': data['parameters'], 'joint_pure_three_transport': joint,
                        'old_pure_three_block': block, 'joint_pure_three_block': joint['joint_upper'],
                        'complete_square_saving': saving, 'previous_complete_square_upper': F(square['full_square_upper']),
                        'complete_square_upper': F(square['full_square_upper'])-saving,
                        'retained_pure_five_saving': F(square['joint_square_saving']),
                        'cost_groups': groups, 'all_original_indices': sorted(indices),
                        'signed_mass_coefficient': cS, 'complete_square_weight': cQ,
                        'signed_endpoint': new_N, 'denominator_at_mass_floor': denominator,
                        'mass_coefficient': M, 'remaining_S_coefficient': remaining, 'offset': offset,
                        'comparison_upper': target, 'previous_comparison_upper': F(old['comparison_upper']),
                        'comparison_improvement': F(old['comparison_upper'])-target})
    return encode({'schema': 'erdos7-pure-three-joint-source-comparison-v1', 'source_sha256': pins,
        'defect_coordinates': ('E5-gq5', 'E15-gq15', 'E27', 'Ege4', 'E5deep', 'E15deep', 'omega', 'gq5', 'gq15'),
        'error_weights': ('1', 'kbar', '0', '0', '1', 'kbar', '1', '1', 'kbar'),
        'zero_radius_joint_upper': face['joint_upper'],
        'complete_rectangles': outputs,
        'scope': 'Ordinary actual-source joint pure-three square bounds on four complete existing source rectangles. Both K orientations, whole beta faces, independent original residues at every depth, one common defect simplex and exact infinite tails. Each full consumer retains all52 original costs, pure-five saving, full denominator and positive remaining actual-mass coefficient. No new global target, sharp actual attainment, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('joint_three_source_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete joint pure-three source certificate')
    for row in result['complete_rectangles']:
        print('PASS: '+row['input']+' complete K='+str(float(F(row['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
