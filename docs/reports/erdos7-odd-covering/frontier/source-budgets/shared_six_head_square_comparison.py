#!/usr/bin/env python3
"""One original six-label head controls its square and both complete crosses."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/shared_six_head_square_comparison.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/retained-transport/pure_axis_shared_deletion_comparison.py': '574a5b2b0aa14d7f74c9e81af74af2968f52f7c165f6d659a0360e13f5e561a2', 'certificates/source_norms/retained-transport/pure_axis_shared_deletion_comparison.json': 'e6ac38cc6ed0b541557cf6f21a6134b1890bde12a2461edbdc7f940cbbb9465c', 'frontier/moments-survival/whole_face_second_factorial_tail.py': '106e081ed80b09a176ca63aa382c5486d3a980c34c04617115f764131b84a0cf', 'certificates/source_norms/moments-survival/whole_face_second_factorial_tail.json': '2cf56c20350e698147a3ed004f23bde00990766fe876c18b61e4444f16e99465', 'frontier/moments-survival/whole_factorial_same_head.py': '845768cfb7c67a9683c92e4ecaacee40dfc22d6b7f6c8791b5169917650e5c24', 'frontier/endpoint-bounds/k_face_complete_ratio.py': '00b86477e4f9fc369058ae64f28bcd9f52da726d74e9969854b32b39c652d160', 'frontier/endpoint-bounds/k_face_common_seven_hinges.py': 'c382bed2ef52cc22c624c33f8aa2b1313df3a43935916f985c9c11060433c1e3', 'profile-notes/065-128/128-the-complete-factorial-tail-retains-its-head-off-the-face.md': '79ae5ce60d7121afdc3fe0eaa3a87abecf21709d15e7627c2425dd7bdb4926cc', 'profile-notes/065-128/75-forced27-and-complete-pure3-deletion-on-the-k-faces.md': 'bf21f845032d56fb86f86dfdecd5426e58eceac63a1c4e44d6fe0a16d7070f33'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original source')
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


class SharedSquareHead:
    """All integer outputs use the common denominator5400."""
    def __init__(self, bridge, factorial):
        self.bridge = bridge
        self.table = factorial.FactorialHead(bridge)
        self.cap = [bridge.integer(360*v) for row in self.table.raw for v in row]
        self.bud = [bridge.integer(360*v) for v in bridge.GROUP_MASSES]
        self.wi = [bridge.integer(5*v) for row in self.table.w for v in row]
        self.p, self.d = self.table.p20, self.table.d18
        self.q27 = [bridge.integer(5400*v/135) for v in factorial.Q_SLOTS]
        self.masks = [[tuple(range(25))],
            [tuple(i for i in range(25) if bridge.ROOT[i//5] == r) for r in range(2)],
            [tuple(range(5*c, 5*c+5)) for c in range(5)],
            [tuple(5*c+s for c in range(5)) for s in range(5)],
            [tuple(5*c+s for c in range(5) if bridge.ROOT[c] == r)
             for r, s in product(range(2), range(5))],
            [(i,) for i in range(25)]]
        self.lp_count = 0

    def lp(self, values, mask=None):
        coefficients = values if mask is None else [v if i in mask else 0 for i, v in enumerate(values)]
        self.lp_count += 1
        value, records = self.bridge.lp_bound(coefficients, self.cap, self.bud)
        require(sum(r['value'] for r in records) == value, 'Every same-source LP has matching primal and dual')
        return value

    def tail_terms(self, values):
        p, d = self.p, self.d
        return (max(sum(p[c][s]*values[5*c+s] for s in range(5)) for c in range(5)),
            max(sum(d[c][s]*values[5*c+s] for c in range(5)) for s in range(5)),
            max(sum(d[c][s]*values[5*c+s] for c in range(5) if self.bridge.ROOT[c] == r)
                for r, s in product(range(2), range(5))),
            max(d[c][s]*values[5*c+s] for c, s in product(range(5), repeat=2)),
            5*max(values))

    def components(self, layout):
        B = self.bridge.head_load(layout)
        require(min(B) >= 1 and max(B) <= 6, 'The original six independent head labels')
        square_before = 3*self.lp([w*v*v for w, v in zip(self.wi, B)])
        deletion = sum(q*B[5+s]**2 for s, q in enumerate(self.q27))
        square = square_before-deletion
        old_terms = self.tail_terms([w*v for w, v in zip(self.wi, B)])
        old_cross = 3*sum(old_terms)
        raw_head = [max(self.lp(B, mask) for mask in masks) for masks in self.masks]
        raw_tail = self.tail_terms(B)
        raw_row = 15*(sum(raw_head)+sum(raw_tail))
        require(square >= 0 and min(old_terms+raw_tail) >= 0, 'Nonnegative complete source upper terms')
        return {'head_square_before27': square_before, 'forced27_square_deletion': deletion,
                'head_square': square, 'old_cross': old_cross,
                'raw_row_head_terms': raw_head, 'raw_row_tail_terms': raw_tail,
                'positive7_raw_row': raw_row,
                'combined_numerator_over27000': 5*(square+2*old_cross)+2*raw_row}


def calculate(base):
    require(PINS, 'Pin all direct proof and consumer inputs')
    io = module('six_square_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior, tail_prior = read('pure_axis_shared_deletion_comparison'), read('whole_face_second_factorial_tail')
    pins = dict(PINS)
    for data in (prior, tail_prior):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original dependency '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('six_square_'+name, io.named_artifact(base/'frontier', name+'.py'))
    bridge, factorial = load('k_face_common_seven_hinges'), load('whole_factorial_same_head')
    partition = load('whole_face_second_factorial_tail').pair_partition(load('k_face_complete_ratio'))
    tail = partition['tail_tail_ordered']
    require(tail == F(2977, 1800), 'All old-old, old-seven and seven-seven ordered tail pairs')
    problem = SharedSquareHead(bridge, factorial)
    best, count, witnesses, digest = -1, 0, [], sha256()
    component_maxima = [0, 0, 0]
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        parts = problem.components(layout)
        value = parts['combined_numerator_over27000']
        digest.update(json.dumps([layout, parts], separators=(',', ':')).encode())
        component_maxima = [max(a, parts[k]) for a, k in zip(component_maxima,
                            ('head_square', 'old_cross', 'positive7_raw_row'))]
        count += 1
        if value > best:
            best, witnesses = value, [{'layout': layout, 'components': parts}]
        elif value == best:
            witnesses.append({'layout': layout, 'components': parts})
    require(count == 12500 and best == 78360
            and [w['layout'] for w in witnesses] == [(0, 1, 2, 0, 2, 1, 2)],
            'Exact maximum over every original independent head')
    Q = F(best, 27000)+tail
    oldQ = F(prior['complete_square_upper'])
    require(Q == F(8201, 1800) and oldQ == F(13109, 2700) and oldQ-Q == F(323, 1080),
            'Replace the entire complete square; do not add the earlier pure-axis saving')
    D, L = F(prior['mass']), F(prior['linear_upper'])
    require((D, L) == (F(53, 360), F(1151, 1800)) and prior['r'] == prior['rho'] == '0',
            'Both original saturated whole K faces')
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in engine.pins.items()), 'Complete52 original cost closure')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    require(len(tags) == len(old_costs) == len(weights) == 52 and prior['all_original_indices'] == list(range(52)),
            'Every original cost retained, including174 factorial and191 majorant gains')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda v, tag=t: engine.source.zero5_cost(tag, v) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, old_costs, old_costs, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*oldQ
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    propagated = sum(w*(a-b) for w, a, b in zip(weights, old_costs, costs))
    require(oldN == F(prior['numerator_upper']) and oldN-N == square_weight*(oldQ-Q)+propagated
            and all(0 <= b <= a for a, b in zip(old_costs, costs)) and propagated >= 0 and N > 0,
            'One complete numerator and no duplicate savings')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) == F(50511415637, 632754738000) > 0,
            'Every AP11 block, AP13 loss and complete infinite count tail')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper']) and 403 < comparison < F(prior['comparison_upper']),
            'Strict complete-face improvement, still above403')
    return encode({'schema': 'erdos7-shared-six-head-square-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
        'source_pre': problem.table.pre, 'source_descendant': problem.table.descendant,
        'selected_density_weights': problem.table.w, 'source_caps': problem.table.raw,
        'source_group_budgets': bridge.GROUP_MASSES, 'forced27_deletion_coefficient': F(1, 135),
        'pure_five_complement_in_slots': factorial.Q_SLOTS,
        'head_count': count, 'rational_lp_count': problem.lp_count,
        'all_head_components_sha256': digest.hexdigest(), 'head_maximizing_witnesses': witnesses,
        'combined_head_upper': F(best, 27000),
        'separate_head_component_uppers': dict(zip(('head_square', 'old_cross', 'positive7_raw_row'),
                                                 (F(v, 5400) for v in component_maxima))),
        'complete_tail_partition': partition, 'complete_tail_square_upper': tail,
        'previous_complete_square_upper': oldQ, 'complete_square_upper': Q,
        'complete_square_saving': oldQ-Q, 'all_original_indices': list(range(52)),
        'original_cost_tags': tags, 'cost_weights': weights, 'previous_cost_bounds': old_costs,
        'improved_cost_bounds': costs, 'majorants': majorants,
        'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'direct_numerator_improvement': square_weight*(oldQ-Q), 'majorant_propagation_improvement': propagated,
        'numerator_upper': N, 'AP11_block_results': prior['AP11_block_results'],
        'full_count_tail': prior['full_count_tail'], 'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
        'uniform_denominator_lower': denominator, 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'scope': 'Ordinary complete square and52-cost comparison on both actual saturated K faces. One original six-label head controls B squared and both B-old-tail and B-positive7 crosses before maximization. Every original tail pair and independent label remains. The complete square replaces191 instead of adding its pure-axis saving. No actual-family attainment, off-face/global extension, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('six_square_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact shared-six-head square certificate')
    print('PASS:12500 common heads, complete square<=8201/1800; complete face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
