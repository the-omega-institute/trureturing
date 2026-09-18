#!/usr/bin/env python3
"""Retain one original head in all terms of the complete factorial-tail bound.

The uniform factorial-tail bound remains619/720. The layout-dependent
bound can be combined with positive hinge costs before maximizing.
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
CERTIFICATE = 'certificates/source_norms/whole_factorial_same_head.json'
HEAD_SCALE = 5400
PAIR_TAIL_UPPER = F(2539, 3600)
Q_SLOTS = (F(0), F(1, 5), F(1, 5), F(3, 20), F(1, 5))
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/whole_face_second_factorial_tail.py': '10a81457579172e28113d2a1e1646ac4f25ba1161c9fb8e927dcaf74a5928870',
    'certificates/source_norms/whole_face_second_factorial_tail.json': '1cea4dcb2b7344fb48e4064d6d8df7ac38b9add92f732e9513f05a5b7fb66c2c',
    'frontier/k_face_common_seven_hinges.py': '8cc4600c9b3f2f65a11820fcb2d0d6663c765c20765bbaf1ae0de6e883cefc97',
    'frontier/endpoint_k_face_forced27.py': '8e5b5267397b8ca4d9cf0477b9c9074ae9e38e8171f1e4eb05a47595ad1df961',
    'certificates/source_norms/endpoint_k_face_forced27.json': '8f4c5fe37ed46d45c914f21872b2e4d00a2091adf028a0497cdd1817f82f8da0',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


class FactorialHead:
    """Exact upper bound J(layout) for H+C_old+C7, excluding P_TT.

    factorial_head_bound(layout, B=None) returns a Fraction.
    head_bound_numerator(layout, B=None) returns HEAD_SCALE*J(layout).
    Both use the same independent original head labels as MeanHead.
    """
    def __init__(self, bridge):
        self.bridge = bridge
        self.pre, self.raw, self.w, self.descendant = bridge.source_tables(2)
        self.p20 = [[bridge.integer(20*v) for v in row] for row in self.pre]
        self.d18 = [[bridge.integer(18*v) for v in row] for row in self.descendant]
        self.wi = [bridge.integer(5*v) for row in self.w for v in row]
        self.head_caps = [[self.w[c][s]*self.raw[c][s]-(Q_SLOTS[s]/135 if c == 1 else F(0))
                           for s in range(5)] for c in range(5)]
        self.raw_rows = [[6*self.raw[c][s]+self.pre[c][s]/9+3*self.descendant[c][s]/20
                         +F(int(self.descendant[c][s] > 0), 360)
                         for s in range(5)] for c in range(5)]
        self.head_i = [[bridge.integer(HEAD_SCALE*v) for v in row] for row in self.head_caps]
        self.cross_i = [[bridge.integer(HEAD_SCALE*v/5) for v in row] for row in self.raw_rows]
        require(all(0 <= v <= F(4, 225) for row in self.head_caps for v in row),
                'Every actual surviving head-cell cap retains the established uniform bound')
        require(all(0 <= v <= F(7, 40) for row in self.raw_rows for v in row),
                'Every complete fixed-cell raw LCM row retains the established uniform bound')
        require(all((self.pre[c][s] == 0) == (self.descendant[c][s] == 0)
                    == (self.raw_rows[c][s] == 0) for c, s in product(range(5), repeat=2)),
                'Source-excluded rectangles have zero complete raw row')

    def component_numerators(self, layout, B=None):
        require(len(layout) == 7 and all(0 <= v < n for v, n in zip(layout, (2, 5, 5, 2, 5, 5, 5))),
                'One original independent six-head layout')
        r3, c9, s5, r15, s15, c45, s45 = layout
        if B is None:
            B = self.bridge.head_load(layout)
        require(len(B) == 25 and min(B) >= 1 and max(B) <= 6, 'Original six-head load on all source cells')
        z = [weight*max(value-4, 0) for weight, value in zip(self.wi, B)]
        old_terms = (max(sum(self.p20[c][s]*z[5*c+s] for s in range(5)) for c in range(5)),
                     max(sum(self.d18[c][s]*z[5*c+s] for c in range(5)) for s in range(5)),
                     max(sum(self.d18[c][s]*z[5*c+s] for c in range(5) if self.bridge.ROOT[c] == r)
                         for r, s in product(range(2), range(5))),
                     max(self.d18[c][s]*z[5*c+s] for c, s in product(range(5), repeat=2)),
                     5*max(z))
        compatible = r3 == self.bridge.ROOT[c9] == r15 and s5 == s15
        all_compatible = compatible and c45 == c9 and s45 == s5
        head = self.head_i[c9][s5] if all_compatible else 0
        old = 3*sum(old_terms)
        cross = self.cross_i[c45][s45]+(self.cross_i[c9][s5] if compatible else 0)
        return head, old, cross

    def head_bound_numerator(self, layout, B=None):
        return sum(self.component_numerators(layout, B))

    def factorial_head_bound(self, layout, B=None):
        return F(self.head_bound_numerator(layout, B), HEAD_SCALE)


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('same_factorial_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/whole_face_second_factorial_tail.json'))
    forced = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/endpoint_k_face_forced27.json'))
    for data in (previous, forced):
        for path, pin in data['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pin')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited input: '+path)
            used[path] = pin
    bridge = module('same_factorial_bridge', base/'frontier/k_face_common_seven_hinges.py')
    factorial = module('same_factorial_previous', base/'frontier/whole_face_second_factorial_tail.py')
    square = module('same_factorial_square', base/'frontier/k_face_complete_ratio.py')
    problem = FactorialHead(bridge)
    require(bridge.ROOT == (0, 0, 1, 1, 1) and bridge.ETA == (F(1, 18),)+(F(1, 9),)*4,
            'Same actual source and cell labels on the two complete K faces')
    require(F(forced['forced27_cell1_deletion']) == F(1, 180)
            and all(tuple(map(F, row['pure5_complement_in_slots'])) == Q_SLOTS
                    for row in forced['first_beta_slot_tables']), 'Actual forced27 carrier and complete pure5 complement')
    for first in (2, 3, 4):
        moved = bridge.source_tables(first)
        perm = list(range(5)); perm[2], perm[first] = perm[first], perm[2]
        require(all(canonical[c] == other[perm[c]] for canonical, other in
                    zip((problem.pre, problem.raw, problem.w, problem.descendant), moved) for c in range(5))
                and tuple(bridge.ROOT[c] for c in perm) == bridge.ROOT,
                'First-beta permutations transport source, descendant and head data')
    partition = factorial.pair_partition(square)
    require(F(previous['complete_pair_partition']['tail_distinct_pairs']) == partition['tail_distinct_pairs']
            == PAIR_TAIL_UPPER, 'Keep the identical complete distinct-tail-pair series')
    best, count, maxima = -1, 0, [0, 0, 0]
    witnesses, digest = [], sha256()
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        B = bridge.head_load(layout)
        parts = problem.component_numerators(layout, B)
        value = sum(parts)
        r3, c9, s5, r15, s15, c45, s45 = layout
        compatible = r3 == bridge.ROOT[c9] == r15 and s5 == s15
        require(all(max(v-4, 0) <= int(c == c45 and s == s45)
                    +int(compatible and c == c9 and s == s5)
                    for (c, s), v in zip(product(range(5), repeat=2), B)),
                'Every independently labelled head satisfies the two-indicator cross inequality')
        require(all(F(max(v-5, 0)*(v-4), 2) == int(compatible and c9 == c45 and s5 == s45 and c == c9 and s == s5)
                    for (c, s), v in zip(product(range(5), repeat=2), B)),
                'The factorial head event has exactly the retained compatibility conditions')
        maxima = [max(a, b) for a, b in zip(maxima, parts)]
        digest.update(json.dumps([layout, parts], separators=(',', ':')).encode())
        count += 1
        witness = {'layout': layout, 'head': F(parts[0], HEAD_SCALE),
                   'old_tail': F(parts[1], HEAD_SCALE), 'positive7_cross': F(parts[2], HEAD_SCALE)}
        if value > best:
            best, witnesses = value, [witness]
        elif value == best:
            witnesses.append(witness)
    require(count == 12500 and F(best, HEAD_SCALE) == F(139, 900), 'Exact same-layout operator maximum')
    require([w['layout'] for w in witnesses] == [(1, 3, 2, 1, 2, 3, 2), (1, 4, 2, 1, 2, 4, 2)],
            'The only two surviving maximizing layouts')
    require([F(v, HEAD_SCALE) for v in maxima] == [F(4, 225), F(1, 15), F(7, 100)],
            'No separate head bound has been weakened')
    T5 = F(best, HEAD_SCALE)+PAIR_TAIL_UPPER
    require(T5 == F(previous['second_factorial_tail_upper']) == F(619, 720),
            'No independent scalar factorial-tail gain is claimed')
    example = (0, 0, 1, 0, 1, 0, 1)
    require(problem.factorial_head_bound(example) == F(53, 450), 'Strictly smaller compatible root0 objective')
    require(previous['faces'] == [{'vertices': [398, 410, 422], 'carrier': [1, 1]},
                                  {'vertices': [616, 628, 640], 'carrier': [1, 0]}]
            and previous['mass'] == '53/360' and previous['r'] == previous['rho'] == '0',
            'Exactly both complete actual saturated K faces')
    return {'schema': 'erdos7-whole-factorial-same-head-v1', 'source_sha256': used,
            'faces': previous['faces'], 'mass': F(53, 360), 'r': F(0), 'rho': F(0),
            'head_scale': HEAD_SCALE, 'source_pre_table': problem.pre, 'source_upper_table': problem.raw,
            'retained_density': problem.w, 'descendant5_coefficients': problem.descendant,
            'surviving_head_cell_caps': problem.head_caps, 'complete_fixed_cell_raw_rows': problem.raw_rows,
            'layout_count': count, 'all_layout_components_sha256': digest.hexdigest(),
            'separate_component_maxima': [F(v, HEAD_SCALE) for v in maxima],
            'head_operator_maximum': F(best, HEAD_SCALE), 'maximizing_witnesses': witnesses,
            'complete_tail_distinct_pairs': PAIR_TAIL_UPPER, 'second_factorial_tail_upper': T5,
            'independent_scalar_improvement': F(0),
            'compatible_root0_example': {'layout': example, 'head_operator': problem.factorial_head_bound(example)},
            'scope': 'Ordinary exact same-layout factorial-tail bound for both entire actual saturated K faces, all original independent residues and complete exponent tails. The head may be combined with any nonnegative factorial coefficient and same-head hinge bound before maximizing. Its independent scalar maximum remains619/720. No actual optimizer attainment, off-face extension, Lean verification, global K or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('same_factorial_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact same-head factorial-tail certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:12500 independent layouts; fixed-cell complete rows; same-head factorial operator139/900.')
    print('Uniform T5 remains619/720; joint cost consumers may retain the head before maximizing.')


if __name__ == '__main__':
    main()
