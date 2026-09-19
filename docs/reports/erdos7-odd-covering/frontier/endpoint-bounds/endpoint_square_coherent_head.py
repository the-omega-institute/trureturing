#!/usr/bin/env python3
"""Exact six-label coherence refinement of the full endpoint square bound.

All12500 shallow layouts have matching primal and feasible dual values
for the surviving-source relaxation. Both raw-source endpoints are
checked for every layout. Infinite original-seven depths are summed
exactly. Only aggregate results and one maximizing witness are emitted.
Standard library, read-only unless --output is explicitly supplied.
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
    'frontier/endpoint-bounds/endpoint_linear_numerator.py': '646c6dce65185917554f77441c8c9d6373bb20021c1204cce01fd71f9a95e314',
    'certificates/source_norms/endpoint-bounds/endpoint_linear_numerator.json': 'c6d20392e71b3fb73b87d40b390b02fe50e9b92bd3245831bfa4d0b96e4875be',
    'frontier/endpoint-bounds/endpoint_square_numerator.py': '5973de37d2d74e2ddb7783baa514709e236f9a894000ca79ec8d66db79174235',
    'certificates/source_norms/endpoint-bounds/endpoint_square_numerator.json': 'a3cb0072765f1e10ce4642f1d46b1bd49ab71de339941a4065938ab59e7fcbea',
}
SCALE = 1800
HEAD = ((0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (2, 1))
LAYOUT_FIELDS = ('root3', 'cell9', 'slot5', 'root15', 'slot15', 'cell45', 'slot45')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(base, relative, name):
    path = base/relative
    require(sha256(path.read_bytes()).hexdigest() == PINS[relative], 'Pinned source: '+relative)
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned source')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def scaled(value):
    result = value*SCALE
    require(result.denominator == 1, 'Exact integral scaling for every source capacity')
    return int(result)


def coefficients(layout, roots):
    root3, cell9, slot5, root15, slot15, cell45, slot45 = layout
    result = []
    for cell, slot in product(range(5), repeat=2):
        value = (1+int(roots[cell] == root3)+int(cell == cell9)+int(slot == slot5)
                 +int(roots[cell] == root15 and slot == slot15)
                 +int(cell == cell45 and slot == slot45))
        result.append(value*value)
    return result


def primal_dual(coefficients, entry_caps, row_caps, mass_cap):
    """Greedy candidate followed by a separately checked feasible LP dual."""
    allocation = [0]*25
    remaining_rows, remaining = row_caps.copy(), mass_cap
    last_row, gamma = [0]*5, 0
    for i in sorted(range(25), key=lambda i: (-coefficients[i], i)):
        row = i//5
        take = min(entry_caps[i], remaining_rows[row], remaining)
        allocation[i] = take
        remaining_rows[row] -= take
        remaining -= take
        if take:
            last_row[row], gamma = coefficients[i], coefficients[i]
        if remaining == 0:
            break
    if remaining:
        gamma = 0
    beta = [max(0, last_row[row]-gamma) if remaining_rows[row] == 0 else 0 for row in range(5)]
    alpha = [max(0, coefficients[i]-gamma-beta[i//5]) for i in range(25)]
    require(gamma >= 0 and min(beta+alpha) >= 0, 'Nonnegative LP dual multipliers')
    require(all(gamma+beta[i//5]+alpha[i] >= coefficients[i] for i in range(25)),
            'Every dual inequality is feasible')
    require(all(0 <= allocation[i] <= entry_caps[i] for i in range(25))
            and all(sum(allocation[5*row:5*row+5]) <= row_caps[row] for row in range(5))
            and sum(allocation) <= mass_cap, 'Every primal capacity is feasible')
    primal = sum(c*x for c, x in zip(coefficients, allocation))
    dual = gamma*mass_cap+sum(b*r for b, r in zip(beta, row_caps))+sum(a*u for a, u in zip(alpha, entry_caps))
    require(primal == dual, 'Primal equals a separately feasible dual for this layout')
    return {'scaled_value': primal, 'allocation': allocation, 'gamma': gamma, 'beta': beta, 'alpha': alpha}


def layout_bounds(linear):
    tables = linear.endpoint_tables()
    endpoints = [linear.slot_matrices(x) for x in linear.LATE_INTERVAL]
    entry_caps = [scaled(max(endpoint[1][cell][slot] for endpoint in endpoints))
                  for cell, slot in product(range(5), repeat=2)]
    raw = [[scaled(endpoint[0][cell][slot]) for cell, slot in product(range(5), repeat=2)] for endpoint in endpoints]
    row_caps = [scaled(value) for value in tables['all_positive5_cell_caps']]
    mass_cap = scaled(tables['surviving_mass'])
    zero_best, raw_best = -1, -1
    zero_maximizers, raw_maximizers = [], []
    zero_witness = None
    zero_digest, raw_digest = sha256(), sha256()
    layouts = raw_checks = 0
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        square = coefficients(layout, linear.ROOT)
        cost = [c-1 for c in square]
        require(min(cost) >= 0, 'The unit-subtracted head-square is nonnegative')
        witness = primal_dual(cost, entry_caps, row_caps, mass_cap)
        val = witness['scaled_value']
        zero_digest.update(json.dumps([layout, witness], separators=(',', ':'), sort_keys=True).encode())
        if val > zero_best:
            zero_best, zero_maximizers, zero_witness = val, [layout], witness
        elif val == zero_best:
            zero_maximizers.append(layout)
        for endpoint, source in enumerate(raw):
            raw_value = sum(c*w for c, w in zip(square, source))
            raw_digest.update(json.dumps([layout, endpoint, raw_value], separators=(',', ':')).encode())
            if raw_value > raw_best:
                raw_best, raw_maximizers = raw_value, [(layout, endpoint)]
            elif raw_value == raw_best:
                raw_maximizers.append((layout, endpoint))
            raw_checks += 1
        layouts += 1
    require(layouts == 12500 and raw_checks == 25000, 'Every independent original shallow residue layout')
    zero_bound, raw_bound = F(zero_best, SCALE), F(raw_best, SCALE)
    require(zero_bound == F(467, 360) and raw_bound == F(769, 360), 'Exact coherent head-block maxima')
    require(zero_maximizers == [(1, 4, 2, 1, 2, 4, 2)]
            and raw_maximizers == [((1, 4, 4, 1, 4, 4, 4), 0), ((1, 4, 4, 1, 4, 4, 4), 1)],
            'Full maximizing-layout inventory')
    return {'layout_fields': LAYOUT_FIELDS, 'slot_names': linear.SLOTS, 'integer_scale': SCALE,
            'entry_caps': [F(v, SCALE) for v in entry_caps], 'row_caps': [F(v, SCALE) for v in row_caps],
            'total_mass_cap': F(mass_cap, SCALE), 'layout_count': layouts,
            'primal_feasible_dual_equality_checks': layouts, 'raw_endpoint_checks': raw_checks,
            'zero7_nonconstant_head_bound': zero_bound, 'raw35_head_bound': raw_bound,
            'zero7_maximizers': zero_maximizers, 'raw35_maximizers': raw_maximizers,
            'one_zero7_maximizing_witness': zero_witness,
            'all_primal_dual_sha256': zero_digest.hexdigest(), 'all_raw_endpoint_values_sha256': raw_digest.hexdigest()}


def calculate(base):
    for relative, pin in PINS.items():
        require(sha256((base/relative).read_bytes()).hexdigest() == pin, 'Current dependency hash: '+relative)
    linear = load(base, 'frontier/endpoint-bounds/endpoint_linear_numerator.py', 'coherent_head_linear')
    square = load(base, 'frontier/endpoint-bounds/endpoint_square_numerator.py', 'coherent_head_square')
    old_linear = json.loads((base/'certificates/source_norms/endpoint-bounds/endpoint_linear_numerator.json').read_text())
    old_square = json.loads((base/'certificates/source_norms/endpoint-bounds/endpoint_square_numerator.json').read_text())
    require(linear.encode(linear.endpoint_tables()) == old_linear['endpoint'], 'Inherited59 cap and geometry reconstruction')
    require(square.encode(square.complete_sums()) == old_square['complete_pair_sums'], 'Inherited62 full square and complete tails')
    bounds = layout_bounds(linear)
    zero_old = sum(square.surviving35_cap(max(a, c), max(b, d))
                   for a, b in HEAD for c, d in HEAD)-F(3, 20)
    raw_old = sum(square.raw35_cap(max(a, c), max(b, d)) for a, b in HEAD for c, d in HEAD)
    require(zero_old == F(2443, 1800) and raw_old == F(91, 40), 'Exactly the old ordered head-pair budgets')
    zero_gain = zero_old-bounds['zero7_nonconstant_head_bound']
    seven_factor = F(6, 5)*square.geometric_weight(7, 1)
    positive_gain = seven_factor*(raw_old-bounds['raw35_head_bound'])
    require(zero_gain == F(3, 50) and seven_factor == F(2, 3) and positive_gain == F(5, 54),
            'Disjoint zero7 and complete positive7 gains')
    old_upper = F(old_square['complete_pair_sums']['full_square_upper'])
    new_upper = old_upper-zero_gain-positive_gain
    margin = 45*F(3, 20)-new_upper
    old_margin = F(old_square['old_square_margin'])
    require(new_upper == F(2653, 540) and margin == F(248, 135)
            and margin-old_margin == F(7207, 19440), 'Absolute full-square and signed-margin improvements')
    tail_checks = []
    for cut in (1, 3, 7):
        finite = sum(F(6, 5*7**max(e, f)) for e, f in product(range(cut+1), repeat=2) if max(e, f) > 0)
        remaining = F(6, 5)*square.geometric_weight(7, cut+1)
        require(finite+remaining == seven_factor, 'Same-depth, cross-depth and infinite positive-seven tail counted once')
        tail_checks.append({'cut': cut, 'finite_ordered_pair_factor': finite, 'complete_tail_factor': remaining})
    return {'schema': 'erdos7-endpoint-square-coherent-head-v1', 'source_vertex': 404, 'carrier': [0, 1],
            'source_sha256': PINS, 'head_original_moduli': [1, 3, 9, 5, 15, 45],
            'head_ordered_pairs': 36, 'zero7_replaced_nonunit_pairs': 35,
            'layout_bounds': bounds, 'old_zero7_head_budget': zero_old, 'old_raw35_head_budget': raw_old,
            'zero7_gain': zero_gain, 'positive7_pair_factor': seven_factor, 'positive7_gain': positive_gain,
            'positive7_tail_checks': tail_checks, 'preceding_full_square_upper': old_upper,
            'full_square_upper': new_upper, 'improvement_over62': zero_gain+positive_gain,
            'barrier': F(45), 'absolute_square_margin': margin, 'old49_square_margin': old_margin,
            'margin_improvement_over49': margin-old_margin,
            'scope': ('Ordinary uniform endpoint and approaching-sequence theorem for all independently '
                      'labelled original357 tests. Complete tails are inherited from62 and the '
                      'positive-seven ordered depth pairs are summed explicitly. Exact shallow '
                      'source relaxations do not assert an attainable full-square extremizer. '
                      'No quantitative neighborhood, global K replacement or Lean result is claimed.')}


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
        certificate = args.base/'certificates/source_norms/endpoint-bounds/endpoint_square_coherent_head.json'
        require(json.loads(certificate.read_text()) == result, 'Exact canonical certificate reconstruction')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS:12500 primal/dual equalities,25000 source endpoint evaluations,complete positive-seven tail.')
    print('Uniform endpoint square2653/540; absolute margin248/135; gain over62 is103/675.')


if __name__ == '__main__':
    main()
