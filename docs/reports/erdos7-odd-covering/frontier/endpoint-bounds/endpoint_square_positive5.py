#!/usr/bin/env python3
"""Complete positive-five tails sharpen the common-layout endpoint square.

Exact rational comparisons over all shallow layouts; all exponent tails
are summed analytically. No solver or numerical square root is used.
Read-only unless --output is supplied.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PINS = {
    'frontier/endpoint-bounds/endpoint_square_common_pure3.py': '4d9ff11fde216b78a89cf68b32215366cd77c4fc231d2813552bbf3504c28a09',
    'certificates/source_norms/endpoint-bounds/endpoint_square_common_pure3.json': '295db96a2db87d488b1f401ab2357bcdbecf2925bea1732bbce6ca7cabece184',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def calculate(base):
    for name, pin in PINS.items():
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Pinned dependency: '+name)
    spec = importlib.util.spec_from_file_location('positive5_deep', base/'frontier/endpoint-bounds/endpoint_square_common_pure3.py')
    require(spec is not None and spec.loader is not None, 'Loadable pure3 source')
    deep = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(deep)
    for name, pin in deep.PINS.items():
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Inherited dependency: '+name)
    linear = deep.load(base, 'frontier/endpoint-bounds/endpoint_linear_numerator.py', 'positive5_linear')
    head = deep.load(base, 'frontier/endpoint-bounds/endpoint_square_coherent_head.py', 'positive5_head')
    old = json.loads((base/'certificates/source_norms/endpoint-bounds/endpoint_square_common_pure3.json').read_text())
    ends = [linear.slot_matrices(x) for x in linear.LATE_INTERVAL]
    entry = [head.scaled(max(t[1][c][s] for t in ends)) for c, s in product(range(5), repeat=2)]
    raw = [[head.scaled(t[0][c][s]) for c, s in product(range(5), repeat=2)] for t in ends]
    rows = [head.scaled(v) for v in linear.endpoint_tables()['all_positive5_cell_caps']]
    pre = [[F(0), F(1, 5) if c < 2 else F(0), F(0) if c == 2 else F(1, 5),
            F(3, 20) if c < 2 else F(1, 20) if c == 2 else F(1, 10), F(1, 5)] for c in range(5)]
    multiplier = [[1-F(int(c < 2)+int(c == 1)+int(s == 4)+int(c >= 2 and s == 4), 5)
                   for s in range(5)] for c in range(5)]
    kept = [[pre[c][s]*multiplier[c][s] for s in range(5)] for c in range(5)]
    # Restore all deeper Q losses; retain only forced full-slot deletions.
    # In cell3,Beta use the complete b=1 late family, not total late x.
    eta = list(map(F, ('1/18', '1/9', '1/9', '1/9', '1/9')))
    V = [[(F(0) if s == 0 or (s == 1 and c >= 2) or (s == 2 and c == 2)
           else eta[c]-F(1, 18) if (c, s) == (3, 2) else eta[c])*multiplier[c][s]
          for s in range(5)] for c in range(5)]
    expected = [['0','2/45','2/45','2/45','1/30'], ['0','1/15','1/15','1/15','2/45'],
                ['0','0','0','1/9','1/15'], ['0','0','1/18','1/9','1/15'],
                ['0','0','1/9','1/9','1/15']]
    require(V == [[F(x) for x in row] for row in expected], 'Complete descendant-five table')
    tail_mass, tail_pairs = F(1, 20), F(3, 40)
    require(tail_mass == F(1, 25)/(1-F(1, 5))
            and tail_pairs == tail_mass*(1+2*F(1, 4)), 'Complete b>=2 geometric pair tails')
    old5 = 2*F(16, 9)*tail_mass+2*F(1, 18)*tail_mass+F(4, 9)*tail_pairs
    old15 = 2*F(14, 9)*tail_mass+2*F(1, 18)*tail_mass+F(1, 3)*tail_pairs
    add5 = 2*F(1, 18)*tail_mass+F(4, 9)*tail_pairs
    add15 = 2*F(1, 18)*tail_mass+F(1, 3)*tail_pairs
    require((old5, old15, add5, add15) == (F(13, 60), F(67, 360), F(7, 180), F(11, 360)),
            'Disjoint added-pair budgets with all pure3 and positive5 tails')
    records = []
    primal_digest, tail_digest, prefix_digest = sha256(), sha256(), sha256()
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        coefficients = head.coefficients(layout, linear.ROOT)
        B = list(map(isqrt, coefficients))
        require(all(b*b == c for b, c in zip(B, coefficients)), 'Exact shallow load')
        witness = head.primal_dual([c-1 for c in coefficients], entry, rows, head.scaled(F(3, 20)))
        primal_digest.update(json.dumps([layout, witness], separators=(',', ':'), sort_keys=True).encode())
        zhead = F(witness['scaled_value'], head.SCALE)
        rhead = max(F(sum(w*c for w, c in zip(row, coefficients)), head.SCALE) for row in raw)
        zlines, rlines = deep.tail_lines(B, pre, kept, linear.ROOT)
        ztail, zcut = deep.affine_tail(zlines)
        rtail, rcut = deep.affine_tail(rlines)
        Z, R = zhead+ztail, rhead+rtail
        tail_digest.update(json.dumps(deep.encode([layout, zlines, rlines, zcut, rcut, Z, R]), separators=(',', ':')).encode())
        q5 = max(sum(V[c][s]*B[5*c+s] for c in range(5)) for s in range(5))
        q15 = max(sum(V[c][s]*B[5*c+s] for c in range(5) if linear.ROOT[c] == r)
                  for r in range(2) for s in range(5))
        q45 = max(V[c][s]*B[5*c+s] for c, s in product(range(5), repeat=2))
        prefix_digest.update(json.dumps(deep.encode([layout, q5, q15, q45]), separators=(',', ':')).encode())
        records.append((layout, Z, R, q5, q15, q45))
    require(len(records) == 12500
            and primal_digest.hexdigest() == old['all_primal_dual_sha256']
            and tail_digest.hexdigest() == old['all_affine_tail_bounds_sha256'],
            'Every inherited primal/dual equality and complete pure3 tail reconstructed')
    rstar = max(row[2] for row in records)
    require(rstar == F(old['raw_head_upper']), 'Unchanged raw positive-seven head bound')
    remainder = F(old['unreplaced_pair_remainder'])-old5-old15
    require(remainder == F(109, 90), 'Unreplaced disjoint original-label pairs')
    target = F(114, 25)
    threshold = target-remainder-F(4, 15)*rstar-add5-add15
    require(threshold == F(138187, 52488), 'Rational common-layout threshold')
    check_digest, checks = sha256(), []
    for layout, Z, R, q5, q15, q45 in records:
        gap = threshold-Z-(q5+q15)/10
        slack = (F(5, 2)*gap)**2-R*rstar
        require(gap >= 0 and slack >= 0, 'All-layout square-root bound by rational squaring')
        checks.append((slack, layout))
        check_digest.update(json.dumps(deep.encode([layout, gap, slack]), separators=(',', ':')).encode())
    minimum = min(x[0] for x in checks)
    require(minimum == F(495114037, 9685512225) > 0, 'Strict minimum over all12500 layouts')
    coupled_zero = max(Z+(q5+q15)/10 for _, Z, R, q5, q15, q45 in records)
    require(coupled_zero == F(6856267, 3936600), 'Complete coherent zero-depth prefix maximum')
    require(max(row[-1] for row in records) == F(2, 3), 'No additional9*5^b prefix gain is assumed')
    return deep.encode({
        'schema': 'erdos7-endpoint-square-positive5-v1', 'source_vertex': 404, 'carrier': [0, 1],
        'source_sha256': {**PINS, **deep.PINS}, 'surviving_mass': F(3, 20), 'barrier': 45,
        'descendant5_cell_caps': V, 'tail_mass': tail_mass, 'tail_self_pair_weight': tail_pairs,
        'old_added_pair_budgets': [old5, old15], 'new_added_pair_constants': [add5, add15],
        'coherent_zero_prefix_maximum': coupled_zero, 'raw_expanded_head_upper': rstar,
        'unreplaced_pair_remainder': remainder, 'common_layout_threshold': threshold,
        'layout_checks': len(records), 'minimum_quadratic_slack': minimum,
        'minimum_slack_layouts': [layout for slack, layout in checks if slack == minimum],
        'all_inherited_primal_dual_sha256': primal_digest.hexdigest(),
        'all_inherited_pure3_tails_sha256': tail_digest.hexdigest(),
        'all_positive5_prefix_bounds_sha256': prefix_digest.hexdigest(),
        'all_common_layout_checks_sha256': check_digest.hexdigest(),
        'full_square_upper': target, 'absolute_square_margin': 45*F(3, 20)-target,
        'improvement_over64': F(old['full_square_upper'])-target,
        'scope': 'Uniform actual endpoint square bound; arbitrary independently labelled tests and complete exponent tails. No global K, denominator or Lean claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--output', type=Path)
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    if args.check:
        expected = args.base/'certificates/source_norms/endpoint-bounds/endpoint_square_positive5.json'
        require(json.loads(expected.read_text()) == result, 'Canonical exact certificate')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS:12500 exact layouts, complete pure3/pure5/3*5 tails; endpoint square114/25, margin219/100.')


if __name__ == '__main__':
    main()
