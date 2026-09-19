#!/usr/bin/env python3
"""One actual K-source collision realizes an unbounded tail/error ratio."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/actual_overlap_tail_obstruction.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
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


def limiting_moments(depth, seven_depth):
    require(isinstance(depth, int) and depth >= 3 and isinstance(seven_depth, int)
            and seven_depth >= 1, 'Original deep3 and positive7 exponents')
    coefficient = F(9, 10*7**seven_depth)
    mass = coefficient/F(3**depth)
    m = depth-2
    return {'depth': depth, 'seven_depth': seven_depth, 'mass': mass,
            'density_coefficient': coefficient, 'first_moment': mass*(m+F(1, 2)),
            'second_moment': mass*(m*m+m+1), 'first_ratio': m+F(1, 2),
            'second_ratio': F(m*m+m+1)}


def finite_collision(constructor, N, depth, seven_depth):
    require(3 <= depth <= N and 1 <= seven_depth <= N, 'Finite original exponent box')
    A, B, C = 3**N, 5**N, 7**N
    all5 = (1 << B)-1
    states = [all5]*A
    before = {}
    for a, b in product(range(N+1), repeat=2):
        if not a+b:
            continue
        aa, ra, bb, rb = constructor.source_label(a, b, 398)
        remove = sum(1 << y for y in range(rb, B, 5**bb))
        for x in range(ra, A, 3**aa):
            states[x] &= all5 ^ remove
        mod, residue = constructor.crt_label(aa, ra, bb, rb, 0, 0)
        before[mod] = residue
    groups = {j: [0]*A for j in range(1, 6)}
    target = [0]*A
    moved = None
    for a, b in product(range(N+1), repeat=2):
        if not a+b:
            continue
        j, aa, ra, bb, rb = constructor.mixed_label(a, b)
        mask = sum(1 << y for y in range(rb, B, 5**bb))
        for x in range(ra, A, 3**aa):
            require(not groups[j][x] & mask, 'Original within-class old cylinders are disjoint')
            groups[j][x] |= mask
            if (a, b) == (depth, 0):
                target[x] = mask
        for e in range(1, N+1):
            mod, residue = constructor.crt_label(aa, ra, bb, rb, e, j*7**(e-1))
            require(mod not in before, 'Every original odd modulus is distinct')
            before[mod] = residue
            if (a, b, e) == (depth, 0, seven_depth):
                mod2, replacement = constructor.crt_label(aa, ra, bb, rb, e, 7**(e-1))
                require(j == 2 and mod == mod2, 'Only seven class2 changes to class1')
                moved = (mod, residue, replacement)
    seven_occupied = set()
    for e, j in product(range(1, N+1), range(1, 7)):
        points = set(range(j*7**(e-1), C, 7**e))
        require(not points & seven_occupied, 'All original seven classes are disjoint across depth and digit')
        seven_occupied.update(points)
        if j == 6:
            mod, residue = constructor.crt_label(0, 0, 0, 0, e, j*7**(e-1))
            require(mod not in before, 'Pure7 modulus is distinct')
            before[mod] = residue
    require(moved is not None, 'Present moved label')
    after = dict(before)
    after[moved[0]] = moved[2]
    require(len(before) == (N+1)**3-1 and set(before) == set(after)
            and sum(before[m] != after[m] for m in before) == 1
            and all(m > 1 and m % 2 for m in before), 'All original labels remain, with exactly one changed residue')
    # The two seven classes have disjoint supports. OR each class separately.
    before_points = sum((groups[j][x] & states[x]).bit_count()
                        for j in (1, 2) for x in range(A))
    after_points = 0
    for x in range(A):
        require(target[x] & groups[1][x] == target[x], 'New deep3 rectangle is contained in original9 rectangle')
        require(target[x] & groups[2][x] == target[x], 'Old deep3 rectangle is in class2')
        after_points += ((groups[1][x] | target[x]) & states[x]).bit_count()
        after_points += ((groups[2][x] & ~target[x]) & states[x]).bit_count()
    active = [(target[x] & states[x]).bit_count() for x in range(A)]
    require(before_points-after_points == sum(active), 'Exact two-class OR union loses only the old target')
    pure7_mass = F(5, 6)+F(1, 6*C)
    seven_mass = F(1, 7**seven_depth)/pure7_mass
    raw_mass = F(sum(active), A*B)
    five_mass = F(3, 4)+F(1, 4*B)
    require(raw_mass == five_mass/F(3**depth), 'Full C1 ternary section and exact pure5 survivor')
    loss = seven_mass*raw_mass
    point = 3+3**(depth-1)
    tests = []
    load = [0]*A
    for k in range(3, N+1):
        residue = point % (3**k)
        selected = list(range(residue, A, 3**k))
        observed = seven_mass*F(sum(active[x] for x in selected), A*B)
        expected = loss if k <= depth else loss/F(3**(k-depth))
        require(observed == expected, 'Each independent original pure3 test has its exact released mass')
        for x in selected:
            load[x] += 1
        tests.append({'modulus': 3**k, 'residue': residue, 'released_mass': observed})
    first = seven_mass*F(sum(active[x]*load[x] for x in range(A)), A*B)
    second = seven_mass*F(sum(active[x]*load[x]**2 for x in range(A)), A*B)
    m, extra = depth-2, N-depth
    mean_extra = sum((F(1, 3**j) for j in range(1, extra+1)), F(0))
    square_extra = sum((F(2*j-1, 3**j) for j in range(1, extra+1)), F(0))
    require(first == loss*(m+mean_extra) and second == loss*(m*m+2*m*mean_extra+square_extra),
            'Literal first and second load moments agree with independent nested-layer sums')
    return {'height': N, 'depth': depth, 'seven_depth': seven_depth, 'original_moduli': len(before),
            'changed_label': {'modulus': moved[0], 'before': moved[1], 'after': moved[2]},
            'label_digest': sha256(json.dumps({'before': sorted(before.items()), 'after': sorted(after.items())}).encode()).hexdigest(),
            'source_grid': (A, B), 'source_mass': F(sum(v.bit_count() for v in states), A*B),
            'raw_released_points': sum(active), 'normalized_union_loss': loss,
            'capacity_and_source_change': 'none: all old carriers, source labels and seven masses identical',
            'tests': tests, 'first_moment': first, 'second_moment': second,
            'first_ratio': first/loss, 'second_ratio': second/loss,
            'scope': 'Actual finite families. Capacity defects are unchanged, not zero. Tests have original distinct pure3 labels.'}


def calculate(base):
    for path, pin in PINS.items():
        require(sha256((base/path).read_bytes()).hexdigest() == pin, 'Pinned source '+path)
    constructor = module('actual_overlap_source', base/'frontier/source_mass_compatibility.py')
    exact = []
    for depth, e in product((3, 4, 8, 20), (1, 2)):
        item = limiting_moments(depth, e)
        for last in (depth, depth+1, depth+5):
            coefficient, mass = item['density_coefficient'], item['mass']
            prefix = sum((min(mass, coefficient/F(3**k)) for k in range(3, last+1)), F(0))
            full_tail = coefficient/F(2*3**last)
            require(prefix+full_tail == item['first_moment'], 'Complete min-geometric cap is attained with its whole infinite tail')
        exact.append(item)
    return encode({'schema': 'erdos7-actual-overlap-tail-obstruction-v1', 'source_sha256': PINS,
                   'finite_fixtures': [finite_collision(constructor, *args) for args in ((3, 3, 1), (4, 3, 2), (4, 4, 1), (5, 5, 1))],
                   'complete_limit_moments': exact,
                   'scope': 'Actual one-label overlap witnesses and complete first/second moments. No fixed linear tail/error price, no new global K, no Lean or unrestricted solution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('actual_overlap_io', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact actual-overlap certificate')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: original-label collision, exact finite union differences and complete divergent moment ratios.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
