#!/usr/bin/env python3
"""Exact adaptive enclosure of a three-unary-cubic/four-query-square envelope."""
from fractions import Fraction as F
from itertools import product
from collections import Counter
from pathlib import Path
from math import prod
import json
import runpy
from hashlib import sha256


DEPENDENCIES = {
    'fibre_credit_depth_two_uniform_shallow.py':
        '1f01fb1c704a48fddb7f0be9563635cbb4ea436ce1495d2e156fdfc3c0788de6',
    'fibre_credit_depth_two_uniform_shallow.json':
        'afc7b9a8167cf22e67885e427c865c5daa844eb3664b6ff7b684be56e3168591',
}


def replay_source():
    directory = Path(__file__).resolve().parent
    for filename, expected in DEPENDENCIES.items():
        if sha256((directory / filename).read_bytes()).hexdigest() != expected:
            raise RuntimeError('pinned same-source dependency: ' + filename)
    module = runpy.run_path(str(directory / 'fibre_credit_depth_two_uniform_shallow.py'))
    result = json.loads(json.dumps(module['calculate']()))
    retained = json.loads((directory / 'fibre_credit_depth_two_uniform_shallow.json').read_text())
    if result != retained:
        raise RuntimeError('replayed common carrier differs from retained result')
    return result


def calculate():
    source = replay_source()
    TARGET = 19000
    MAX_DEPTH = 12
    MAX_NODES = 3000000
    visits = Counter()
    leaves = Counter()
    failures = []
    nodes = 0


    def need(ok, message):
        if not ok:
            raise RuntimeError(message)


    def lower_at(a, b, c, d):
        u, v, w = 28*d-a, 30*d-b, 36*d-c
        n = (u-1)*(v-1)*(w-1)
        m = u*u+v*v+w*w+d*d
        cubes = a*a*a+b*b*b+c*c*c
        if 2*n <= 3*m*d:
            return m*d*cubes+n*n, m*d**4, 'quadratic'
        return 4*cubes+12*n-9*m*d, 4*d**3, 'linear'


    stack = [(a, b, c, 1, 0) for a in range(1, 28)
             for b in range(1, 30) for c in range(1, 36)]
    while stack:
        a, b, c, d, depth = stack.pop()
        nodes += 1
        visits[depth] += 1
        num, den, regime = lower_at(a, b, c, d)
        if num >= TARGET * den:
            leaves[depth] += 1
            continue
        if depth == MAX_DEPTH or nodes >= MAX_NODES:
            failures.append({'cell': [a, b, c, d], 'depth': depth,
                             'lower': str(F(num, den)), 'regime': regime})
            break
        stack.extend((2*a+i, 2*b+j, 2*c+k, 2*d, depth+1)
                     for i, j, k in product((0, 1), repeat=3))

    need(not failures and not stack, 'complete dyadic cover is certified')
    need(sum((F(count, 2**(3*depth)) for depth, count in leaves.items()), F(0)) == 27*29*35,
         'accepted leaf volumes exactly fill the original closed rectangle')
    refinements = sum(visits.values()) - sum(leaves.values())
    need(nodes == 27*29*35 + 8*refinements,
         'every refined cube was replaced by all eight children')
    need(28**3+1+1 == 21954 > TARGET, 'outside the relevant rectangle unary cubes suffice')

    # Existing same-law increasing-convex comparator from head-profile Report1.
    # This rechecks its distribution arithmetic, not its inherited universal proof.
    atoms = {1: F(581, 6966), 2: F(3031, 6966), 3: F(146, 1053),
             4: F(425, 2106), 5: F(10, 1443), 6: F(45, 481),
             8: F(1, 37), 12: F(1, 74)}
    need(all(p > 0 for p in atoms.values()) and sum(atoms.values()) == 1,
         'inherited comparator is one probability law')
    raw_cube = sum((p*x**3 for x, p in atoms.items()), F(0))
    B = (11, 13, 17, 19, 23)
    P = prod(q-1 for q in B)
    Q = prod(B)
    single = sum(P//(q-1) for q in B)
    multi = Q-P-single
    c1 = (F(185, 86), F(178, 85), F(178, 85), F(2), F(157, 77), F(157, 77))
    square = (F(1091, 82), F(1103, 85), F(1103, 85), F(965, 76), F(993, 77), F(993, 77))
    deltas = tuple((F(P-multi)-(single+multi)*c)/P for c in c1)
    lift2 = prod(1+F(3, q-1) for q in B)
    lift3 = prod(1+F(7, q-1) for q in B)
    G2 = max(g*lift2/delta for g, delta in zip(square, deltas))
    G3 = max(raw_cube*lift3/delta for delta in deltas)
    need(raw_cube == F(87660407, 1116882) and lift3 == F(1077205, 152064),
         'raw cubic moment and pure-product cubic multiplier')
    need(min(deltas) == F(1243487, 13077504), 'same-carrier relative surviving mass lower')
    need(G2 == F(2607189975, 7283281) and G3 == F(94428228722435, 16149165669),
         'same-law source moment ceilings after joint restriction and normalization')
    need(list(map(str, deltas)) ==
         [row['continuous_gate'] for row in source['complete_shallow_bounds'][1]['shape_bounds']],
         'same six relative mass bounds from the replayed actual carrier')
    need(G2 == max(F(row['Gamma23_upper']) for row in source['square_moment29_extension']['rows']),
         'same complete-query square bounds from the replayed actual carrier')
    need(source['complete_shallow_bounds'][1]['uniform_density_lower_if_positive'] == '104726/6084351',
         'same old Haar lower, not another source')
    budget = 3*G3+4*G2
    EW = (TARGET-budget)/3
    Haar = F(104726, 6084351)*EW/(28*30*36)
    need(budget < TARGET and EW > 0 and Haar > F(1, 200000), 'strict joint cubic/square surplus')
    out = {'target': TARGET, 'dependency_hashes': DEPENDENCIES, 'source_replayed': True, 'pointwise_candidate':
           'A^3+B^3+D^3 + sum_(four pair/triple loads) C_i^2 + 3*W >=19000',
           'processed_nodes': nodes, 'visits_by_depth': dict(visits),
           'accepted_leaves_by_depth': dict(leaves), 'unfinished_cells': len(stack),
           'failures': failures, 'complete': not failures and not stack,
           'scope': 'Ordinary proof and exact integer certificate, not Lean. '
                    'The old core through23 remains shallow (v3<=2 and all other '
                    'core exponents<=1). Three new primes q1>=29,q2>=31,q3>=37 '
                    'have arbitrary finite heights and globally fixed phases.',
           'same_source_cubic_inheritance': {
               'raw_head_comparator_atoms': {str(x): str(p) for x,p in atoms.items()},
               'raw_head_cubic_upper': str(raw_cube), 'pure_product_cubic_multiplier': str(lift3),
               'shape_relative_survivor_mass_lower': list(map(str, deltas)),
               'common_relative_mass_lower': str(min(deltas)),
               'claim': 'The same uniform pruned head law has both square and cubic '
                        'bounds. Pure-product extension, followed by the one actual '
                        'mixed-deletion restriction and normalization, preserves both '
                        'on the same E23. Maxima here choose numerical ceilings, not sources.'},
           'accepted_volume': str(sum((F(count,2**(3*depth)) for depth,count in leaves.items()),F(0))),
           'outside_rectangle_unary_cube_lower': 21954,
           'source_square_upper': str(G2), 'source_cubic_upper': str(G3),
           'total_expected_cost_upper': str(budget), 'mean_W_lower': str(EW),
           'Haar_lower_if_complete': str(Haar)}
    return out


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        if json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) != result:
            raise RuntimeError('retained result disagrees with the complete interval certificate')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
