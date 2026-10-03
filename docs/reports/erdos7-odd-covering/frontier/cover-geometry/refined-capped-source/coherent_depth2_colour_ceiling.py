#!/usr/bin/env python3
"""Exact common-colour witnesses for the un-clipped signed source ceiling.

Evaluates every mixed support, disjoint pair and disjoint triple using one
colour per support. No optimization solver or search certificate is trusted.
This limits one source lower-bound template, not actual survivor measures.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations
from math import prod
from pathlib import Path
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


PRIMES = (5, 7, 11, 13, 17, 19, 23)
COLORS = tuple(tuple(1+int((l >= 2) == bool(r))+int(l == t) for l in range(5))
               for r in range(2) for t in range(5))
SUPPORTS = tuple(s for s in range(128) if s.bit_count() >= 2)
PAIRS = tuple((s, t) for s, t in combinations(SUPPORTS, 2) if not s & t)
TRIPLES = tuple((s, t, u) for s, t, u in combinations(SUPPORTS, 3)
                if s & t == s & u == t & u == 0)


def response(layout, indices):
    need(len(layout) == 7 and all(len(rt) == 2 and rt[0] in (0, 1)
                                  and rt[1] in range(5) for rt in layout), 'star roles')
    need(len(indices) == 120 and all(type(i) is int and i in range(10) for i in indices),
         'one legal colour for each complete mixed support')
    colors = dict(zip(SUPPORTS, (COLORS[i] for i in indices)))
    b = tuple(F(1, p-2) for p in PRIMES)
    mass = tuple(tuple(1-b[i]*(int((l >= 2) == bool(r))+int(l == t))
                       for l in range(5)) for i, (r, t) in enumerate(layout))
    coeff = {s: tuple(prod(b[i] if s >> i & 1 else mass[i][l] for i in range(7))
                      for l in range(5)) for s in range(128)}
    terms = [[coeff[0][l] for l in range(5)]]
    terms.append([sum(coeff[s][l]*colors[s][l] for s in SUPPORTS) for l in range(5)])
    terms.append([sum(coeff[s | t][l]*colors[s][l]*colors[t][l]
                      for s, t in PAIRS) for l in range(5)])
    terms.append([sum(coeff[s | t | u][l]*colors[s][l]*colors[t][l]*colors[u][l]
                      for s, t, u in TRIPLES) for l in range(5)])
    return tuple(terms[0][l]-terms[1][l]+terms[2][l]-terms[3][l] for l in range(5))


def hinge_floor():
    # Root and leaf probability caps of any five-leaf law are >=1/2 and >=1/5.
    r, v = F(1, 2), F(1, 5)
    atoms = {1: 1-r, 2: r-v}
    atoms.update((k, 2*v/F(3**(k-2))) for k in range(3, 28))
    for q in PRIMES:
        cap = F(q-1, q-2)
        law = {1: 1-cap/q}
        law.update((k, cap*F(q-1, q**k)) for k in range(2, 28))
        atoms = {n: sum((a*law[n//k] for k, a in atoms.items()
                         if n % k == 0 and n//k in law), F(0)) for n in range(1, 28)}
    mean = (1+r+F(3, 2)*v)*prod(F(q-1, q-2) for q in PRIMES)
    ratios = [(t, (mean-t+sum((t-n)*a for n, a in atoms.items() if n < t))/(28-t))
              for t in range(28)]
    return dict(threshold_ratios=ratios, minimum_threshold=min(ratios, key=lambda z: z[1])[0],
                required_mass=min(v for _, v in ratios), complete_mean=mean)


def calculate(witness_path):
    data = json.loads(witness_path.read_text())
    need(data['schema'] == 'e7-coherent-depth-two-colours-v1', 'witness schema')
    need(tuple(data['primes']) == PRIMES and len(data['witnesses']) == 2, 'scope and witnesses')
    need((len(SUPPORTS), len(PAIRS), len(TRIPLES)) == (120, 546, 210), 'complete inventory')
    rows = []
    group = tuple(tuple(a)+tuple(b) for a in permutations(range(2)) for b in permutations(range(2, 5)))
    for witness in data['witnesses']:
        layout, indices = witness['layout'], witness['color_indices']
        values = response(layout, indices)
        orbit_values = []
        for perm in group:
            new_layout = [(r, perm[t]) for r, t in layout]
            new_indices = [5*(i//5)+perm[i % 5] for i in indices]
            transformed = response(new_layout, new_indices)
            need(all(transformed[perm[l]] == values[l] for l in range(5)), 'joint relabel equivariance')
            orbit_values.append(transformed)
        averaged = tuple(sum(row[l] for row in orbit_values)/12 for l in range(5))
        need(averaged[0] == averaged[1] and averaged[2] == averaged[3] == averaged[4], 'group average')
        intercept = sum(values[2:])/3
        slope = sum(values[:2])-2*intercept
        rows.append(dict(layout=layout, leaf_responses=values, orbit_average=averaged,
                         slope=slope, intercept=intercept,
                         color_counts=dict(Counter(indices))))
    up, down = rows
    need(up['slope'] > 0 > down['slope'], 'opposing slopes')
    crossing = (down['intercept']-up['intercept'])/(up['slope']-down['slope'])
    ceiling = up['intercept']+crossing*up['slope']
    need(0 < crossing < F(1, 2), 'interior crossing')
    need(crossing == F(237713, 1080931), 'exact crossing')
    need(ceiling == F(11371478021, 781432043175), 'full coherent signed ceiling')
    hinge = hinge_floor()
    need(hinge['minimum_threshold'] == 16 and ceiling < hinge['required_mass'], 'hinge obstruction')
    weights = (crossing, crossing)+((1-2*crossing)/3,)*3
    clipped = [sum(w*max(v, 0) for w, v in zip(weights, row['leaf_responses'])) for row in rows]
    need(all(v > hinge['required_mass'] for v in clipped), 'leafwise clipping is not obstructed')
    return dict(status='exact_common_colour_checks_passed_not_Lean', support_count=120,
                pair_count=546, triple_count=210, witness_orbit_size=12,
                witnesses=rows, crossing=crossing, signed_ceiling=ceiling,
                signed_ceiling_decimal=float(ceiling), hinge=hinge,
                required_mass_decimal=float(hinge['required_mass']),
                clipped_witness_values=clipped, clipped_witness_decimals=list(map(float, clipped)),
                scope='All globally fixed five-leaf weights; uniform lower bounds on the UN-CLIPPED signed response over the completed budget domain. Not an upper bound on actual survivor mass, leafwise-clipped responses, adaptive weights, or exact phase-aware sources.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--witnesses', type=Path,
                        default=Path(__file__).with_name('coherent_depth2_colour_witnesses.json'))
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(args.witnesses), default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        need(result == json.loads(Path(__file__).with_suffix('.json').read_text()), 'retained exact result')
    print(json.dumps({k: result[k] for k in ('signed_ceiling_decimal', 'required_mass_decimal',
                                            'clipped_witness_decimals')}, indent=2))
