#!/usr/bin/env python3
"""Exact shared-support deficit credit for one depth-two star profile.

All 546 disjoint pairs and all 100 color choices on each pair are evaluated.
The complete first-query tail uses its full mean, without a height cutoff.
The mathematical source/comparator arguments are in Report790; no Lean claim.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json
import runpy


def need(condition, message):
    if not condition:
        raise ValueError(message)


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))


PRIMES = (5, 7, 11, 13, 17, 19, 23)
LAYOUT = ((1, 3), (0, 0), (0, 1), (0, 4), (0, 2), (0, 2), (1, 4))
WEIGHTS = (F(6375, 23726),)*2 + (F(5488, 35589),)*3


def source_credit():
    n = len(PRIMES)
    need(sum(WEIGHTS) == 1, 'one common leaf probability')
    b = tuple(F(1, p-2) for p in PRIMES)
    m = tuple(tuple(1-b[i]*(int((l >= 2) == bool(r))+int(l == t))
                    for l in range(5)) for i, (r, t) in enumerate(LAYOUT))
    need(all(x > 0 for row in m for x in row), 'positive restricted star masses')
    colors = tuple(tuple(1+int((l >= 2) == bool(r))+int(l == t) for l in range(5))
                   for r in range(2) for t in range(5))
    need(len(set(colors)) == 10, 'ten distinct completed colors')
    supports = tuple(s for s in range(1 << n) if s.bit_count() >= 2)
    coeff = {s: tuple(WEIGHTS[l]*prod(m[i][l] for i in range(n) if not s >> i & 1)
                     for l in range(5)) for s in range(1 << n)}
    budget = {s: prod(b[i] for i in range(n) if s >> i & 1) for s in range(1 << n)}
    pairs = tuple((s, t) for s, t in combinations(supports, 2) if s & t == 0)
    triples = tuple((s, t, u) for s, t, u in combinations(supports, 3)
                    if s & t == s & u == t & u == 0)
    degree = Counter(s for pair in pairs for s in pair)
    need((len(supports), len(pairs), len(triples)) == (120, 546, 210),
         'complete support, pair and triple inventories')
    for s in supports:
        need(degree[s] == 2**(n-s.bit_count())-1-(n-s.bit_count()), 'endpoint degree')
        if degree[s]:
            need(sum(F(1, degree[s]) for pair in pairs if s in pair) == 1,
                 'each positive-degree first deficit is spent exactly once')
    zero_degree = tuple(s for s in supports if not degree[s])
    need(len(zero_degree) == 8, 'isolated deficits discarded without dividing by zero')
    single = {s: tuple(dot(coeff[s], c) for c in colors) for s in supports}
    first_max = {s: max(single[s]) for s in supports}
    pair_products = tuple(tuple(c[l]*d[l] for l in range(5))
                          for c, d in product(colors, repeat=2))
    triple_products = tuple(sorted(set(tuple(c[l]*d[l]*e[l] for l in range(5))
                                      for c, d, e in product(colors, repeat=3))))
    pair_counts = Counter(s | t for s, t in pairs)
    triple_counts = Counter(s | t | u for s, t, u in triples)
    pair_values = {s: tuple(dot(coeff[s], c) for c in pair_products) for s in pair_counts}
    pair_min = {s: min(v) for s, v in pair_values.items()}
    triple_max = {s: max(dot(coeff[s], c) for c in triple_products) for s in triple_counts}
    terms = (sum(coeff[0]), sum(budget[s]*first_max[s] for s in supports),
             sum(count*budget[s]*pair_min[s] for s, count in pair_counts.items()),
             sum(count*budget[s]*triple_max[s] for s, count in triple_counts.items()))
    baseline = terms[0]-terms[1]+terms[2]-terms[3]
    need(baseline == F(14490465233, 566019912150), 'separate-extrema baseline')
    rows = []
    for s, t in pairs:
        values = tuple(budget[s]*(first_max[s]-single[s][i])/degree[s]
                       + budget[t]*(first_max[t]-single[t][j])/degree[t]
                       + budget[s | t]*(pair_values[s | t][10*i+j]-pair_min[s | t])
                       for i in range(10) for j in range(10))
        best = min(values)
        need(best >= 0, 'nonnegative local credit')
        index = values.index(best)
        rows.append([s, t, degree[s], degree[t], index//10, index % 10, best])
    credit = sum((row[-1] for row in rows), F(0))
    need(credit == F(354546550427, 80940847437450), 'complete exact deficit credit')
    need(sum(row[-1] > 0 for row in rows) == 538, 'positive edge count')
    source_mass = baseline+credit
    need(source_mass == F(134815726597, 4496713746525), 'corrected source mass')
    complement = tuple(F(1, q-4) for q in PRIMES if q != 5)
    base_cap = 3*(prod(1+x for x in complement)-1-sum(complement))
    need(base_cap == F(184697, 233415) < 1, 'one-clique base Shearer permission')
    return dict(primes=PRIMES, layout=LAYOUT, weights=WEIGHTS, star_masses=m,
                colors=colors, baseline_terms=terms, baseline=baseline,
                pair_credit=credit, source_mass_lower=source_mass,
                support_count=len(supports), pair_count=len(pairs), triple_count=len(triples),
                zero_degree_supports=zero_degree, positive_edges=538,
                base_cap=base_cap,
                edge_columns=('D_mask', 'E_mask', 'deg_D', 'deg_E', 'color_D', 'color_E', 'credit'),
                edges=rows)


def complete_queries(source):
    r = max(sum(WEIGHTS[:2]), sum(WEIGHTS[2:]))
    v = max(WEIGHTS)
    threshold = 18
    atoms = {1: 1-r, 2: r-v}
    atoms.update((k, 2*v/F(3**(k-2))) for k in range(3, threshold))
    for q in PRIMES:
        cap = F(q-1, q-2)
        law = {1: 1-cap/q}
        law.update((k, cap*F(q-1, q**k)) for k in range(2, threshold))
        atoms = {n: sum((a*law[n//k] for k, a in atoms.items()
                         if n % k == 0 and n//k in law), F(0))
                 for n in range(1, threshold)}
    mean = (1+r+F(3, 2)*v)*prod(F(q-1, q-2) for q in PRIMES)
    hinge = mean-threshold+sum((threshold-n)*a for n, a in atoms.items())
    baseline, mass = source['baseline'], source['source_mass_lower']
    old_score, score = 10*baseline-hinge, 10*mass-hinge
    bound = threshold+hinge/mass
    need(old_score < 0 < score and bound < 28, 'credit crosses complete-query threshold28')
    return dict(root_cap=r, leaf_cap=v, threshold=threshold, mean=mean,
                subthreshold_atoms=atoms, hinge=hinge, old_score=old_score, score=score,
                complete_first_upper=bound, complete_first_decimal=float(bound))


def calculate():
    source = source_credit()
    query = complete_queries(source)
    # Reuse the existing local exact quartic and analytic-tail arithmetic.
    helpers = runpy.run_path(str(Path(__file__).with_name('local_ternary_height_lift.py')))
    a4, cutoff_tail = helpers['a4'], helpers['cutoff_tail']
    ternary4 = 1+15*query['root_cap']+216*query['leaf_cap']
    fourth8 = ternary4*prod(1+F(q-1, q-2)*a4(q) for q in PRIMES)/source['source_mass_lower']
    need(fourth8 == F(1068419013913480870613388825227, 89669705971802913792000),
         'normalized same-source old fourth envelope')
    fourth29 = fourth8*(1+F(28, 27)*a4(29))
    need(fourth29 == F(18370854419091495866842584627592421,
                       949064168005562039574528000), 'unnormalized post29 fourth envelope')
    mass29 = (28-query['complete_first_upper'])/27
    tail = cutoff_tail(3000, 7)
    final = mass29-fourth29*tail
    need(final > F(1, 100), 'complete prime tail strictly above3000')
    return dict(status='exact_rational_checks_passed_not_Lean', source=source, query=query,
                old_fourth_upper=fourth8, post29_fourth_upper=fourth29,
                post29_mass_lower=mass29, post29_mass_decimal=float(mass29),
                tail=dict(cutoff=3000, ell=7, delta=F(2, 7), growth=21, factor=tail),
                final_mass_lower=final, final_mass_decimal=float(final), simple_lower=F(1, 100),
                scope='Specified completed old-star profile on3,5,7,11,13,17,19,23 with old v3<=2; arbitrary29 originals and finite prime tail strictly above3000. No other support primes31..3000.',
                analytic_input='Report734 complete quartic tail and its attributed prime-product premise',
                proof_boundary='One-clique source validity, exact submeasure completion, shared-allocation deficit inequality and arbitrary-phase query comparison are ordinary mathematical arguments.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(), default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        need(result == json.loads(Path(__file__).with_suffix('.json').read_text()),
             'fresh shared-deficit result equals retained exact data')
    print(json.dumps(dict(source_mass=result['source']['source_mass_lower'],
                          pair_credit=result['source']['pair_credit'],
                          query_upper=result['query']['complete_first_decimal'],
                          final_mass=result['final_mass_decimal']), indent=2))
