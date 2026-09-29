#!/usr/bin/env python3
"""A fixed depth-two profile and an actual-mask box: shared source/query bounds."""
import argparse
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import prod
import json
from pathlib import Path


def need(test, message):
    if not test:
        raise RuntimeError(message)


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))


QS = (5, 7, 11, 13, 17, 19)
ROOTS = ((0, 1), (2, 3, 4))
OWNERS = ((1, 3), (0, 1), (0, 0), (0, 1), (0, 1), (0, 0))
B = [F(1, q-2) for q in QS]
C = [F(q-1, q-2) for q in QS]
P = [C[i]/QS[i] for i in range(6)]
M = [[1-B[i]*(int(l in ROOTS[r])+int(l == s)) for l in range(5)]
     for i, (r, s) in enumerate(OWNERS)]
G = [[prod((M[i][l] for i in range(6) if not mask >> i & 1), start=F(1))
      for mask in range(64)] for l in range(5)]
BS = [prod((B[i] for i in range(6) if mask >> i & 1), start=F(1))
      for mask in range(64)]
CHOICES = [tuple(1+int(l in ROOTS[r])+int(l == s) for l in range(5))
           for r in range(2) for s in range(5)]
PRODUCT_CHOICES = {
    k: sorted(set(tuple(prod(c[l] for c in cc) for l in range(5))
                  for cc in combinations_with_replacement(CHOICES, k)))
    for k in (1, 2, 3)}
PARTS = {(0, 0): 1}
for h in range(1, 7):
    for k in range(1, h//2+1):
        PARTS[h, k] = k*PARTS.get((h-1, k), 0)+(h-1)*PARTS.get((h-2, k-1), 0)


def responses(masses):
    return [[prod((masses[i][l] for i in range(6) if not mask >> i & 1), start=F(1))
             for mask in range(64)] for l in range(5)]


def source_terms(masses=None):
    """G(w)=base dot w + sum_j min_{v in rows[j]} v dot w."""
    gs = G if masses is None else responses(masses)
    rows = []
    for union in range(1, 64):
        for k in range(1, union.bit_count()//2+1):
            scale = (-1)**k*BS[union]*PARTS[union.bit_count(), k]
            rows.append([tuple(scale*gs[l][union]*cc[l] for l in range(5))
                         for cc in PRODUCT_CHOICES[k]])
    return tuple(gs[l][0] for l in range(5)), rows


def source_value(w, masses=None):
    base, rows = source_terms(masses)
    return dot(base, w)+sum((min(dot(row, w) for row in block) for block in rows), F(0))


def query_terms(t, masses=None):
    """H(w,t)=base dot w + sum_j max_{v in rows[j]} v dot w.

    The maxima remain INSIDE the integral: each positive-depth support E
    and each small product load gets its own independent maximum.
    """
    masses = M if masses is None else masses
    base = [F(0)]*5
    rows = []
    for E in range(64):
        a = [prod((masses[i][l]-P[i] for i in range(6) if not E >> i & 1), start=F(1))
             for l in range(5)]
        total = prod((P[i] for i in range(6) if E >> i & 1), start=F(1))
        first = prod((B[i]+P[i] for i in range(6) if E >> i & 1), start=F(1))
        low = {1: F(1)}
        for i, q in enumerate(QS):
            if not E >> i & 1:
                continue
            new = {}
            for old, oldp in low.items():
                for v in range(2, t):
                    if old*v < t:
                        new[old*v] = new.get(old*v, F(0))+oldp*C[i]*F(q-1, q**v)
            low = new
        low = {v: p for v, p in low.items() if v < t}
        tail_mass = total-sum(low.values(), F(0))
        tail_first = first-sum((v*p for v, p in low.items()), F(0))
        need(tail_mass >= 0 and tail_first >= t*tail_mass,
             'complete positive-depth tail accounted for')
        for l in range(5):
            base[l] += (tail_first-t*tail_mass)*a[l]
        if tail_first:
            rows.append([tuple(tail_first*a[l]*int(l in root) for l in range(5))
                         for root in ROOTS])
            rows.append([tuple(tail_first*a[l]*int(l == leaf) for l in range(5))
                         for leaf in range(5)])
        for value, mass in low.items():
            vectors = sorted(set(tuple(mass*a[l]*max(choice[l]*value-t, 0)
                                       for l in range(5)) for choice in CHOICES))
            if any(any(v) for v in vectors):
                rows.append(vectors)
    return tuple(base), rows


def query_value(w, t, masses=None):
    base, rows = query_terms(t, masses)
    return dot(base, w)+sum((max(dot(row, w) for row in block) for block in rows), F(0))


def check_leaf_bridge(masses=None):
    gs = G if masses is None else responses(masses)
    result = []
    for leaf in range(5):
        z = {0: F(1)}
        for mask in range(1, 64):
            bit = mask & -mask
            z[mask] = z[mask ^ bit]-sum(
                (3*BS[d]*gs[leaf][d]/gs[leaf][0]*z[mask ^ d]
                 for d in range(1, mask+1) if d & bit and d & mask == d
                 and d.bit_count() >= 2), F(0))
        minimum = min(v for mask, v in z.items() if mask.bit_count() <= 4)
        if leaf != 3:
            need(minimum > 0, 'valid signed support response on each positive-weight leaf')
        result.append(dict(leaf=leaf, four_coordinate_minimum=str(minimum),
                           six_coordinate_top=str(z[63])))
    return result


def check_weights(w, t, masses=None):
    need(len(w) == 5 and min(w) >= 0 and sum(w) == 1 and w[3] == 0,
         'four-leaf weights in the verified probability domain')
    masses = M if masses is None else masses
    need(all(masses[i][l] >= P[i] for i in range(6) for l in range(5) if w[l] > 0),
         'every positive-weight leaf has nonnegative query zero atoms')
    alpha = source_value(w, masses)
    hinge = query_value(w, t, masses)
    score = (F(615, 49)-t)*alpha-hinge
    return dict(weights=list(map(str, w)), threshold=t, source_lower=str(alpha),
                query_hinge_upper=str(hinge), score=str(score), score_decimal=float(score),
                query_upper=str(t-1+hinge/alpha) if alpha > 0 else None,
                positive=score > 0 and alpha > 0)


def calculate_box():
    epsilon = F(1, 100)
    active = (0, 1, 2, 4)
    w = [F(8, 25), F(3, 10), F(19, 100), F(0), F(19, 100)]
    masses = [[M[i][l] - (epsilon if l in active else 0) for l in range(5)]
              for i in range(6)]
    zero_min = min(masses[i][l] - P[i] for i in range(6) for l in active)
    mass_min = min(masses[i][l] for i in range(6) for l in active)
    need(zero_min == F(39, 100) and mass_min == F(59, 100),
         'positive uniform target masses and query zero atoms')
    bridge = check_leaf_bridge(masses)
    certificate = check_weights(w, 6, masses)
    need(F(certificate['source_lower']) == F(6859178516797877, 75735000000000000),
         'uniform actual-mask box source lower')
    need(F(certificate['query_upper']) < F(45, 4) and
         F(certificate['score']) > F(3, 100), 'uniform strict continuation margin')
    return dict(scope='Every actual star mask bounded by beta_DT+1/100 on the four active leaves; no full-profile claim.',
                active_leaves=active, epsilon=str(epsilon),
                target_masses=[[str(x) for x in row] for row in masses],
                minimum_target_mass=str(mass_min), minimum_query_zero_atom=str(zero_min),
                leaf_probability_bridge=bridge, certificate=certificate,
                thinning_rule='xi[q,l]=(m_star[q,l]/eta_actual[q,l](1))*eta_actual[q,l]')


def calculate():
    bridge = check_leaf_bridge()
    wstar = [F(1, 4), F(1, 4), F(1, 4), F(0), F(1, 4)]
    need(source_value(wstar) == F(37922, 378675), 'new fixed-vertex source response')
    positive_w = [F(8, 25), F(3, 10), F(19, 100), F(0), F(19, 100)]
    positive = check_weights(positive_w, 6)
    need(F(positive['source_lower']) == F(4061237, 37867500), 'positive source mass')
    need(F(positive['query_upper']) < F(21, 2) and F(positive['score']) > F(1, 10),
         'exact positive fixed-profile certificate')
    result = dict(scope='The declared DT comparison vertex and a transported actual-mask box; no claim for all height-two profiles or all weights.',
                  leaf_probability_bridge=bridge,
                  coefficient_choice_counts={k: len(v) for k, v in PRODUCT_CHOICES.items()},
                  wstar=check_weights(wstar, 6), positive=positive, actual_mask_box=calculate_box())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, sort_keys=True, indent=2) + '\n'
    if args.output is None:
        expected = Path(__file__).resolve().with_suffix('.json')
        need(json.loads(expected.read_text()) == result,
             'retained result agrees with exact replay')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
