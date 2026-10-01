#!/usr/bin/env python3
"""Exact small conditional controls for two-cut private-fibre amplification.

Enumerates only the four declared residual grids (15, 75, 45, 225 points).
Original membership and private witnesses use exact CRT on full integers;
the full periods are never enumerated.
"""

import argparse
from fractions import Fraction
import json
from math import gcd, lcm
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def crt(parts):
    result, period = 0, 1
    for residue, modulus in parts:
        require(gcd(period, modulus) == 1, 'CRT moduli not coprime')
        shift = ((residue - result) * pow(period, -1, modulus)) % modulus
        result += period * shift
        period *= modulus
    return result % period


def make_family(H, J):
    p, q, tag = 3, 5, 7
    K = max((p - 1) * (H - 1), (q - 1) * (J - 1))
    M = K + max(p - 1, q - 1)
    family = [dict(residue=0, modulus=p*q, axis='target')]
    for axis, height in ((p, H), (q, J)):
        for n in range(1, height + 1):
            for c in range(1, axis):
                j = K+c if n == 1 else (axis-1)*(n-2)+c
                require(1 <= j <= M, 'invalid tag exponent')
                residue = crt([(c*axis**(n-1), axis**n), (0, tag**j)])
                family.append(dict(residue=residue, modulus=axis**n*tag**j,
                                   axis=axis, n=n, c=c, j=j))
    return family, K, M


def members(family, x):
    return [i for i, item in enumerate(family)
            if x % item['modulus'] == item['residue']]


def grid_profile(family, H, J, M):
    rows = []
    for xp in range(3**H):
        for xq in range(5**J):
            x = crt([(xp, 3**H), (xq, 5**J), (0, 7**M)])
            hit = members(family, x)
            target = 0 in hit
            p_hit = any(family[i]['axis'] == 3 for i in hit)
            q_hit = any(family[i]['axis'] == 5 for i in hit)
            rows.append(dict(x=x, xp=xp, xq=xq, covered=bool(hit),
                             private=hit == [0], target=target,
                             p_hit=p_hit, q_hit=q_hit,
                             rectangle=xp % 3 != 0 and xq % 5 != 0))
    return rows


def run():
    results = []
    total_cells = total_witnesses = 0
    base_family = None
    base_rows = None
    for H, J in ((1, 1), (1, 2), (2, 1), (2, 2)):
        family, K, M = make_family(H, J)
        period = lcm(*(item['modulus'] for item in family))
        require(period == 3**H*5**J*7**M, 'actual original period')
        moduli = [item['modulus'] for item in family]
        require(len(set(moduli)) == len(moduli) == 1+2*H+4*J,
                'numerical distinctness/count')
        require(all(m > 1 and m % 2 for m in moduli), 'odd nonunit originals')
        require(all(m % 15 != 0 for m in moduli[1:]), 'maximal target')
        witnesses = []
        for i, item in enumerate(family):
            if i == 0:
                xp, xq, xtag = 0, 0, 1
            else:
                own = item['c'] * item['axis']**(item['n']-1)
                other = 0 if item['n'] == 1 else 1
                xtag = 0 if item['n'] == 1 else 7**item['j']
                if item['n'] >= 2:
                    require(item['j'] <= K < M, 'private tag separation')
                xp, xq = (own, other) if item['axis'] == 3 else (other, own)
            witness = crt([(xp, 3**H), (xq, 5**J), (xtag, 7**M)])
            require(members(family, witness) == [i], 'actual global private witness')
            witnesses.append(witness)
        require(not members(family, 1), 'global noncoverage witness 1')
        rows = grid_profile(family, H, J, M)
        require(all(row['covered'] for row in rows), 'selected fibre not covered')
        require(all(not row['rectangle'] or row['p_hit'] and row['q_hit']
                    for row in rows), 'pointwise arbitrary-payoff rectangle inclusion')
        cells = len(rows)
        private = Fraction(sum(row['private'] for row in rows), cells)
        cross = Fraction(sum(row['p_hit'] and row['q_hit'] for row in rows), cells)
        rectangle = Fraction(sum(row['rectangle'] for row in rows), cells)
        require(private == Fraction(1, 3**H*5**J), 'actual private mass')
        require(cross == (1-Fraction(1,3**H))*(1-Fraction(1,5**J)),
                'actual cross-union mass')
        require(rectangle == Fraction(8,15), 'actual complementary rectangle')
        avoiding_target = [row for row in rows if not row['target']]
        conditioned_cross = Fraction(sum(row['p_hit'] and row['q_hit']
                                         for row in avoiding_target), len(avoiding_target))
        conditioned_rectangle = Fraction(sum(row['rectangle'] for row in avoiding_target),
                                         len(avoiding_target))
        require(conditioned_cross >= conditioned_rectangle == Fraction(4,7),
                'conditional target-complement bound')
        require(all(not row['target'] for row in avoiding_target), 'zero conditioned target')
        if H == J == 1:
            base_family, base_rows = family, rows
        results.append(dict(H=H, J=J, K=K, M=M, period=period,
                            coarse_modulus=7**M, residual_cells=cells,
                            original_count=len(family), private_witnesses=witnesses,
                            originals=[dict(residue=f['residue'],modulus=f['modulus'])
                                       for f in family],
                            private_mass=str(private), cross_union_mass=str(cross),
                            rectangle_mass=str(rectangle),
                            conditioned_cross_union=str(conditioned_cross),
                            conditioned_rectangle=str(conditioned_rectangle),
                            amplification_ratio=str(rectangle/(8*private))))
        total_cells += cells
        total_witnesses += len(witnesses)
    require(base_family is not None and base_rows is not None, 'missing base fixture')
    removed = [f for f in base_family if not (f['axis'] == 3 and f['c'] == 1)]
    hole_rows = grid_profile(removed, 1, 1, 4)
    require(any(row['private'] for row in hole_rows), 'negative control lost target privacy')
    holes = sum(not row['covered'] for row in hole_rows)
    failures = sum(row['rectangle'] and not(row['p_hit'] and row['q_hit'])
                   for row in hole_rows)
    require(holes == 1 and failures == 4, 'coverage-premise negative control')
    unit_family = [dict(residue=0,modulus=15,axis='target'),
                   dict(residue=0,modulus=7,axis='unit')]
    unit_rows = grid_profile(unit_family, 1, 1, 1)
    unit_has_private = any(row['private'] for row in unit_rows)
    require(all(row['covered'] for row in unit_rows) and not unit_has_private,
            'unit-event control must cover without target privacy')
    require(all(not(row['p_hit'] and row['q_hit']) for row in unit_rows),
            'private-premise negative control')
    further_survivors = [row for row in base_rows if not row['target'] and not row['p_hit']]
    further_cross = Fraction(sum(row['p_hit'] and row['q_hit'] for row in further_survivors),
                             len(further_survivors))
    require(len(further_survivors) == 4 and further_cross == 0,
            'further-deletion source guard')
    return dict(scope='Four fixed conditional grids; no full-period enumeration or all-family computational claim',
                arithmetic='Exact CRT integers and rational probabilities',
                total_main_grid_cells=total_cells, global_private_witnesses=total_witnesses,
                fixtures=results,
                negative_controls=dict(omitted_p_strip_holes=holes,
                                       omitted_p_strip_rectangle_failures=failures,
                                       covered_unit_fibre_has_private_target=unit_has_private,
                                       further_deletion_survivor_count=len(further_survivors),
                                       further_deletion_cross_union_mass=str(further_cross)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    encoded = json.dumps(run(), indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(encoded, encoding='utf-8')
    else:
        print(encoded, end='')
