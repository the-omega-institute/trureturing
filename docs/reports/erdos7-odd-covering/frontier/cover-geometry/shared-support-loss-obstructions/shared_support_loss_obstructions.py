#!/usr/bin/env python3
"""Two actual loss obstructions and a general single-query conditioning bound.

Builds every numerical modulus, fixed CRT residue, and CRT private point.
Computes the SAME pure-product-source union by block inclusion-exclusion.
Does not scan the full period or import any previous producer/results.
Only the standard library is required. No Lean verification is claimed.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import gcd, prod
from pathlib import Path


PRIMES = (3, 5, 7, 11, 13, 17, 19)
TARGET = F(565, 51)
LOSS_TARGET = F(173, 250)
CHECKS = []


def check(name, condition):
    if not condition:
        raise AssertionError(name)
    CHECKS.append(name)


def ratio(value):
    return str(value)


def cylinder(p, digit, depth):
    return digit * p ** (depth - 1) + (p ** (depth - 1) - 1) // (p - 1)


def crt(local):
    modulus = prod(m for m, _ in local)
    residue = sum(r * (modulus // m) * pow(modulus // m, -1, m)
                  for m, r in local) % modulus
    return modulus, residue


def original(role, data):
    coords = [dict(prime=p, digit=d, exponent=e, residue=cylinder(p, d, e))
              for p, d, e in data]
    m, a = crt([(v['prime'] ** v['exponent'], v['residue']) for v in coords])
    return dict(role=role, modulus=m, residue=a, coordinates=coords)


def block(role, data):
    # Each coordinate is the union of depths 1..K in one fixed digit channel.
    return dict(role=role, coordinates={p: (d, k) for p, d, k in data})


def channel_mass(p, depth, weights):
    return sum((F(1, p ** e) for e in range(1, depth + 1)), F(0)) / weights[p]


def union_mass(blocks, weights):
    answer = F(0)
    nonzero_intersections = 0
    by_size = {}
    for size in range(1, len(blocks) + 1):
        subtotal = F(0)
        for subset in combinations(blocks, size):
            meet = {}
            compatible = True
            for event in subset:
                for p, (d, k) in event['coordinates'].items():
                    if p in meet and meet[p][0] != d:
                        compatible = False
                        break
                    meet[p] = (d, min(k, meet[p][1]) if p in meet else k)
                if not compatible:
                    break
            if compatible:
                value = prod(channel_mass(p, k, weights) for p, (_, k) in meet.items())
                subtotal += value
                nonzero_intersections += 1
        by_size[str(size)] = ratio(subtotal)
        answer += (1 if size % 2 else -1) * subtotal
    return answer, by_size, nonzero_intersections


def construct(kind):
    primary = kind == 'primary'
    heights = {p: (7 if p == 3 else 3) if primary else (6 if p == 3 else 2)
               for p in PRIMES}
    ternary_height = 4 if primary else 5
    blocks = [block(f'star-{q}', [(3, 2, ternary_height), (q, 2, 2)])
              for q in PRIMES[1:]]
    if primary:
        roles = [((5, 3), (7, 3)), ((5, 4), (11, 3)),
                 ((7, 4), (11, 4)), ((7, 5), (13, 3)),
                 ((7, 6), (17, 3))]
        blocks.extend(block(f'pair-{u[0]}-{v[0]}',
                            [(3, 2, ternary_height), (u[0], u[1], 2), (v[0], v[1], 2)])
                      for u, v in roles)
    else:
        blocks.extend([block('triangle-5-7', [(3, 2, 5), (5, 3, 2), (7, 3, 2)]),
                       block('old-5-7', [(5, 4, 2), (7, 4, 2)])])

    rows = [original(f'pure-{p}', [(p, 0, e)])
            for p in PRIMES for e in range(1, heights[p] + 1)]
    pure_count = len(rows)
    for event in blocks:
        data = sorted(event['coordinates'].items())
        for exponents in product(*(range(1, k + 1) for _, (_, k) in data)):
            rows.append(original(event['role'],
                                 [(p, d, e) for (p, (d, _)), e in zip(data, exponents)]))

    expected_count = 153 if primary else 102
    prefix = kind + ': '
    check(prefix + 'complete original count', len(rows) == expected_count)
    check(prefix + 'numerical moduli pairwise distinct', len({r['modulus'] for r in rows}) == len(rows))
    check(prefix + 'all labels odd greater than one', all(r['modulus'] > 1 and r['modulus'] % 2 for r in rows))
    check(prefix + 'canonical residues and exact CRT projections',
          all(0 <= r['residue'] < r['modulus'] and
              all(r['residue'] % (c['prime'] ** c['exponent']) == c['residue']
                  for c in r['coordinates']) for r in rows))
    check(prefix + 'all prime/exponent support accounted for',
          all(r['modulus'] == prod(c['prime'] ** c['exponent'] for c in r['coordinates'])
              and all(c['prime'] in heights and c['exponent'] <= heights[c['prime']]
                      for c in r['coordinates']) for r in rows))
    check(prefix + 'all required mixed ternary supports',
          all((r['modulus'] % 3 == 0) or (not primary and r['role'] == 'old-5-7')
              for r in rows[pure_count:]))

    period = prod(p ** heights[p] for p in PRIMES)
    for i, row in enumerate(rows):
        overrides = {c['prime']: (c['digit'], c['exponent']) for c in row['coordinates']}
        local = []
        for p in PRIMES:
            value = (p ** heights[p] - 1) // (p - 1)
            if p in overrides:
                d, e = overrides[p]
                value += (d - 1) * p ** (e - 1)
            local.append((p ** heights[p], value))
        witness_period, point = crt(local)
        hits = [j for j, r in enumerate(rows) if point % r['modulus'] == r['residue']]
        check(prefix + f'original {i} has explicit private point', witness_period == period and hits == [i])
        row['private_point'] = point

    weights = {p: 1 - sum((F(1, p ** e) for e in range(1, heights[p] + 1)), F(0)) for p in PRIMES}
    omega = prod(weights.values())
    check(prefix + 'pure counts match exact coordinate cardinalities',
          all(weights[p] == F(p ** heights[p] - sum(p ** (heights[p] - e)
                                                   for e in range(1, heights[p] + 1)),
                              p ** heights[p]) for p in PRIMES))
    used_cells = {p: set() for p in PRIMES}
    for row in rows:
        for c in row['coordinates']:
            used_cells[c['prime']].add((c['digit'], c['exponent']))
    check(prefix + 'distinct prefix cells pairwise disjoint on each coordinate',
          all(cylinder(p, d, e) % gcd(p ** e, p ** f) != cylinder(p, c, f) % gcd(p ** e, p ** f)
              for p, cells in used_cells.items()
              for (d, e), (c, f) in combinations(sorted(cells), 2)))
    loss, ie_by_size, ie_nonzero = union_mass(blocks, weights)
    survival = 1 - loss
    haar_survival = omega * survival
    r0 = prod(1 + F(1, p - 1) / weights[p] for p in PRIMES) - 1
    global_bound = r0 / survival
    q3 = F(1, 3) / weights[3]
    clipped_bound = min(F(1), q3 / survival) + (r0 - q3) / survival
    required_debit = r0 - TARGET * survival
    label3_debit = max(F(0), q3 - survival)
    expected_loss = (F(80458424237490660, 115676825858028029) if primary
                     else F(27943515594546, 40357058369825))
    expected_haar = (F(346765800571444864, 4970375566622841375) if primary
                     else F(12413542775279, 173200065313275))
    expected_r0 = (F(4183137340318400011792327, 1238951421369984756482048) if primary
                   else F(19793237799862001737, 5891381494991106048))
    check(prefix + 'block inclusion-exclusion agrees with stated exact loss', loss == expected_loss)
    check(prefix + 'strict uniform loss obstruction', loss > LOSS_TARGET)
    check(prefix + 'positive exact full Haar survivor', haar_survival == expected_haar and haar_survival > 0)
    check(prefix + 'complete product-query norm exact formula', r0 == expected_r0)
    check(prefix + 'ordinary clipped bound strictly below target', clipped_bound < TARGET)
    if primary:
        check(prefix + 'unclipped source-adaptive estimate is above target', global_bound > TARGET)
        check(prefix + 'single-label debit exceeds required debit', label3_debit > required_debit > 0)
        check(prefix + 'exact single-query repair', clipped_bound == F(26143266279751984807415409, 2640435704882446344912896))
    else:
        check(prefix + 'ordinary global estimate already passes', global_bound < TARGET)

    counts = {}
    for row in rows:
        counts[row['role']] = counts.get(row['role'], 0) + 1
    # b-v is an unused-label cap sum for THIS same complete pure source.
    cap_total = sum((F(1, row['modulus']) * prod(1 / weights[c['prime']] for c in row['coordinates'])
                     for row in rows[pure_count:]), F(0))
    b = r0 - sum((1 / weights[p] - 1 for p in PRIMES), F(0))
    unused_bound = (b - cap_total) / survival
    check(prefix + 'unused-label cap sum nonnegative', b >= cap_total)
    check(prefix + 'actual unused-query bound below two', unused_bound < 2)
    check(prefix + 'actual full survivor density below fifteen', 1 / haar_survival < 15)
    return dict(
        family=kind, pure_heights=heights, pure_count=pure_count,
        original_count=len(rows), role_counts=counts,
        full_period=period, original_rows=rows,
        pure_coordinate_masses={p: ratio(w) for p, w in weights.items()},
        pure_source_mass=ratio(omega), mixed_blocks=blocks,
        inclusion_exclusion_subset_count=2 ** len(blocks) - 1,
        inclusion_exclusion_nonzero_intersections=ie_nonzero,
        inclusion_exclusion_sums_by_size=ie_by_size,
        mixed_loss=ratio(loss), loss_threshold_gap=ratio(loss - LOSS_TARGET),
        conditional_survivor_mass=ratio(survival), full_haar_survivor_mass=ratio(haar_survival),
        source_complete_query_norm=ratio(r0), global_conditioning_bound=ratio(global_bound),
        global_bound_minus_target=ratio(global_bound - TARGET), query3_source_mass=ratio(q3),
        clipped_conditioning_bound=ratio(clipped_bound), clipped_target_margin=ratio(TARGET - clipped_bound),
        required_debit=ratio(required_debit), label3_guaranteed_debit=ratio(label3_debit),
        label3_debit_margin=ratio(label3_debit - required_debit),
        same_source_mixed_original_cap_sum=ratio(cap_total),
        unused_query_bound=ratio(unused_bound), full_survivor_density=ratio(1 / haar_survival))



def general_bridge():
    # Algebraic monotonicity is proved in the report. These are exact
    # constants and all 128 corners, not a sampling proof of monotonicity.
    endpoint_a = {p: (F(1), F(p - 1, p - 2)) for p in PRIMES}
    values = []
    for row in product(*(endpoint_a[p] for p in PRIMES)):
        caps = dict(zip(PRIMES, row))
        B = prod(1 + caps[p] / (p - 1) for p in PRIMES[1:])
        remainder = B - 1 + caps[3] * (B / 2 - F(1, 3))
        direct = prod(1 + caps[p] / (p - 1) for p in PRIMES) - 1 - caps[3] / 3
        check('general cap identity at corner ' + str(len(values)), remainder == direct)
        values.append(remainder)
    cap = max(values)
    threshold = 1 - cap / (TARGET - 1)
    check('general exact clipped numerator', cap == F(7613, 2805))
    check('general exact direct-query loss threshold', threshold == F(20657, 28270))
    check('general threshold strict extension', threshold > LOSS_TARGET)
    alpha = F(7235955529, 6075000000000)
    check('original G density cap', 1 / alpha > 800 > 15)
    # Positive exponential series bounds e below 68/25 and above 19/7.
    term = F(1)
    partial = term
    for n in range(1, 13):
        term /= n
        partial += term
    upper = partial + (term / 13) / (1 - F(1, 14))
    check('Taylor lower bound for e', partial > F(19, 7))
    check('Taylor upper bound for e', upper < F(68, 25))
    check('concrete entropy below three', F(19, 7) ** 3 > 15)
    check('original log Lambda above twenty thirds', F(68, 25) ** 20 < 800 ** 3)
    return dict(cap_numerator=ratio(cap), loss_threshold=ratio(threshold),
                corner_count=len(values), target=ratio(TARGET),
                original_alpha=ratio(alpha), exp_lower='19/7', exp_upper='68/25',
                scope='Conditional direct-query bound for arbitrary finite distinct P-smooth originals. No general G claim at this loss threshold.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    families = [construct('primary'), construct('fallback')]
    bridge = general_bridge()
    result = dict(
        scope='General conditional single-query bound and two actual distinct-modulus loss obstructions; no full-period enumeration; no Lean.',
        general_single_query_bridge=bridge,
        target=ratio(TARGET), uniform_loss_threshold=ratio(LOSS_TARGET),
        expected_values_disclosed=True,
        claims_refuted=['Uniform mixed loss below 173/250 on the two proposed enlarged classes.'],
        claims_not_refuted=['Erdos 7', 'Existence of a supported law with R below 565/51'],
        families=families, checks_passed=len(CHECKS), checks=CHECKS)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(checks_passed=len(CHECKS), output=str(args.output),
                         results=[{k: f[k] for k in ('family', 'original_count', 'mixed_loss',
                                                     'full_haar_survivor_mass',
                                                     'clipped_conditioning_bound', 'clipped_target_margin')}
                                  for f in families]), indent=2))


if __name__ == '__main__':
    main()
