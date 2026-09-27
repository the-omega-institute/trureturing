#!/usr/bin/env python3
"""Exact original-AP checks for the full private vector under residue swaps.

All fixtures are whole covers with even moduli. The nonzero examples are
not divisor-closed and do not refute an extremal odd-cover cancellation
claim. Standard library only; checks stay active with Python -O. No Lean
verification, new general surplus bound, or literature novelty is claimed.
"""
from fractions import Fraction
from math import gcd, lcm
import json


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def factors(n):
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.append(n)
    return tuple(result)


def ppart(n, p):
    result = 1
    while n % p == 0:
        result *= p
        n //= p
    return result


def prepare(aps, require_irredundant=True):
    residues = dict((d, a) for a, d in aps)
    check(len(residues) == len(aps), 'repeated modulus')
    check(all(d > 1 and 0 <= a < d for d, a in residues.items()), 'bad AP')
    period = lcm(*residues)
    primes = factors(period)
    check(all(p in residues for p in primes), 'missing original prime')
    classes = {d: {y for y in range(period) if y % d == a}
               for d, a in residues.items()}
    labels = [frozenset(d for d, points in classes.items() if y in points)
              for y in range(period)]
    private = {d: {y for y, hits in enumerate(labels) if hits == {d}}
               for d in residues}
    covering = all(labels)
    irredundant = covering and all(private.values())
    comparable = all(not (classes[d] & classes[e])
                     for d in residues for e in residues
                     if d < e and e % d == 0)
    if require_irredundant:
        check(irredundant, 'fixture is not an irredundant whole cover')
        check(comparable, 'comparable fixture originals intersect')
    if covering:
        check(sum(Fraction(1, d) for d in residues) - 1 ==
              Fraction(sum(len(hits) - 1 for hits in labels), period),
              'whole-cover excess identity')
    missing = sorted({j for d in residues for j in range(2, d)
                      if d % j == 0 and j not in residues})
    return dict(residues=residues, period=period, primes=primes,
                classes=classes, labels=labels, private=private,
                covering=covering, irredundant=irredundant,
                comparable=comparable, missing_divisors=missing)


def root_transposition(y, period, p, low_power, b, c):
    """Exchange two low p-power residues, retaining all higher digits."""
    low = y % low_power
    replacement = c if low == b else b if low == c else low
    full_power = ppart(period, p)
    other = period // full_power
    target = y % full_power - low + replacement
    return (y + other * ((target - y) * pow(other, -1, full_power)
                         % full_power)) % period


def transport_check(old, new, p, low_power, b, c):
    period = old['period']
    permutation = [root_transposition(y, period, p, low_power, b, c)
                   for y in range(period)]
    check(len(set(permutation)) == period, 'root map is not bijective')
    check(all(permutation[permutation[y]] == y for y in range(period)),
          'root map is not an involution')
    full_power = ppart(period, p)
    for y, z in enumerate(permutation):
        check((y % full_power) // low_power ==
              (z % full_power) // low_power, 'root map changed higher digits')
        check(y % (period // full_power) == z % (period // full_power),
              'root map changed a different prime coordinate')
    for d in old['residues']:
        check({permutation[y] for y in old['classes'][d]} == new['classes'][d],
              'root map failed labelled-AP transport')
        check({permutation[y] for y in old['private'][d]} == new['private'][d],
              'root map failed private-set transport')
        check(len(old['private'][d]) == len(new['private'][d]),
              'transport changed a private mass')


def swap_check(old, p, m, d):
    period = old['period']
    residues = old['residues']
    power = d // m
    b, c = residues[m], residues[d] % m
    parent = old['classes'][m]
    cofactor = {y for y in range(period) if y % m == c}
    prefix = {y for y in range(period) if y % power == residues[d] % power}
    outside = set(range(period)) - prefix
    check(not (parent & cofactor), 'old parent meets child cofactor')
    check(not (prefix & old['classes'][p]), 'child prefix meets prime root')
    changed = dict(residues)
    changed[m] = c
    changed[d] = (b + m * (((residues[d] - b) * pow(m, -1, power)) % power)) % d
    new = prepare([(a, j) for j, a in changed.items()], False)
    legal = not (old['private'][m] & outside)
    check(new['covering'] == legal, 'legal-exchange equivalence')
    for y in range(period):
        change = len(new['labels'][y]) - len(old['labels'][y])
        expected = int(y in cofactor and y in outside) - int(y in parent and y in outside)
        check(change == expected, 'full multiplicity derivative')
    if not legal:
        return dict(p=p, m=m, d=d, legal=False)
    check(new['private'][m] == old['private'][d], 'new parent-private set')
    check(new['private'][d] == old['private'][m], 'new child-private set')
    check(not (new['private'][m] & outside), 'reverse swap is not legal')
    delta, gains, losses = {}, {}, {}
    for q in old['primes']:
        delta[q] = len(new['private'][q]) - len(old['private'][q])
        if q == m:
            check(delta[q] == len(old['private'][d]) - len(old['private'][m]),
                  'changed prime root derivative')
            wrong_old_root = parent - set().union(
                *(points for j, points in new['classes'].items() if j != m))
            check(not wrong_old_root and new['private'][m],
                  'old-root normalization control did not separate')
            continue
        gains[q] = {y for y in outside if old['labels'][y] == {m, q}}
        losses[q] = old['private'][q] & cofactor & outside
        check(delta[q] == len(gains[q]) - len(losses[q]), 'prime vector derivative')
        if m % q == 0:
            check(not gains[q] and not losses[q], 'parent-divisor prime changed')
    pfree = [j for j in residues if j % p]
    survivor = set(range(period)) - set().union(*(old['classes'][j] for j in pfree))
    exclusive = parent - set().union(*(old['classes'][j] for j in pfree if j != m))
    source = cofactor & survivor
    check(p * delta[p] == len(exclusive) - len(source), 'cofactor survivor derivative')
    for exponent in (0, 1, 2):
        coeff = {q: q ** exponent for q in old['primes']}
        actual = sum(coeff[q] * delta[q] for q in coeff)
        formula = sum(coeff[q] * (len(gains[q]) - len(losses[q])) for q in gains)
        if m in coeff:
            formula += coeff[m] * (len(old['private'][d]) - len(old['private'][m]))
        check(actual == formula, 'weighted potential derivative')
    prime_parent = m in old['primes']
    sibling = len(factors(m)) == 1 and b % (m // factors(m)[0]) == c % (m // factors(m)[0])
    if new['irredundant'] and (prime_parent or sibling):
        transport_check(old, new, factors(m)[0], m, b, c)
        check(len(exclusive) == len(source), 'rigidity cofactor equality')
        check(len(old['private'][m]) * d <= period,
              'rigid parent-private cylinder bound')
    return dict(p=p, m=m, d=d, legal=True, irredundant=new['irredundant'],
                comparable=new['comparable'], prime_parent=prime_parent,
                sibling=sibling, delta_counts=delta,
                old_prime_counts={q: len(old['private'][q]) for q in old['primes']},
                new_prime_counts={q: len(new['private'][q]) for q in old['primes']},
                gain_points={q: sorted(points) for q, points in gains.items()},
                loss_points={q: sorted(points) for q, points in losses.items()})


FIXTURES = (
    ('period12', ((0,2),(0,3),(1,4),(5,6),(7,12))),
    ('period144', ((0,2),(0,3),(1,4),(5,6),(7,24),(7,36),
                   (19,48),(67,72),(91,144))),
    ('period960', ((0,2),(0,3),(3,4),(0,5),(1,8),(1,10),(13,16),
                   (17,20),(13,40),(69,160),(149,320),(469,480),(629,960))),
    ('period120', ((0,2),(0,3),(0,5),(1,6),(1,8),(1,10),
                   (2,15),(3,20),(11,24),(13,40),(29,60),(119,120))),
    ('period180', ((0,2),(0,3),(0,5),(1,4),(1,9),(1,10),(2,15),
                   (3,20),(5,18),(7,30),(7,36),(29,45),(49,90),(179,180))),
)


def main():
    summary = []
    found = {}
    total_candidates = total_legal = total_prime_rigid = total_sibling_rigid = 0
    for name, aps in FIXTURES:
        old = prepare(aps)
        rows = []
        for d in old['residues']:
            for p in factors(d):
                m = d // ppart(d, p)
                if m <= 1 or m not in old['residues']:
                    continue
                row = swap_check(old, p, m, d)
                rows.append(row)
                found[(name, p, m, d)] = row
        legal = [r for r in rows if r['legal']]
        prime_rigid = sum(r['irredundant'] and r['prime_parent'] for r in legal)
        sibling_rigid = sum(r['irredundant'] and r['sibling'] and not r['prime_parent'] for r in legal)
        total_candidates += len(rows)
        total_legal += len(legal)
        total_prime_rigid += prime_rigid
        total_sibling_rigid += sibling_rigid
        summary.append(dict(name=name, period=old['period'], original_APs=len(aps),
                            missing_divisors=old['missing_divisors'],
                            candidates=len(rows), legal=len(legal),
                            irredundant_after=sum(r['irredundant'] for r in legal),
                            prime_parent_transports=prime_rigid,
                            composite_sibling_transports=sibling_rigid))
    selected = found[('period120', 3, 8, 24)]
    check(selected['legal'] and selected['irredundant'] and selected['comparable'],
          'period120 exchange hypotheses')
    check(selected['delta_counts'] == {2: 0, 3: 1, 5: 0}, 'period120 nonzero control')
    cross = found[('period180', 5, 9, 45)]
    check(cross['legal'] and cross['irredundant'] and cross['comparable'],
          'period180 exchange hypotheses')
    check(cross['old_prime_counts'] == {2: 32, 3: 6, 5: 3}, 'period180 old vector')
    check(cross['new_prime_counts'] == {2: 34, 3: 6, 5: 3}, 'period180 new vector')
    check(cross['gain_points'] == {2: [28,46,82,118,136,172], 3: [], 5: [55]},
          'period180 exact gain cells')
    check(cross['loss_points'] == {2: [38,56,128,146], 3: [], 5: [155]},
          'period180 exact loss cells')
    print(json.dumps(dict(fixtures=summary, candidates=total_candidates,
                          legal_swaps=total_legal,
                          prime_parent_transports=total_prime_rigid,
                          composite_sibling_transports=total_sibling_rigid,
                          distinguished_change=selected, cross_prime_change=cross),
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
