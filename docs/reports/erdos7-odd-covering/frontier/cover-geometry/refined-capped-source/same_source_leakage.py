#!/usr/bin/env python3
"""Exact same-source leakage repair of the identified Report801 result.

Uses one inherited verified source artifact, finite declared actual phases,
exact CRT intersections and rational continuation. Ordinary proof, not Lean.
"""
from fractions import Fraction as F
from math import gcd, lcm, prod
from pathlib import Path
import argparse
import hashlib
import json

PRIMES = (5, 7, 11, 13, 17, 19, 23)
LEAVES = (4, 7, 2, 5, 8)
# Identity of the retained Report801 input at commit594fdf57cd.
SOURCE_SHA256 = 'dc4ceba98c8e992a85c001d50aed1928a255c937f4b1bc248b6f1850cb6e222c'
CHECKS = 0


def need(ok, label):
    global CHECKS
    CHECKS += 1
    if not ok:
        raise ValueError(label)


def factor(m):
    n, exponents = m, []
    for p in (3,) + PRIMES:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        exponents.append(e)
    need(n == 1, 'finite witness family uses only the stated old head')
    return tuple(exponents)


def validate_class(row):
    m, a = row['modulus'], row['phase']
    need(type(m) is int and m > 1 and m % 2 == 1, 'odd nonunit original modulus')
    need(type(a) is int and 0 <= a < m, 'canonical integer original phase')
    return factor(m)


def core(leaf, mask):
    return mask & 1 == 0 and mask.bit_count() <= 1 if leaf % 3 == 1 else mask & 126 == 0


def cylinder_core_mass(m, a, weights):
    exponents = factor(m)
    h, powers = exponents[0], exponents[1:]
    total = F(0)
    for leaf, w in zip(LEAVES, weights):
        if h and leaf % (3 ** min(h, 2)) != a % (3 ** min(h, 2)):
            continue
        w = w / 3 ** max(h - 2, 0)
        for mask in range(128):
            if not core(leaf, mask):
                continue
            probability = w
            for i, (q, e) in enumerate(zip(PRIMES, powers)):
                hit = bool(mask >> i & 1)
                if e:
                    if hit != (a % q == 2):
                        probability = F(0)
                        break
                    probability /= q ** e
                else:
                    probability *= F(1, q) if hit else F(q - 1, q)
            total += probability
    return total


def intersect(left, right):
    a, m = left
    b, n = right
    g = gcd(m, n)
    if (b - a) % g:
        return None
    reduced = n // g
    t = 0 if reduced == 1 else ((b - a) // g) * pow(m // g, -1, reduced) % reduced
    return ((a + m * t) % lcm(m, n), lcm(m, n))


def actual_union_mass(rows, weights):
    # Incremental exact inclusion-exclusion, merging identical CRT cylinders.
    # Zero core intersections are discarded before expansion.
    terms = {}
    for row in rows:
        if F(row['core_intersection']) == 0:
            continue
        item = row['phase'], row['modulus']
        following = dict(terms)
        following[item] = following.get(item, 0) + 1
        for previous, coefficient in terms.items():
            combined = intersect(previous, item)
            if combined is not None:
                following[combined] = following.get(combined, 0) - coefficient
        terms = {key: value for key, value in following.items() if value}
    return sum((coefficient * cylinder_core_mass(m, a, weights)
                for (a, m), coefficient in terms.items()), F(0)), len(terms)


def crt(pairs):
    x, modulus = 0, 1
    for a, m in pairs:
        need(type(m) is int and m > 1 and type(a) is int and 0 <= a < m,
             'valid declared CRT coordinate')
        need(gcd(modulus, m) == 1, 'coprime CRT coordinate interfaces')
        x += modulus * ((a - x) * pow(modulus, -1, m) % m)
        modulus *= m
        x %= modulus
    return x, modulus


def continuation(alpha, hinges, K, tau):
    need(alpha > 0, 'positive repaired old source')
    query, h = min((h + value / alpha, h) for h, value in hinges.items())
    final = (28 - query) / 27 - K * tau / alpha
    return dict(alpha=str(alpha), threshold=h, query_upper=str(query),
                query_upper_decimal=float(query), post29_mass=str((28 - query) / 27),
                full_tail_reserve=str(final), full_tail_reserve_decimal=float(final))


def calculate(cert, source_bytes):
    global CHECKS
    CHECKS = 0
    need(cert['schema'] == 'same-source-leakage-v1', 'certificate schema')
    source_hash = hashlib.sha256(source_bytes).hexdigest()
    need(source_hash == SOURCE_SHA256, 'identified verified Report801 source digest')
    source_result = json.loads(source_bytes)
    need(source_result['schema'] == 'retained-core-phase-union-result-v1', 'inherited source schema')
    matches = [row for row in source_result['cases'] if row['name'] == cert['source_case']]
    need(len(matches) == 1, 'one identified inherited source case')
    source = matches[0]
    weights = tuple(map(F, source['weights']))
    need(weights == tuple(map(F, cert['weights'])) and sum(weights) == 1,
         'same fixed five-leaf law for every term')
    selected = set(source['selected_labels'])
    alpha, K, tau = F(source['alpha']), F(source['fourth_product_with29']), F(source['tau3000'])
    hinges = {int(k): F(v) for k, v in source['full_hinges'].items()}
    need(set(hinges) == set(range(28)), 'all integer continuation hinges below28')
    gates = {h: (value + 27 * K * tau) / (28 - h) for h, value in hinges.items()}
    gate = min(gates.values())
    need(gate == F(source['critical']), 'recomputed inherited complete continuation gate')
    gamma = alpha - gate
    need(gamma > 0, 'positive available leakage interval')
    family = cert['actual_family']
    need(isinstance(family, list) and len({row['modulus'] for row in family}) == len(family),
         'numerically distinct actual originals')
    masses = []
    for row in family:
        e = validate_class(row)
        need(not (e[0] == 0 and sum(x > 0 for x in e[1:]) == 1),
             'actual pure-q inventories are empty in this finite instance')
        if row['modulus'] in (3, 9):
            need(row['phase'] == int(row['modulus'] == 9), 'one common pure3/9 normalization')
        value = cylinder_core_mass(row['modulus'], row['phase'], weights)
        masses.append(dict(**row, selected=row['modulus'] in selected, core_intersection=str(value)))
    present = [row for row in masses if row['selected']]
    positive = sorted(row['modulus'] for row in present if F(row['core_intersection']) > 0)
    need(positive == cert['expected_positive_labels'], 'declared positive selected intersections')
    total = sum((F(row['core_intersection']) for row in present), F(0))
    union, terms = actual_union_mass(present, weights)
    need(0 <= union <= min(total, F(1)), 'one actual union is bounded by individual core intersections')
    need(union == F(cert['expected_union_leakage']) and total == F(cert['expected_sum_leakage']),
         'exact declared joint and individual leakage values')
    epsilon = F(cert['leakage_budget'])
    need(union <= epsilon < gamma, 'certified actual union fits the strict complete-tail budget')
    repaired = continuation(alpha - epsilon, hinges, K, tau)
    need(F(repaired['full_tail_reserve']) > F(cert['tail_floor']), 'stated positive full-tail reserve')
    need(all((28 - h) / F(27) - (value + 27 * K * tau) / (27 * gate) <= 0
             for h, value in hinges.items()), 'budget equality gives no positive retained bound')
    floor = F(cert['comparison_floor'])
    need(0 <= floor < F(28, 27), 'valid comparison mass floor')
    stricter_gate = min((value + 27 * K * tau) / (F(28 - h) - 27 * floor)
                       for h, value in hinges.items() if F(28 - h) > 27 * floor)
    period = lcm(9, prod(PRIMES), *(row['modulus'] for row in family))
    need(period == cert['common_crt_period'], 'complete common source and family resolving period')
    witnesses = []
    for witness in cert['witnesses']:
        x, modulus = crt(witness['coordinates'])
        need(modulus == period and x == witness['integer'], 'declared common CRT witness')
        mask = sum((x % q == 2) << i for i, q in enumerate(PRIMES))
        need(x % 9 in LEAVES and core(x % 9, mask), 'witness is in the entire reference core')
        hits = sorted(row['modulus'] for row in family if x % row['modulus'] == row['phase'])
        need(hits == witness['actual_hits'], 'global witness actual-family incidences')
        witnesses.append(dict(name=witness['name'], integer=x, actual_hits=hits))
    control = cert['over_budget_control']
    validate_class(control)
    excess = cylinder_core_mass(control['modulus'], control['phase'], weights)
    need(excess == F(cert['expected_over_budget_leakage']) and excess > gamma,
         'declared single-cylinder leakage exceeds the uniform budget')
    return dict(schema='same-source-leakage-result-v1', check_count=CHECKS,
                scope='Conditional ordinary repair of the identified801 source. One actual union, one fixed law, full29 and prime tail above3000. No arbitrary-shallow-phase or unrestrictedErdos7 conclusion; not Lean.',
                inherited_source_sha256=source_hash, inherited_source_case=source['name'],
                weights=list(map(str, weights)), alpha23=str(alpha),
                positive_mass_gate=str(gate), minimizing_gate_h=min(gates, key=gates.get),
                leakage_supremum=str(gamma), leakage_supremum_decimal=float(gamma),
                comparison_floor=str(floor), comparison_floor_leakage_supremum=str(alpha - stricter_gate),
                comparison_floor_leakage_supremum_decimal=float(alpha - stricter_gate),
                actual_family=masses, absent_selected_labels=sorted(selected - {row['modulus'] for row in family}),
                actual_union_leakage=str(union), actual_union_leakage_decimal=float(union),
                individual_leakage_sum=str(total), exact_union_terms=terms,
                certified_leakage_budget=str(epsilon), budget_slack=str(gamma - epsilon),
                continuation=repaired, common_crt_period=period, witnesses=witnesses,
                over_budget_control=dict(**control, leakage=str(excess), leakage_decimal=float(excess)))


def main():
    here = Path(__file__)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=here.with_name(here.stem + '_certificate.json'))
    parser.add_argument('--source-result', type=Path, default=here.with_name('retained_core_phase_union.json'))
    parser.add_argument('--result', type=Path, default=here.with_suffix('.json'))
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = calculate(json.loads(args.certificate.read_text()), args.source_result.read_bytes())
    if args.write_result:
        args.write_result.write_text(json.dumps(result, indent=2) + '\n')
    else:
        need(result == json.loads(args.result.read_text()), 'retained result exact replay')
    print(json.dumps(dict(check_count=result['check_count'],
                          actual_union_leakage=result['actual_union_leakage'],
                          leakage_supremum_decimal=result['leakage_supremum_decimal'],
                          full_tail_reserve_decimal=result['continuation']['full_tail_reserve_decimal'])))


if __name__ == '__main__':
    main()
