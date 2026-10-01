#!/usr/bin/env python3
"""Exact root-incidence core certificates with one fixed source per case.

Ordinary conditional proof controls, complete height/query/tail arithmetic;
not Lean and not unrestricted Erdos7. Standard library and explicit inputs only.
"""
from fractions import Fraction as F
from math import comb, factorial, gcd, lcm, prod
from pathlib import Path
import argparse
import json

PRIMES = (5, 7, 11, 13, 17, 19, 23)
LEAVES = (4, 7, 2, 5, 8)
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
    need(n == 1, 'stated old-head prime support')
    return tuple(exponents)


def core(root, hits, short_forbidden):
    forbidden = short_forbidden if root == 1 else 127 ^ short_forbidden
    return hits & forbidden == 0 and hits.bit_count() <= 1


def response(t, removed, forbidden):
    absent, zero, one = F(1), F(1), F(0)
    for i in range(7):
        if removed >> i & 1:
            continue
        if forbidden >> i & 1:
            absent *= 1 - t[i]
        else:
            zero, one = zero * (1 - t[i]), one * (1 - t[i]) + zero * t[i]
    result = absent * (zero + one)
    need(type(result) is F and 0 <= result <= 1, 'exact root-core probability')
    return result


def compatible(leaf, hits, row, digits):
    m, a = row['modulus'], row['phase']
    exponents = row['exponents']
    h = exponents[0]
    if h and leaf % (3 ** min(h, 2)) != a % (3 ** min(h, 2)):
        return False
    return all(not e or bool(hits >> i & 1) == (a % q == digits[i])
               for i, (q, e) in enumerate(zip(PRIMES, exponents[1:])))


def query_data(weights, caps):
    root_cap = max(sum(weights[:2]), sum(weights[2:]))
    leaf_cap = max(weights)
    atoms = {1: F(1)}
    for axis, p in enumerate((3,) + PRIMES):
        def tail(j):
            if j == 1:
                return F(1)
            if p == 3:
                return root_cap if j == 2 else leaf_cap / 3 ** (j - 3)
            return caps[axis - 1] / p ** (j - 1)
        following = {}
        for x, probability in atoms.items():
            for j in range(1, (27 // x) + 1):
                mass = tail(j) - tail(j + 1)
                need(mass >= 0, 'nonnegative comparator atom')
                following[x * j] = following.get(x * j, F(0)) + probability * mass
        atoms = following
    # This expression is essential when caps=1; prod(caps) is then wrong.
    nonternary_mean = prod((1 + c / (q - 1) for c, q in zip(caps, PRIMES)), start=F(1))
    mean = (1 + root_cap + 3 * leaf_cap / 2) * nonternary_mean
    hinges = {h: mean - h + sum(((h - n) * p for n, p in atoms.items() if n < h), F(0))
              for h in range(28)}
    need(all(h > 0 for h in hinges.values()), 'positive complete comparator hinges')
    def a4(p):
        z = F(1, p - 1)
        return 15 * z + 50 * z ** 2 + 60 * z ** 3 + 24 * z ** 4
    fourth = ((1 + 15 * root_cap + 216 * leaf_cap)
              * prod((1 + c * a4(q) for c, q in zip(caps, PRIMES)), start=F(1))
              * (1 + F(28, 27) * a4(29)))
    return hinges, fourth, nonternary_mean, mean


def complete_tail(spec):
    B, ell, growth, delta = spec['cutoff'], spec['ell'], spec['growth'], F(spec['delta'])
    need(type(B) is int and type(ell) is int and type(growth) is int,
         'integer complete-tail parameters')
    need(B >= 286 and ell >= 4 and 3 ** ell <= B and 4 * ell >= growth and 0 < delta < 1,
         'inherited analytic prime-tail range')
    coefficients = (F(1),) + tuple(F(x) / (1 - delta) for x in (15, 50, 60, 24))
    need(all(x <= comb(growth, i) for i, x in enumerate(coefficients)),
         'quartic growth coefficient domination')
    return (F(27, 256) / (3 * delta ** 3 * (1 - delta))
            * F(2 * ell * ell + 1, 2 * ell * ell - 1) ** growth
            * F(B, (B - 1) ** 4)
            * sum((F(factorial(growth), factorial(growth - j) * (3 * ell) ** j)
                   for j in range(growth + 1)), F(0)))


def calculate(cert):
    global CHECKS
    CHECKS = 0
    need(cert['schema'] == 'root-incidence-repair-v1', 'certificate schema')
    need(tuple(cert['primes']) == PRIMES, 'seven fixed nonternary head primes')
    short = cert['short_forbidden_primes']
    need(len(short) == len(set(short)) and set(short) <= set(PRIMES), 'one declared root incidence')
    R = sum(1 << PRIMES.index(q) for q in short)
    digits = cert['reference_digits']
    need(len(digits) == 7 and all(type(c) is int and 0 <= c < q for c, q in zip(digits, PRIMES)),
         'one reference first digit per prime')
    selected = cert['selected_labels']
    need(len(selected) == len(set(selected)), 'distinct selected numerical slots')
    selected_specs = {}
    for m in selected:
        need(type(m) is int and m > 1 and m % 2 == 1, 'odd nonunit selected label')
        exponents = factor(m)
        h = exponents[0]
        support = sum(1 << i for i, e in enumerate(exponents[1:]) if e)
        need(h <= 2 and support and (h > 0 or support.bit_count() >= 2), 'selected shallow mixed label')
        selected_specs[m] = (h, support, m // 3 ** h)
    family = []
    for original in cert['actual_family']:
        m, a = original['modulus'], original['phase']
        need(type(m) is int and m > 1 and m % 2 == 1, 'odd nonunit actual modulus')
        need(type(a) is int and 0 <= a < m, 'canonical fixed actual phase')
        exponents = factor(m)
        if m in (3, 9):
            need(a == int(m == 9), 'one common pure3/9 normalization')
        family.append(dict(modulus=m, phase=a, exponents=exponents))
    need(len({row['modulus'] for row in family}) == len(family), 'numerically distinct actual originals')
    for root in (1, 2):
        for hits in range(128):
            for removed in range(128):
                need(not core(root, hits, R) or core(root, hits & ~removed, R),
                     'forcing queried hits absent enlarges this same root core')
    null_labels = []
    for row in family:
        if row['modulus'] not in selected_specs:
            continue
        need(not any(core(leaf % 3, hits, R) and compatible(leaf, hits, row, digits)
                     for leaf in LEAVES for hits in range(128)), 'actual selected class is structurally core-null')
        null_labels.append(row['modulus'])
    period = lcm(9, prod(PRIMES), *(row['modulus'] for row in family))
    witness = cert['witness']
    x, modulus = 0, 1
    for a, m in witness['coordinates']:
        need(type(m) is int and m > 1 and type(a) is int and 0 <= a < m and gcd(modulus, m) == 1,
             'valid pairwise coprime CRT witness coordinate')
        x += modulus * ((a - x) * pow(modulus, -1, m) % m)
        modulus *= m
        x %= modulus
    need(modulus == period == witness['period'] and x == witness['integer'], 'one full resolving CRT witness')
    hitmask = sum((x % q == c) << i for i, (q, c) in enumerate(zip(PRIMES, digits)))
    need(x % 9 in LEAVES and core(x % 3, hitmask, R), 'witness belongs to the entire new core')
    need(all(x % row['modulus'] != row['phase'] for row in family), 'witness avoids every actual original')
    results = []
    for case in cert['cases']:
        weights = tuple(map(F, case['weights']))
        need(len(weights) == 5 and all(w >= 0 for w in weights) and sum(weights) == 1,
             'one normalized fixed five-leaf law')
        need(case['cap_kind'] in ('pure_survivor', 'haar'), 'declared cylinder cap regime')
        caps = tuple(F(q - 1, q - 2) for q in PRIMES) if case['cap_kind'] == 'pure_survivor' else (F(1),) * 7
        need(case['source_mode'] in ('box', 'haar'), 'declared source premise')
        need(case['source_mode'] != 'box' or case['cap_kind'] == 'pure_survivor',
             'arbitrary pure inventories require universal survivor caps')
        if case['source_mode'] == 'haar' or case['cap_kind'] == 'haar':
            need(not any(row['exponents'][0] == 0 and sum(e > 0 for e in row['exponents'][1:]) == 1
                         for row in family), 'actual old pure-q inventories are empty for Haar case')
        beta = tuple(prod((caps[i] / (q - 1) for i, q in enumerate(PRIMES) if s >> i & 1), start=F(1))
                     for s in range(128))
        remain = [[beta[s] if s and (h > 0 or s.bit_count() > 1) else F(0) for s in range(128)] for h in range(3)]
        for h, support, n in selected_specs.values():
            remain[h][support] -= prod((caps[i] for i in range(7) if support >> i & 1), start=F(1)) / n
        need(all(v >= 0 for row in remain for v in row), 'nonnegative full residual inventories')
        sA, sB, vA, vB = sum(weights[:2]), sum(weights[2:]), max(weights[:2]), max(weights[2:])
        def lower(t):
            factors = []
            for removed in range(128):
                A, B = response(t, removed, R), response(t, removed, 127 ^ R)
                factors.append((sA * A + sB * B, max(sA * A, sB * B), max(vA * A, vB * B)))
            mass = factors[0][0]
            high = sum((beta[s] * factors[s][2] / 2 for s in range(128)), F(0))
            shallow = sum((remain[h][s] * factors[s][h] for h in range(3) for s in range(128)), F(0))
            return mass - high - shallow, mass, high, shallow
        vertex_rows = []
        for mask in range(128):
            t = tuple(caps[i] / q if mask >> i & 1 else F(0) for i, q in enumerate(PRIMES))
            value, mass, high, shallow = lower(t)
            vertex_rows.append(dict(mask=mask, value=str(value), mass=str(mass), high_loss=str(high), shallow_loss=str(shallow)))
        worst = min(range(128), key=lambda i: F(vertex_rows[i]['value']))
        box_alpha = F(vertex_rows[worst]['value'])
        actual_t = tuple(F(1, q) for q in PRIMES)
        haar_alpha, haar_mass, haar_high, haar_shallow = lower(actual_t)
        # Independent Boolean formula for the original Haar root-core probabilities.
        for root in (1, 2):
            direct = sum((prod((F(1, q) if hits >> i & 1 else F(q - 1, q)
                               for i, q in enumerate(PRIMES)), start=F(1))
                          for hits in range(128) if core(root, hits, R)), F(0))
            need(direct == response(actual_t, 0, R if root == 1 else 127 ^ R), 'Boolean and recurrence root masses agree')
        alpha = box_alpha if case['source_mode'] == 'box' else haar_alpha
        need(alpha == F(case['expected_source_mass']) and alpha > 0, 'declared exact positive source mass')
        need(box_alpha == F(case['expected_box_mass']) and worst == case['expected_worst_vertex'], 'all128 box control')
        hinges, fourth, nonternary_mean, mean = query_data(weights, caps)
        query, h = min((h + value / alpha, h) for h, value in hinges.items())
        tail_results = []
        for tail in case['tails']:
            tau = complete_tail(tail)
            gate = min((value + 27 * fourth * tau) / (28 - h) for h, value in hinges.items())
            final = (28 - query) / 27 - fourth * tau / alpha
            need(final > F(tail['mass_floor']), 'strict full-tail mass floor under this same source')
            need((box_alpha > gate) == tail['expected_box_pass'], 'stated uniform-box gate control')
            tail_results.append(dict(cutoff=tail['cutoff'], ell=tail['ell'], tau=str(tau), gate=str(gate),
                                     box_pass=box_alpha > gate, final_mass=str(final), final_mass_decimal=float(final),
                                     mass_floor=tail['mass_floor']))
        results.append(dict(name=case['name'], weights=list(map(str, weights)), cap_kind=case['cap_kind'],
                            source_mode=case['source_mode'], caps=list(map(str, caps)), source_mass=str(alpha),
                            source_mass_decimal=float(alpha), box_mass=str(box_alpha), worst_vertex=worst,
                            haar_mass_bound=str(haar_alpha), haar_core_mass=str(haar_mass),
                            haar_high_loss=str(haar_high), haar_shallow_loss=str(haar_shallow),
                            vertices=vertex_rows, query_h=h, query_upper=str(query), query_upper_decimal=float(query),
                            nonternary_complete_mean=str(nonternary_mean), comparator_mean=str(mean),
                            complete_hinges={str(h): str(value) for h, value in hinges.items()},
                            fourth_product_with29=str(fourth), tails=tail_results))
    return dict(schema='root-incidence-repair-result-v1', check_count=CHECKS,
                scope='Ordinary conditional core-incidence repair with one fixed source per case. Selected actual classes are null on the stated core; all unselected old heights and allowed29/tail phases are charged. Not arbitrary shallow phases, not Lean, not unrestricted Erdos7.',
                short_forbidden_primes=short, reference_digits=digits, selected_labels=selected,
                actual_null_labels=sorted(null_labels), absent_selected_labels=sorted(set(selected) - set(null_labels)),
                common_crt_period=period, witness=x, cases=results)


def main():
    here = Path(__file__)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=here.with_name(here.stem + '_certificate.json'))
    parser.add_argument('--result', type=Path, default=here.with_suffix('.json'))
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = calculate(json.loads(args.certificate.read_text()))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, indent=2) + '\n')
    else:
        need(result == json.loads(args.result.read_text()), 'retained result exact replay')
    print(json.dumps(dict(check_count=result['check_count'], cases=[dict(name=row['name'],
                          source_mass=row['source_mass'], query_upper=row['query_upper_decimal'],
                          tails=[dict(cutoff=t['cutoff'], mass=t['final_mass_decimal']) for t in row['tails']])
                          for row in result['cases']]), indent=2))


if __name__ == '__main__':
    main()
