"""Exact supported unit-mixture and arithmetic aggregate-error controls.

CRT inclusion-exclusion evaluates actual finite masks without enumerating the
outside period. Closed geometric moments and finite differences cross-check
the infinite-tail constants of the separate ordinary proof.
"""
from pathlib import Path
from fractions import Fraction as F
from math import gcd, lcm, prod
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
INPUT = 'supported_unit_mixture_input.json'
PIN = 'a8464d7e223410944fd612b1b7c62dddd8730f1c1c08a0a0f6c686bd8a12914b'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def part(n, primes):
    out = 1
    for p in primes:
        while n % p == 0:
            n //= p
            out *= p
    return out


def exponent(n, p):
    out = 0
    while n % p == 0:
        n //= p
        out += 1
    return out


def merge(left, right):
    if left is None:
        return None
    a, m = left
    b, n = right
    g = gcd(m, n)
    if (b - a) % g:
        return None
    nn = n // g
    k = 0 if nn == 1 else ((b - a) // g) * pow(m // g, -1, nn) % nn
    modulus = m * nn
    return ((a + m * k) % modulus, modulus)


def volume(positive=(), negative=()):
    base = (0, 1)
    for event in positive:
        base = merge(base, event)
        if base is None:
            return F()
    terms = [(base, 1)]
    for event in sorted(set(negative)):
        terms += [(intersection, -sign) for state, sign in terms[:]
                  if (intersection := merge(state, event)) is not None]
    out = sum((F(sign, state[1]) for state, sign in terms), F())
    need(0 <= out <= 1, 'CRT Boolean-event mass')
    return out


def poly_value(coeff, x):
    return sum((a * x ** k for k, a in enumerate(coeff)), F())


def tail(coeff, q, cutoff):
    t = F(1, q)
    moments = [1 / (1 - t), t / (1 - t) ** 2,
               t * (1 + t) / (1 - t) ** 3,
               t * (1 + 4 * t + t * t) / (1 - t) ** 4,
               t * (1 + 11 * t + 11 * t * t + t ** 3) / (1 - t) ** 5]
    exact = sum((a * moments[k] for k, a in enumerate(coeff)), F())
    exact -= sum((poly_value(coeff, j) * t ** j for j in range(cutoff + 1)), F())
    values = [poly_value(coeff, cutoff + 1 + k) for k in range(len(coeff))]
    differences = []
    while values:
        differences.append(values[0])
        values = [b - a for a, b in zip(values, values[1:])]
    independent = t ** (cutoff + 1) * sum((a * t ** k / (1 - t) ** (k + 1)
                                          for k, a in enumerate(differences)), F())
    need(exact == independent and exact > 0, 'closed moments equal finite-difference infinite tail')
    return exact


def bounds(cutoff, old_primes):
    er = tail([F(), F(1, 2), F(1, 2)], 23, cutoff)
    es = tail([F(1), F(2), F(1)], 29, cutoff)
    aa = tail([F(), F(23, 44), F(45, 44), F(1, 2)], 23, cutoff)
    bb = tail([F(4), F(59, 6), F(47, 6), F(13, 6), F(1, 6)], 29, cutoff)
    zp = prod(F(p, p - 1) for p in old_primes)
    response = 616 * F(27, 2) * zp * (F(899, 840) * aa + F(23, 22) * bb)
    return {'component_bound': 1 + cutoff * ((cutoff + 1) ** 2 - 1),
            'E_R': er, 'E_S': es, 'E': er + es, 'A': aa, 'B': bb, 'response': response}


def decomposition(data, units, cutoff, source_weights):
    low = [row for row in units if max(row['exponents']) <= cutoff]
    high = [row for row in units if max(row['exponents']) > cutoff]
    rnegative = [(row['residue'] % row['R'], row['R']) for row in low if row['S'] == 1]
    snegative = [(row['residue'] % row['S'], row['S']) for row in low if row['R'] == 1]
    mixed = [row for row in low if row['R'] > 1 and row['S'] > 1]
    rtests = sorted({(row['residue'] % row['R'], row['R']) for row in mixed}, key=lambda x: (x[1], x[0]))
    need(all(merge(a, b) is None or merge(a, b)[1] == max(a[1], b[1])
             for a in rtests for b in rtests), 'low R cylinders are laminar')
    atoms = [((), tuple(rnegative))]
    for event in rtests:
        refined = []
        for positive, negative in atoms:
            for pp, nn in ((positive + (event,), negative), (positive, negative + (event,))):
                if volume(pp, nn):
                    refined.append((pp, nn))
        need(len(refined) <= len(atoms) + 1, 'each sorted laminar cylinder adds at most one atom')
        atoms = refined
    need(len(atoms) <= 1 + cutoff * ((cutoff + 1) ** 2 - 1), 'universal low-component bound')
    need(sum((volume(pp, nn) for pp, nn in atoms), F()) == volume((), rnegative),
         'low R atoms partition the pure survivor')
    need(all(volume(atoms[i][0] + atoms[j][0], atoms[i][1] + atoms[j][1]) == 0
             for i in range(len(atoms)) for j in range(i)), 'R atoms are disjoint')
    components = []
    for pp, nn in atoms:
        mass = volume(pp, nn)
        active = []
        for row in mixed:
            intersection = volume(pp + ((row['residue'] % row['R'], row['R']),), nn)
            need(intersection in (F(), mass), 'low mixed activity constant on R atom')
            if intersection:
                active.append(row)
        sn = tuple(snegative + [(row['residue'] % row['S'], row['S']) for row in active])
        if volume((), sn):
            components.append((pp, nn, (), sn))
    low_events = [(row['residue'], row['modulus']) for row in low]
    need(sum((volume(rp, rn) * volume(sp, sn) for rp, rn, sp, sn in components), F())
         == volume((), low_events), 'exact low joint survivor decomposition')
    masks = {'R': [], 'S': []}
    assignments = []
    for row in high:
        j, k, ell = row['exponents']
        h = k + ell
        side = 'R' if row['S'] == 1 else 'S' if row['R'] == 1 else 'R' if j >= h + 1 else 'S'
        need((j > cutoff) if side == 'R' else (h > cutoff), 'assigned non-low projection lies in claimed tail')
        event = row['residue'] % row[side], row[side]
        masks[side].append(event)
        assignments.append({'original_modulus': row['modulus'], 'original_residue': row['residue'],
                            'side': side, 'projection_residue': event[0], 'projection_modulus': event[1]})
    final = [(rp, rn + tuple(masks['R']), sp, sn + tuple(masks['S'])) for rp, rn, sp, sn in components
             if volume(rp, rn + tuple(masks['R'])) * volume(sp, sn + tuple(masks['S'])) > 0]
    need(final, 'positive supported mixture')
    unit_events = [(row['residue'], row['modulus']) for row in units]
    star_events = low_events + masks['R'] + masks['S']
    true_mass = volume((), unit_events)
    component_masses = [volume(rp, rn) * volume(sp, sn) for rp, rn, sp, sn in final]
    star_mass = sum(component_masses, F())
    need(star_mass == volume((), star_events) and 0 < star_mass <= true_mass,
         'mixture equals projected supported survivor')
    for rp, rn, sp, sn in final:
        for row in units:
            qr = volume(rp + ((row['residue'] % row['R'], row['R']),), rn)
            qs = volume(sp + ((row['residue'] % row['S'], row['S']),), sn)
            need(qr * qs == 0, 'every component avoids every actual original unit')
    budget = bounds(cutoff, data['old_primes'])
    need(true_mass - star_mass <= budget['E'], 'actual supported mass loss within infinite tail bound')
    query_results, weighted_loss = [], F()
    seen = set()
    old_period = data['old_source']['period']
    for row in data['test_originals']:
        m, a, weight = row['modulus'], row['residue'], F(row['weight'])
        need(type(m) is int and m > 1 and m % 2 == 1 and m not in seen
             and type(a) is int and 0 <= a < m and 0 <= weight <= 616, 'distinct original test labels and allowed weights')
        seen.add(m)
        old = part(m, data['old_primes'])
        rr, ss = part(m, data['R']), part(m, data['S'])
        need(old * rr * ss == m and old_period % old == 0, 'test factorization resolved on one fixed old source')
        old_mass = sum((v for x, v in enumerate(source_weights) if x % old == a % old), F())
        event = a % (rr * ss), rr * ss
        exact = volume((event,), unit_events)
        direct_star = volume((event,), star_events)
        mixture = sum((volume(rp + ((a % rr, rr),), rn) * volume(sp + ((a % ss, ss),), sn)
                       for rp, rn, sp, sn in final), F())
        need(direct_star == mixture <= exact, 'all queries use the same component mixture and supported inclusion')
        loss = weight * old_mass * (exact - mixture)
        weighted_loss += loss
        query_results.append({'modulus': m, 'residue': a, 'weight': str(weight), 'old_mass': str(old_mass),
                              'true_outside_response': str(exact), 'mixture_outside_response': str(mixture),
                              'weighted_unnormalized_loss': str(loss)})
    need(0 < weighted_loss <= budget['response'], 'nonzero simultaneous response loss within inventory-independent bound')
    if cutoff == 0:
        need(len(final) == 1 and star_mass >= F(1018473977, 1252204800), 'uniform single-product restriction')
    if cutoff == 12:
        need(any(merge(a, b) is not None and a[1] != b[1] for a in rtests for b in rtests),
             'finite control exercises genuinely nested low R cylinders')
        need({row['side'] for row in assignments} == {'R', 'S'}, 'finite control exercises both high-tail assignments')
        need(true_mass - star_mass < F(1, 10 ** 15) and weighted_loss < F(1, 10 ** 10),
             'actual high-cutoff control meets both quantitative thresholds')
    return {'cutoff': cutoff, 'low_original_count': len(low), 'high_original_count': len(high),
            'R_membership_atom_count': len(atoms), 'component_count': len(final),
            'component_masks': [{'R_positive': rp, 'R_negative': rn, 'S_positive': sp, 'S_negative': sn,
                                  'weight': str(w)} for (rp, rn, sp, sn), w in zip(final, component_masses)],
            'tail_assignments': assignments, 'true_unit_survivor_mass': str(true_mass),
            'supported_mixture_mass': str(star_mass), 'actual_mass_loss': str(true_mass - star_mass),
            'weighted_response_loss': str(weighted_loss), 'queries': query_results,
            'universal_bounds': {k: str(v) for k, v in budget.items()}}


def verify(input_dir):
    raw = (Path(input_dir) / INPUT).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PIN, 'pinned actual input')
    data = json.loads(raw)
    need(data['schema'] == 'supported-unit-mixture-input-v1' and data['R'] == [23] and data['S'] == [29, 31], 'declared groups')
    units, seen = [], set()
    for row in data['unit_originals']:
        m, a = row['modulus'], row['residue']
        need(type(m) is int and m > 1 and m % 2 == 1 and m not in seen and type(a) is int and 0 <= a < m,
             'distinct actual unit numerical moduli and fixed phases')
        seen.add(m)
        r, s = part(m, data['R']), part(m, data['S'])
        need(r * s == m, 'unit old cofactor is one')
        units.append({**row, 'R': r, 'S': s, 'exponents': [exponent(m, p) for p in (23, 29, 31)]})
    source_weights = [F(v) for v in data['old_source']['weights']]
    period = data['old_source']['period']
    need(len(source_weights) == period and sum(source_weights) == 1
         and all(0 <= v <= F(27, 2 * period) for v in source_weights), 'one normalized old source with the claimed Haar domination')
    need(prod(F(p, p - 1) for p in data['old_primes']) == F(323323, 110592), 'complete old reciprocal inventory')
    r_lower = 1 - F(1, 22) - F(45, 10648)
    s_lower = 1 - F(59, 840) - F(26071, 352800)
    need(r_lower == F(10119, 10648) and s_lower == F(301949, 352800)
         and r_lower * s_lower == F(1018473977, 1252204800) > F(8133, 10000), 'strict universal product constant')
    b12 = bounds(12, data['old_primes'])
    need(b12['component_bound'] == 2017 and b12['E'] < F(1, 10 ** 15)
         and b12['response'] < F(1, 10 ** 10), 'universal H12 thresholds')
    for coeff, q in (([F(), F(1, 2), F(1, 2)], 23), ([F(1), F(2), F(1)], 29),
                     ([F(), F(23, 44), F(45, 44), F(1, 2)], 23),
                     ([F(4), F(59, 6), F(47, 6), F(13, 6), F(1, 6)], 29)):
        need(tail(coeff, q, 12) == poly_value(coeff, 13) * F(1, q) ** 13 + tail(coeff, q, 13),
             'exact geometric-tail recurrence')
    cases = [decomposition(data, units, cutoff, source_weights) for cutoff in data['cutoffs']]
    return {'schema': 'supported-unit-mixture-result-v1', 'input_sha256': PIN,
            'unit_original_count': len(units), 'test_original_count': len(data['test_originals']),
            'universal_product_lower': str(r_lower * s_lower),
            'universal_H12': {k: str(v) for k, v in b12.items()}, 'controls': cases,
            'scope': 'Exact scalar infinite tails and finite actual supported decompositions/queries. No full outside-period enumeration, source producer, optimizer, geometry or Lean run. Universal support and inventory-independent estimates follow the separate ordinary proof; transport capacity is not inferred.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.input_dir)
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    else:
        need(encoded == Path(__file__).with_suffix('.json').read_text(), 'retained result mismatch')
    print(json.dumps({'unit_originals': result['unit_original_count'], 'test_originals': result['test_original_count'],
                      'product_lower': result['universal_product_lower'],
                      'H12_components_bound': result['universal_H12']['component_bound'],
                      'H12_mass_loss_bound': result['universal_H12']['E'],
                      'H12_response_bound': result['universal_H12']['response'],
                      'actual_components': [c['component_count'] for c in result['controls']]}, indent=2))


if __name__ == '__main__':
    main()
