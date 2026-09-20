#!/usr/bin/env python3
"""Portable exact certificate for six-vertex block fees and their finite frontier.

Python 3.10+; standard library only; no input data files. The probability,
descendant-induction, and all-large analytic arguments remain ordinary
mathematical premises, not conclusions of this finite calculation.
"""
import argparse
import json
import sys
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import comb, isqrt, lcm, prod
from pathlib import Path

TOTAL = F(187, 384)
BOUNDARY = 43
TAILS = (((5, 7, 11, 13), 75), ((5, 7, 11, 17), 51),
         ((5, 7, 13, 17), 67), ((5, 7, 13, 19), 51))


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def fee(q):
    return {5: F(7, 24), 7: F(1, 8), 11: F(1, 24), 13: F(1, 48)}.get(
        q, F(1, 2 ** ((q - 1) // 2)))


def caps(pp, expense):
    return tuple(1 / (3 - F(6, 5) * expense) if q == 5
                 else 1 / (q - 2 - 2 * expense) for q in pp)


@lru_cache(None)
def families(mask):
    """Every family of disjoint nonempty supports inside mask, once."""
    if not mask:
        return ((),)
    bit = mask & -mask
    rest = mask ^ bit
    out = list(families(rest))
    part = rest
    while True:
        support = part | bit
        out.extend((support,) + tail for tail in families(mask ^ support))
        if not part:
            break
        part = (part - 1) & rest
    return tuple(out)


def add(a, b):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return out


def scale(a, k):
    return [k * x for x in a]


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def polynomial_coefficients():
    """Check c_n(t) symbolically against direct set-partition expansion."""
    cs = [[1]]
    for n in range(1, 6):
        value = mul([0, -1], cs[n - 1])
        for r in range(2, n + 1):
            value = add(value, scale(mul([-1, -1], cs[n - r]),
                                     comb(n - 1, r - 1)))
        direct = [0] * (n + 1)
        mask = (1 << n) - 1
        for family in families(mask):
            if sum(family) != mask:
                continue
            term = [1]
            for s in family:
                term = mul(term, [-int(s.bit_count() > 1), -1])
            direct = add(direct, term)
        assert value == direct
        cs.append(value)
    assert cs[5] == [9, 9, -25, -15, 10, -1]
    return cs


def at(poly, t):
    return sum(c * t ** i for i, c in enumerate(poly))


def elementary(xs):
    es = [F(1)] + [F(0)] * len(xs)
    for x in xs:
        for i in range(len(xs), 0, -1):
            es[i] += x * es[i - 1]
    return es


def support_weights(bs):
    return [F(0)] + [prod((bs[i] for i in range(5) if s >> i & 1),
                          start=F(1)) for s in range(1, 32)]


def residuals(v):
    out = [F(1)] * 32
    for mask in range(1, 32):
        bit = mask & -mask
        rest = mask ^ bit
        out[mask] = out[rest]
        part = rest
        while True:
            support = part | bit
            out[mask] -= v[support] * out[mask ^ support]
            if not part:
                break
            part = (part - 1) & rest
    return out


def literal(v, mask):
    return sum((-1) ** len(family) * prod((v[s] for s in family), start=F(1))
               for family in families(mask))


def kernel(bs, t, coefficients, direct=False):
    sw = support_weights(bs)
    es_by_mask = [elementary(tuple(bs[i] for i in range(5) if mask >> i & 1))
                  for mask in range(32)]
    cn = [at(p, t) for p in coefficients]
    dn = [at([i * p[i] for i in range(1, len(p))], t)
          for p in coefficients]
    zs = [sum(c * e for c, e in zip(cn, es)) for es in es_by_mask]
    values = [(t + int(s.bit_count() > 1)) * sw[s] for s in range(32)]
    assert zs == residuals(values)
    if direct:
        assert zs == [literal(values, mask) for mask in range(32)]
    load = sum(sw[s] * zs[31 ^ s] for s in range(1, 32))
    assert load == -sum(d * e for d, e in zip(dn, es_by_mask[31]))
    strict = min(zs) > 0
    return {'t': t, 'strict': strict, 'residuals': list(map(str, zs)),
            'Z': str(zs[31]), 'L': str(load),
            'K3': str(load / (2 * 3 ** t * zs[31])) if strict else None}


def non3(pp, small, charge, bound):
    # All proxy children are >=43; this missing prime is <=19.
    parent = next(q for q in range(5, 43) if prime(q) and q not in small)
    assert parent not in pp and parent < 43
    t = bound['t']
    cp = F(3, 10) if parent == 5 else F(2, parent - 1)
    factor = F(2, parent - 1) * F(3, parent) ** t / cp
    normalized = factor * F(bound['K3'])
    assert t >= 1 and normalized < charge
    return {'minimum_legal_parent': parent, 't': t,
            'normalized_Kp_over_cp': str(normalized),
            'ratio_to_charge': str(normalized / charge),
            'margin': str(charge - normalized)}


def kr(pp, charge, total_budget=TOTAL):
    """Exact continuous KR14 minimum by forced supports and remaining corners."""
    expense = total_budget - charge
    bs = caps(pp, expense)
    sw = support_weights(bs)
    w = [sw[s] if s.bit_count() > 1 else F(0) for s in range(32)]
    low = residuals(w)
    high_v = [w[s] + sw[s] for s in range(32)]
    high = residuals(high_v)
    assert min(high) > 0 and F(1, 3) < charge < F(2, 3)
    assert high == [literal(high_v, mask) for mask in range(32)]
    margins = {s: F(1, 3) * high[31 ^ s] - (charge - F(1, 3)) * low[31 ^ s]
               for s in range(1, 32)}
    forced = [s for s in margins if margins[s] > 0]
    free = [s for s in margins if margins[s] <= 0]
    forced_vertex = sum(1 << (s - 1) for s in forced)
    den = prod(x.denominator for x in bs)
    weighted_den = lcm(3, charge.denominator)
    a = weighted_den // 3
    c = charge.numerator * (weighted_den // charge.denominator) - a
    terms = []
    for family in families(31):
        coefficient = (-1) ** len(family) * prod((sw[s] for s in family), start=F(1)) * den
        assert coefficient.denominator == 1
        terms.append((family, int(coefficient)))
    best = arg = pair = None
    for corner in range(1 << len(free)):
        vertex = forced_vertex + sum(1 << (s - 1) for i, s in enumerate(free)
                                      if corner >> i & 1)
        z1 = z2 = 0
        for family, coefficient in terms:
            p1 = p2 = coefficient
            for s in family:
                bit = (vertex >> (s - 1)) & 1
                old = int(s.bit_count() > 1)
                p1 *= old + bit
                p2 *= old + 1 - bit
            z1 += p1
            z2 += p2
        score = a * z1 + c * z2
        if best is None or score < best:
            best, arg, pair = score, vertex, (F(z1, den), F(z2, den))
    y = [sw[s] * ((arg >> (s - 1)) & 1) if s else F(0) for s in range(32)]
    assert pair == (residuals([w[s] + y[s] for s in range(32)])[31],
                    residuals([w[s] + sw[s] - y[s] for s in range(32)])[31])
    load = sum(sw[s] * low[31 ^ s] for s in range(1, 32))
    gap = F(best, den * weighted_den) - load / 6
    return {'children': pp, 'charge': str(charge), 'expense': str(expense),
            'total_fee_budget': str(total_budget),
            'caps': list(map(str, bs)), 'residuals_w_plus_b': list(map(str, high)),
            'forced_derivative_margins': {str(s): str(margins[s]) for s in forced},
            'free_supports': free, 'corners_checked': 1 << len(free),
            'minimum_vertex': arg, 'Z_first': str(pair[0]), 'Z_second': str(pair[1]),
            'L0': str(load), 'gap': str(gap), 'passes': gap > 0}


def main():
    if not __debug__:
        raise SystemExit('Run without -O: assertions are certificate checks.')
    if sys.version_info < (3, 10):
        raise SystemExit('Python 3.10 or newer is required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    coefficients = polynomial_coefficients()
    assert len(families(31)) == len(set(families(31))) == 203
    small_primes = tuple(q for q in range(5, BOUNDARY) if prime(q))
    assert len(small_primes) == 11
    rows = []
    partition = {}
    for j in range(1, 6):
        counts = {'rows': 0, 'kernel_paid': 0, 'KR_paid': 0, 'unpaid': 0}
        for small in combinations(small_primes, j):
            pp = small + (43, 45, 47, 49)[:5 - j]
            charge = sum(map(fee, small), F(0))
            bs = caps(pp, TOTAL - charge)
            tested = []
            selected = None
            first_nonstrict = None
            for t in range(25):
                bound = kernel(bs, t, coefficients)
                if not bound['strict']:
                    first_nonstrict = t
                    break
                tested.append(bound)
                if t >= 1 and F(bound['K3']) < charge:
                    selected = bound
                    break
            row = {'children': pp, 'fixed_small_children': small, 'small_count': j,
                   'charge': str(charge), 'expense': str(TOTAL - charge),
                   'caps': list(map(str, bs))}
            if selected is not None:
                selected = kernel(bs, selected['t'], coefficients, direct=True)
                row.update({'method': 'kernel', 'kernel': selected,
                            'kernel_fee_margin': str(charge - F(selected['K3']))})
                counts['kernel_paid'] += 1
            else:
                assert first_nonstrict == 2 and len(tested) == 2
                selected = kernel(bs, 1, coefficients, direct=True)
                kc = kr(pp, charge)
                row.update({'method': 'KR' if kc['passes'] else 'unpaid',
                            'kernel': selected, 'kernel_t0': tested[0],
                            'first_nonstrict': first_nonstrict, 'KR': kc})
                counts['KR_paid' if kc['passes'] else 'unpaid'] += 1
            row['non3'] = non3(pp, small, charge, selected)
            counts['rows'] += 1
            rows.append(row)
        partition[str(j)] = counts
    assert len(rows) == 1023
    assert sum(r['method'] == 'kernel' for r in rows) == 972
    assert sum(r['method'] == 'KR' for r in rows) == 13
    assert sum(r['method'] == 'unpaid' for r in rows) == 38
    initial_failures = [r for r in rows if r['method'] != 'kernel']
    assert len(initial_failures) == 51
    assert sum(r['KR']['corners_checked'] for r in initial_failures) == 5286
    unpaid_proxy = {tuple(r['fixed_small_children']) for r in rows
                    if r['method'] == 'unpaid' and r['small_count'] < 5}
    assert unpaid_proxy == {s for s, _ in TAILS}

    tails = []
    finite = []
    for small, threshold in TAILS:
        charge = sum(map(fee, small), F(0))
        endpoint = kr(small + (threshold,), charge)
        assert endpoint['passes']
        tails.append({'fixed_small_children': small, 'Q_tail': threshold,
                      'charge': str(charge), 'certificate': endpoint})
        for q in range(43, threshold):
            if not prime(q):
                continue
            pp = small + (q,)
            full_charge = charge + fee(q)
            point = kr(pp, full_charge)
            bs = caps(pp, TOTAL - full_charge)
            b0 = kernel(bs, 0, coefficients, direct=True)
            b1 = kernel(bs, 1, coefficients, direct=True)
            b2 = kernel(bs, 2, coefficients, direct=True)
            assert b0['strict'] and b1['strict'] and not b2['strict']
            assert F(b0['K3']) >= full_charge and F(b1['K3']) >= full_charge
            assert not point['passes']
            point['kernel_controls'] = [b0, b1, b2]
            point['non3'] = non3(pp, pp, full_charge, b1)
            finite.append(point)
    assert len(finite) == 17
    old_unpaid = [tuple(r['children']) for r in rows
                  if r['method'] == 'unpaid' and r['small_count'] == 5]
    assert len(old_unpaid) == 34
    remaining_before = sorted(old_unpaid + [tuple(r['children']) for r in finite])
    assert len(remaining_before) == len(set(remaining_before)) == 51
    # The odd-tail fee majorant included composite 21. Removing its one
    # geometric term is a valid universal saving; all older looser caps stand.
    assert 21 == 3 * 7 and not prime(21)
    sharper_total = TOTAL - F(1, 2 ** ((21 - 1) // 2))
    assert sharper_total == F(1493, 3072)
    sharper_tail = kr((5, 7, 11, 13, 73), F(23, 48), sharper_total)
    assert sharper_tail['expense'] == str(F(7, 1024))
    assert sharper_tail['passes'] and F(sharper_tail['gap']) == F(
        4357883692674437, 35313726266855802000)
    newly_paid = [pp for pp in remaining_before if pp[:4] == (5, 7, 11, 13) and pp[4] >= 73]
    assert newly_paid == [(5, 7, 11, 13, 73)]
    remaining = [pp for pp in remaining_before if pp not in newly_paid]
    assert len(remaining) == 50
    assert all(pp[:2] == (5, 7) for pp in remaining)
    worst_non3_exception = max(initial_failures, key=lambda r: F(r['non3']['ratio_to_charge']))
    assert tuple(worst_non3_exception['children']) == (5, 7, 13, 17, 19)
    assert F(worst_non3_exception['non3']['ratio_to_charge']) == F(
        2016141231967518654464, 5168427017630317131405)
    out = {
        'scope': 'Finite exact certificate under the actual descendant-density invariant. '
                 'The 50 remaining entries are child-prime sets with unrestricted finite '
                 'original heights/residues, not 50 finite AP systems or covering examples.',
        'small_primes': small_primes, 'boundary': BOUNDARY,
        'coefficient_polynomials_ascending_powers_t': coefficients,
        'disjoint_support_family_count': 203,
        'partition': partition, 'boundary_rows': 1023, 'kernel_paid': 972,
        'additional_KR_paid': 13, 'initial_KR_corner_count': 5286,
        'max_selected_kernel_cutoff': max(r['kernel']['t'] for r in rows),
        'non3_boundary_checks': len(rows), 'non3_additional_finite_checks': len(finite),
        'worst_non3_initial_kernel_exception': {
            'children': worst_non3_exception['children'],
            'charge': worst_non3_exception['charge'],
            'K3_t1': worst_non3_exception['kernel']['K3'],
            **worst_non3_exception['non3']},
        'tails': tails, 'finite_tail_rows': finite,
        'frontier_before_composite21_saving': remaining_before,
        'composite21_saving': {'removed_odd_integer': 21,
                              'saved_term': str(F(1, 1024)),
                              'total_fee_budget': str(sharper_total),
                              'Q_tail': 73, 'certificate': sharper_tail,
                              'newly_paid_tuples': newly_paid,
                              'root3_reserve': str(F(1, 2) - sharper_total)},
        'remaining_root3_tuple_count': len(remaining), 'remaining_root3_tuples': remaining,
        'all_large_branch': 'The ordinary k=5 analytic theorem applies at min child 43; '
                            'this program does not replace its unbounded proof.',
        'tail_threshold_scope': 'Sufficient odd proxy endpoints, with fixed small-child '
                                'charges and outside budgets; no smallest-threshold claim.',
        'rows': rows,
    }
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print('PASS: 1023 boundary rows; 972 kernel and 13 additional KR fees; '
          'four infinite tails; 17 finite additions; composite-21 saving; all non-3 checks.')
    print('Remaining root-3 child-prime sets:', len(remaining))


if __name__ == '__main__':
    main()
