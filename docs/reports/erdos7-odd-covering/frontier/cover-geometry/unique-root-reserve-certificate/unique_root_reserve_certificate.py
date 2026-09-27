#!/usr/bin/env python3
"""Exact certificate for the unique root-3 reserve and shared descendant budget.

Python 3.10+; standard library only. Read the Chapter 25 JSON explicitly via
--inherited. Arithmetic uses the Chapter 25 disjoint-support expansion, copied
here with expense and blocker target as separate arguments. No code is loaded
from another file. Probability and graph-recursion implications are the
ordinary arguments of the accompanying chapter, not Lean-verified claims.
"""
import argparse
import hashlib
import json
import sys
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt, lcm, prod
from pathlib import Path

INHERITED_SHA256 = '5fc133a5826747a04787e13a6ddc92c311d065cd54357a18c9f0e414bb45a571'
FSTAR = F(1493, 3072)
RESERVE = F(43, 3072)
PARTITIONS = {
    (5, 7, 11, 13, 41): (F(0), F(1, 2), F(1)),
    (5, 7, 11, 17, 29): (F(0), F(1, 8), F(1, 4), F(1, 2), F(1)),
    (5, 7, 11, 17, 31): (F(0), F(1, 2), F(1)),
    (5, 7, 13, 17, 29): (F(0), F(1, 4), F(1, 2), F(1)),
    (5, 7, 13, 17, 31): (F(0), F(1, 2), F(1)),
    (5, 7, 13, 19, 29): (F(0), F(1, 2), F(1)),
    (5, 7, 17, 19, 23): (F(0), F(1, 2), F(1)),
}
EXPECTED_REMAINING = {
    (5, 7, 11, 13, q) for q in (17, 19, 23, 29, 31, 37)
} | {
    (5, 7, 11, 17, q) for q in (19, 23)
} | {(5, 7, 11, 19, 23)} | {
    (5, 7, 13, 17, q) for q in (19, 23)
} | {(5, 7, 13, 19, 23)}


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


def kr(pp, expense, target):
    """Exact continuous KR14 minimum by forced supports and remaining corners."""
    assert expense >= 0
    bs = caps(pp, expense)
    sw = support_weights(bs)
    w = [sw[s] if s.bit_count() > 1 else F(0) for s in range(32)]
    low = residuals(w)
    high_v = [w[s] + sw[s] for s in range(32)]
    high = residuals(high_v)
    assert min(high) > 0 and F(1, 3) < target < F(2, 3)
    assert high == [literal(high_v, mask) for mask in range(32)]
    margins = {s: F(1, 3) * high[31 ^ s] - (target - F(1, 3)) * low[31 ^ s]
               for s in range(1, 32)}
    forced = [s for s in margins if margins[s] > 0]
    free = [s for s in margins if margins[s] <= 0]
    forced_vertex = sum(1 << (s - 1) for s in forced)
    den = prod(x.denominator for x in bs)
    weighted_den = lcm(3, target.denominator)
    a = weighted_den // 3
    c = target.numerator * (weighted_den // target.denominator) - a
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
    return {'children': pp, 'target': str(target), 'expense': str(expense),
            'caps': list(map(str, bs)), 'residuals_w_plus_b': list(map(str, high)),
            'derivative_margins': {str(s): str(margins[s]) for s in margins},
            'forced_supports': forced,
            'free_supports': free, 'corners_checked': 1 << len(free),
            'minimum_vertex': arg, 'Z_first': str(pair[0]), 'Z_second': str(pair[1]),
            'L0': str(load), 'gap': str(gap), 'passes': gap > 0}


def main():
    if not __debug__:
        raise SystemExit('Run without -O: assertions are certificate checks.')
    if sys.version_info < (3, 10):
        raise SystemExit('Python 3.10 or newer is required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inherited', type=Path, required=True,
                        help='Chapter 25 six_vertex_conditional_kernel_certificate.json')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw = args.inherited.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == INHERITED_SHA256, 'Inherited Chapter 25 input differs from the pinned certificate.'
    inherited = json.loads(raw)
    assert F(inherited['composite21_saving']['total_fee_budget']) == FSTAR
    children = [tuple(pp) for pp in inherited['remaining_root3_tuples']]
    assert inherited['remaining_root3_tuple_count'] == len(children) == 50
    assert children == sorted(set(children))
    assert all(len(pp) == 5 and pp == tuple(sorted(set(pp))) and
               pp[:2] == (5, 7) and all(prime(q) for q in pp) for pp in children)
    assert FSTAR == sum((fee(q) for q in (5, 7, 11, 13)), F(0)) + F(1, 128) - F(1, 1024)
    assert RESERVE == F(1, 2) - FSTAR
    assert len(families(31)) == len(set(families(31))) == 203

    fixed = []
    for pp in children:
        C = sum(map(fee, pp), F(0))
        E, M = FSTAR - C, C + RESERVE
        assert E > 0 and M == F(1, 2) - E
        result = kr(pp, E, M)
        fixed.append(dict(child_fees=str(C), **result))
    fixed_paid = {tuple(r['children']) for r in fixed if r['passes']}
    fixed_unpaid = {tuple(r['children']) for r in fixed if not r['passes']}
    assert len(fixed_paid) == 31 and len(fixed_unpaid) == 19
    assert all(F(r['gap']) != 0 for r in fixed)
    assert sum(r['corners_checked'] for r in fixed) == 12440
    assert set(PARTITIONS) <= fixed_unpaid

    shared = []
    for pp, ratios in PARTITIONS.items():
        C = sum(map(fee, pp), F(0))
        E, M = FSTAR - C, C + RESERVE
        endpoints = [E * t for t in ratios]
        assert endpoints[0] == 0 and endpoints[-1] == E
        assert all(lo < hi for lo, hi in zip(endpoints, endpoints[1:]))
        intervals = []
        for lo, hi in zip(endpoints, endpoints[1:]):
            result = kr(pp, hi, M + lo)
            assert result['passes']
            intervals.append(dict(lo=str(lo), hi=str(hi), certificate=result))
        assert all(F(a['hi']) == F(b['lo']) for a, b in zip(intervals, intervals[1:]))
        shared.append(dict(children=pp, child_fees=str(C), outside_budget=str(E),
                           base_target=str(M), endpoint_ratios=list(map(str, ratios)),
                           intervals=intervals, covers_full_budget_interval=True))
    cells = [c for row in shared for c in row['intervals']]
    assert len(cells) == 17
    assert sum(c['certificate']['corners_checked'] for c in cells) == 3688
    paid = fixed_paid | set(PARTITIONS)
    remaining = set(children) - paid
    assert len(paid) == 38 and len(remaining) == 12 and remaining == EXPECTED_REMAINING
    minimum_fixed = min((r for r in fixed if r['passes']), key=lambda r: F(r['gap']))
    assert tuple(minimum_fixed['children']) == (5, 7, 11, 13, 43)
    assert F(minimum_fixed['gap']) == F(
        16315593837048237831107322855008746701,
        53492794872230672809615562047262440816640)
    minimum_shared = min(cells, key=lambda c: F(c['certificate']['gap']))
    assert tuple(minimum_shared['certificate']['children']) == (5, 7, 11, 13, 41)
    assert (F(minimum_shared['lo']), F(minimum_shared['hi'])) == (F(0), F(7167, 2097152))
    assert F(minimum_shared['certificate']['gap']) == F(
        100940323747930477708823537562792377,
        5501376123406464765500334715636798193664)
    result = {
        'scope': 'Unique root-3 core only, with all other graph blocks carrying '
                 'established recursive fees. The global prime-fee bound is Fstar; '
                 'the root blocker target is a separate quantity. The twelve '
                 'remaining entries are prime sets with arbitrary original finite '
                 'heights/residues, not covering examples or failed AP realizations.',
        'inherited_sha256': digest,
        'inherited_root3_tuple_count': 50,
        'Fstar': str(FSTAR), 'root_reserve': str(RESERVE),
        'disjoint_support_family_count': 203,
        'fixed_positive_count': 31, 'fixed_nonpositive_count': 19,
        'fixed_corner_count': 12440,
        'shared_additional_count': 7, 'shared_interval_count': 17,
        'shared_corner_count': 3688,
        'total_residual_count': 32 * (len(fixed) + len(cells)),
        'total_derivative_margin_count': 31 * (len(fixed) + len(cells)),
        'total_corner_count': 12440 + 3688,
        'paid_count': 38, 'remaining_count': 12,
        'paid_root3_tuples': sorted(paid),
        'remaining_root3_tuples': sorted(remaining),
        'minimum_fixed_positive_gap': {k: minimum_fixed[k] for k in ('children', 'gap')},
        'minimum_shared_positive_gap': dict(
            children=minimum_shared['certificate']['children'],
            lo=minimum_shared['lo'], hi=minimum_shared['hi'],
            gap=minimum_shared['certificate']['gap']),
        'fixed_budget_rows': fixed, 'shared_budget_rows': shared,
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in (
        'fixed_positive_count', 'shared_additional_count', 'shared_interval_count',
        'total_corner_count', 'paid_count', 'remaining_count')}, indent=2))


if __name__ == '__main__':
    main()
