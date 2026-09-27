#!/usr/bin/env python3
"""Exact literal modulus-5/15 branch certificate for a six-vertex frontier.

Python >=3.10, standard library only. Input is the Chapter25 certificate JSON.
This checks finite rational arithmetic; the all-height probability transfer,
actual-pure induction and arbitrary-cutoff identity are ordinary proofs.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import isqrt, prod
from pathlib import Path
import json
import sys

if not __debug__:
    raise SystemExit('Run without -O: assertions are certificate checks.')
if sys.version_info < (3, 10):
    raise SystemExit('Python 3.10 or newer is required.')

TOTAL = F(187, 384)
SUPPORTS = tuple(range(1, 32))
FULL = 31
SPECIAL_FEES = {5: F(7, 24), 7: F(1, 8), 11: F(1, 24), 13: F(1, 48)}


def fee(q):
    return SPECIAL_FEES.get(q, F(1, 2 ** ((q - 1) // 2)))


def prime(q):
    return q >= 2 and all(q % d for d in range(2, isqrt(q) + 1))


def disjoint_families():
    """Enumerate at most five support subsets; do not use the Z recurrence."""
    result = []
    for size in range(6):
        for family in combinations(SUPPORTS, size):
            union = 0
            for support in family:
                if union & support:
                    break
                union |= support
            else:
                result.append((family, union))
    assert len(result) == 203
    return result


FAMILIES = disjoint_families()


def support_products(coordinate_caps):
    return [F(0)] + [
        prod(coordinate_caps[i] for i in range(5) if support >> i & 1)
        for support in SUPPORTS
    ]


def residuals(v):
    z = [F(1)] + [F(0)] * 31
    for coordinates in SUPPORTS:
        first = coordinates & -coordinates
        z[coordinates] = z[coordinates ^ first] - sum(
            v[support] * z[coordinates ^ support]
            for support in SUPPORTS
            if support & coordinates == support and support & first
        )
        direct = sum(
            (-1) ** len(family) * prod(v[support] for support in family)
            for family, union in FAMILIES
            if union & coordinates == union
        )
        assert z[coordinates] == direct
    return z


def evaluate(products, shallow):
    z = residuals(shallow)
    assert all(value > 0 for value in z)
    load = sum(products[support] * z[FULL ^ support] for support in SUPPORTS)
    cost = load / (6 * z[FULL])
    return z, load, cost


def one_tuple(children):
    charge = sum(map(fee, children), F())
    expense = TOTAL - charge
    assert expense >= 0
    density = tuple(
        1 - F(1, q - 1) - (F(3, 10) if q == 5 else F(2, q - 1)) * expense
        for q in children
    )
    assert all(d > 0 for d in density)
    caps = tuple(1 / ((q - 1) * d) for q, d in zip(children, density))
    products = support_products(caps)
    baseline_shallow = [F(0)] + [
        products[support] * (1 + int(support.bit_count() > 1))
        for support in SUPPORTS
    ]
    baseline_z = residuals(baseline_shallow)
    delta = F(4, 5) * caps[0]
    scale = 1 + delta

    improved_density = (density[0] + F(1, 5),) + density[1:]
    improved_caps = (1 / (4 * improved_density[0]),) + caps[1:]
    assert improved_caps[0] == caps[0] / scale
    improved_products = support_products(improved_caps)
    improved_shallow = [F(0)] + [
        improved_products[support] * (1 + int(support.bit_count() > 1))
        for support in SUPPORTS
    ]
    zi, li, ki = evaluate(improved_products, improved_shallow)

    removed_shallow = baseline_shallow.copy()
    removed_shallow[1] = caps[0] / 5
    zr, lr, kr = evaluate(products, removed_shallow)
    assert ki == kr < charge
    for coordinates in range(32):
        if coordinates & 1:
            assert zi[coordinates] * scale == zr[coordinates]
            assert zr[coordinates] == (
                baseline_z[coordinates] + delta * baseline_z[coordinates ^ 1]
            )
        else:
            assert zi[coordinates] == zr[coordinates] == baseline_z[coordinates]
    assert li * scale == lr
    return {
        'children': children,
        'fee': str(charge),
        'outside_expense': str(expense),
        'baseline_density': list(map(str, density)),
        'baseline_caps': list(map(str, caps)),
        'delta': str(delta),
        'scale_lambda': str(scale),
        'missing_modulus5': {
            'density': list(map(str, improved_density)),
            'caps': list(map(str, improved_caps)),
            'nonempty_residuals': list(map(str, zi[1:])),
            'minimum_residual': str(min(zi[1:])),
            'Z': str(zi[FULL]),
            'L': str(li),
        },
        'missing_or_redundant_modulus15': {
            'singleton5_shallow_cap': str(removed_shallow[1]),
            'nonempty_residuals': list(map(str, zr[1:])),
            'minimum_residual': str(min(zr[1:])),
            'Z': str(zr[FULL]),
            'L': str(lr),
        },
        'same_kernel_bound': str(ki),
        'fee_margin': str(charge - ki),
        'cost_over_fee': str(ki / charge),
        'all_residual_scaling_identities_at_t1': True,
    }


def certificate(frontier_path):
    raw = frontier_path.read_bytes()
    frontier = json.loads(raw)
    tuples = [tuple(row) for row in frontier['remaining_root3_tuples']]
    assert frontier['remaining_root3_tuple_count'] == len(tuples) == 50
    assert len(set(tuples)) == len(tuples)
    assert all(
        len(row) == 5 and tuple(sorted(set(row))) == row and row[:2] == (5, 7)
        and all(isinstance(q, int) and prime(q) for q in row)
        for row in tuples
    )
    rows = [one_tuple(row) for row in sorted(tuples)]
    worst = max(rows, key=lambda row: F(row['cost_over_fee']))
    assert worst['children'] == (5, 7, 11, 13, 17)
    assert F(worst['same_kernel_bound']) == F(328823862662848, 743415381507325)
    assert F(worst['fee_margin']) == F(23270380014150311, 570943012997625600)
    assert F(worst['cost_over_fee']) == F(36076675217866752, 39401015219888225)
    return {
        'scope': (
            'Exact t=1 conditional-kernel arithmetic for the 50 original root3 '
            'five-child tuples listed by the supplied Chapter25 certificate. '
            'Literal modulus5 absence, modulus15 absence, or mod5 agreement '
            'give two equivalent cap modifications. The ordinary proof supplies '
            'the actual-pure induction, all-height transfer and arbitrary-t identity. '
            'No unrestricted noncoverage or Lean certification is asserted.'
        ),
        'frontier_input_sha256': sha256(raw).hexdigest(),
        'conservative_total_fee_F': str(TOTAL),
        'tuple_count': len(rows),
        'literal_branches': [
            'original modulus5 absent',
            'original modulus15 absent',
            'both original moduli5 and15 present with equal residues modulo5',
        ],
        'distinct_cap_vectors_per_tuple': 2,
        'nonempty_coordinate_residuals_per_vector': 31,
        'disjoint_support_family_count': len(FAMILIES),
        'worst_ratio': worst['cost_over_fee'],
        'worst_children': worst['children'],
        'rows': rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--frontier', type=Path, required=True,
                        help='Chapter25 six_vertex_conditional_kernel_certificate.json')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = certificate(args.frontier)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print('PASS: 50 child tuples, two equivalent vectors, all 31 residuals each.')
    print('Worst kernel/fee:', result['worst_ratio'])


if __name__ == '__main__':
    main()
