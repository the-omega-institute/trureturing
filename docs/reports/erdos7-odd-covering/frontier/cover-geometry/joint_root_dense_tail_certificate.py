#!/usr/bin/env python3
"""Exact head and all-prime-tail arithmetic for the conditional-root bound.

This independent implementation uses direct low-product tuple enumeration
and five-variable rational automatic differentiation. It imports no oracle
attachment, source verifier, geometry table, or third-party package.
The conditional-label comparison and prime-product estimate are ordinary
mathematical premises specified in Chapter 32; this is not a Lean replay.
Python 3.10+; run from any directory with --output FILE.
"""
import argparse
from fractions import Fraction as Q
import json
from math import factorial, prod
from pathlib import Path
import sys

N = 5
PRIMES = (5, 7, 11, 13, 17)
THRESHOLDS = (0, 1, 3, 5, 7)
GAMMA = (Q(6, 5), Q(2), Q(2), Q(2), Q(2))
FSTAR = Q(1493, 3072)
EMAX = Q(67, 3072)
SIMPLE_GRADIENT = tuple(Q(n, 1000) for n in (288, 215, 73, 54, 25))
HEADS = ((5, 7, 11, 13, 17), (5, 7, 11, 13, 19),
         (5, 7, 11, 13, 23), (5, 7, 11, 13, 29),
         (5, 7, 11, 13, 31), (5, 7, 11, 17, 19))


class Jet:
    """A rational value and its five exact first partial derivatives."""
    def __init__(self, value, gradient=None):
        self.value = Q(value)
        self.gradient = tuple(map(Q, gradient)) if gradient is not None else (Q(0),) * N
        assert len(self.gradient) == N

    @staticmethod
    def lift(x):
        return x if isinstance(x, Jet) else Jet(x)

    def __add__(self, other):
        other = self.lift(other)
        return Jet(self.value + other.value, [a + b for a, b in zip(self.gradient, other.gradient)])

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.value, [-x for x in self.gradient])

    def __sub__(self, other):
        return self + (-self.lift(other))

    def __rsub__(self, other):
        return self.lift(other) + (-self)

    def __mul__(self, other):
        other = self.lift(other)
        return Jet(self.value * other.value,
                   [a * other.value + self.value * b for a, b in zip(self.gradient, other.gradient)])

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.value != 0
        return Jet(1 / self.value, [-a / self.value ** 2 for a in self.gradient])

    def __truediv__(self, other):
        return self * self.lift(other).reciprocal()

    def __rtruediv__(self, other):
        return self.lift(other) * self.reciprocal()


def low_product_tuples(arity, upper):
    if arity == 0:
        if upper >= 1:
            yield ()
        return
    for n in range(1, upper + 1):
        for rest in low_product_tuples(arity - 1, upper // n):
            yield (n,) + rest


def exact_hinge(previous, threshold):
    """E[(product X - threshold)+], with the infinite tail in E[product X]."""
    assert isinstance(threshold, int) and threshold >= 1
    mean = Jet(1)
    for p, cap in previous:
        mean *= 1 + cap / (p - 1)
    result, count = mean - threshold, 0
    for values in low_product_tuples(len(previous), threshold - 1):
        weight = Jet(1)
        for (p, cap), n in zip(previous, values):
            probability = 1 - cap / p if n == 1 else cap * Q(p - 1, p ** n)
            assert probability.value >= 0
            weight *= probability
        result += (threshold - prod(values)) * weight
        count += 1
    assert result.value >= 0
    return result, count


def evaluate(expenses):
    assert len(expenses) == N
    previous = [(3, Jet(2))]
    costs, denominators, caps, counts = [], [], [], []
    for i, (p, threshold, gamma, expense) in enumerate(zip(PRIMES, THRESHOLDS, GAMMA, expenses)):
        variable = Jet(expense, [int(j == i) for j in range(N)])
        denominator = p - 2 - threshold - gamma * variable
        cap = (p - 1) / denominator
        assert denominator.value > 0 and 0 < cap.value <= p
        numerator, count = exact_hinge(previous, threshold + 1)
        costs.append(numerator / denominator)
        denominators.append(denominator.value)
        caps.append(cap.value)
        counts.append(count)
        previous.append((p, cap))
    total = sum(costs, Jet(0))
    moment = Jet(1)
    for p, cap in previous:
        moment *= 1 + cap * Q(3 * p - 1, (p - 1) ** 2)
    assert counts == [0, 1, 7, 23, 61]
    return {'expenses': list(expenses), 'denominators': denominators,
            'auxiliary_caps': [Q(2)] + caps, 'low_product_tuple_counts': counts,
            'stage_costs': [c.value for c in costs], 'cost': total.value,
            'gradient': list(total.gradient), 'second_moment': moment.value}


def fee(p):
    return {5: Q(7, 24), 7: Q(1, 8), 11: Q(1, 24), 13: Q(1, 48)}.get(
        p, Q(1, 2 ** ((p - 1) // 2)))


def serialize(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {key: serialize(v) for key, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [serialize(v) for v in value]
    return value


def certificate():
    zero = evaluate([Q(0)] * N)
    corner = evaluate([EMAX] * N)
    assert zero['cost'] == Q(2379346060993228562427403831, 2659278071347311162498750000)
    assert zero['cost'] < Q(179, 200)
    assert corner['cost'] < Q(909, 1000)
    assert all(0 <= a < b < Q(1, 3) for a, b in zip(corner['gradient'], SIMPLE_GRADIENT))
    assert corner['second_moment'] == Q(3112461874161011540673, 47325920018794268621) < 66

    B, ell, exponent = 10000, 8, 7
    assert B >= 286 and ell >= 4 and 3 ** ell <= B and 2 * ell > exponent
    correction = Q(2 * ell ** 2 + 1, 2 * ell ** 2 - 1)
    terms = [Q(factorial(exponent), factorial(exponent - h) * ell ** h)
             for h in range(exponent + 1)]
    tau = correction ** exponent / B * Q(B, B - 3) ** 2 * sum(terms)
    tail_charge = 66 * tau
    assert tail_charge == Q(5214935802363444072691875, 218135012396331463923822592)
    assert tail_charge < Q(3, 125)
    assert Q(179, 200) + EMAX / 3 + Q(3, 125) < 1

    rows = []
    for head in HEADS:
        assert all(p >= r for p, r in zip(head, PRIMES))
        expense = FSTAR - sum(map(fee, head), Q(0))
        assert 0 < expense <= EMAX
        core = (1 - Q(179, 200)) / 2 - expense
        dense = (1 - Q(179, 200) - Q(3, 125)) / 2 - expense
        assert core > 0 and dense > 0
        rows.append({'head_children': head, 'outside_expense_upper_bound': expense,
                     'head_root_margin': core, 'dense_tail_root_margin': dense,
                     'additional_total_descendant_expense_coefficient': Q(5, 6)})
    expected = [Q(1269, 25600), Q(1219, 25600), Q(2363, 51200),
                Q(18729, 409600), Q(37433, 819200), Q(2357, 76800)]
    assert [r['head_root_margin'] for r in rows] == expected
    assert min(r['outside_expense_upper_bound'] for r in rows) > 0
    assert max(r['outside_expense_upper_bound'] for r in rows) == EMAX
    assert min(r['dense_tail_root_margin'] for r in rows) == Q(7177, 384000)

    return serialize({
        'schema': 'conditional-root-dense-tail-certificate-v1',
        'scope': 'Exact root-margin arithmetic for the prime-interaction component containing 3, with six specified heads and arbitrary finite additional prime sets above 10000, conditional on the actual descendant-domain invariant, proved other-root charges, conditional complete-label comparison, and the cited prime-product bound. Whole-family noncoverage additionally requires avoidance of every other component; Chapter 31 supplies this when every other graph block has at most seven vertices. No unrestricted odd-cover theorem or Lean verification is asserted.',
        'method': 'Direct low-product tuple enumeration with full exact means; five-variable rational automatic differentiation.',
        'external_verifier_imported': False, 'geometry_used': False,
        'prime_product_premise': {
            'source': 'Michael Schroeder, Noncoverage for Distinct Odd Moduli with at Most Three Prime Divisors, Lemma 8.2 (Explicit prime-product ratio)',
            'archive_sha256': '5956327277ac47dd6e98a0a38f2a785cd61e647560c7f6ab5c73a63cf49faa51',
            'tex_member': 'three-prime-factors-complete/publication/three_factors/paper/main.tex',
            'tex_sha256': '291020863f5fbb4f2d98aa0a1d5ac63349bd8c565d4ab07422aee83d23825451',
            'statement_label': 'lem:mertens',
            'verification_boundary': 'Pinned source statement and its ratio derivation inspected; Rosser-Schoenfeld 1962 Theorem 8 is an external premise. The original RS PDF was not independently retrieved.',
        },
        'reference_head_children': PRIMES, 'thresholds': THRESHOLDS, 'gamma': GAMMA,
        'expense_box_upper_corner': EMAX, 'zero_expense': zero, 'upper_corner': corner,
        'strict_gradient_upper_bounds': SIMPLE_GRADIENT,
        'atomic_owner_coefficients': [1 - c / 2 for c in SIMPLE_GRADIENT],
        'head_charge_upper_bound': Q(179, 200),
        'tail': {'cutoff': B, 'ell': ell, 'moment_exponent': exponent,
                 'prime_ratio_correction': correction, 'integral_polynomial_terms': terms,
                 'tau7_upper_bound': tau, 'head_second_moment_upper_bound': 66,
                 'charge_upper_bound': tail_charge, 'simple_strict_charge_bound': Q(3, 125),
                 'simple_charge_slack': Q(3, 125) - tail_charge},
        'head_rows': rows, 'uniform_head_root_margin': Q(2357, 76800),
        'uniform_dense_tail_root_margin': Q(7177, 384000),
        'uniform_owner_coefficient': Q(5, 6),
        'maximum_total_charge_bound': Q(179, 200) + EMAX / 3 + Q(3, 125),
    })


def main():
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = certificate()
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: zero/corner charges, five exact derivatives, M2 < 66, 66*tau7 < 3/125, and all six root margins.')


if __name__ == '__main__':
    main()
