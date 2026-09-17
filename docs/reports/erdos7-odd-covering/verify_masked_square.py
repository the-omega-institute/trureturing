#!/usr/bin/env python3
"""Exact coefficient and finite-array checks for the masked square inequality.
The all-family conclusions use the accompanying ordinary proof, not enumeration.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
import json


def need(condition, message):
    if not condition:
        raise ArithmeticError(message)


def check_identity(p, height, c, q, r, loads):
    s = F(1, p - 1)
    a = F(3 * p - 1, (p - 1) ** 2)
    b = a - s
    theta = 1 / (2 + s)
    lam = s / (s + r)
    rho = 1 - lam
    k = rho / theta
    w = c - theta * (c - q)
    v = q + lam * (c - q)
    z = c / v if v else F()
    g = q + s * c + (r * lam * c * (c - q) / v if v else F())
    need(0 <= g <= (1 + s) * c and 0 <= k <= 2 + s,
         'weight caps and nonnegative norm coefficients')
    phi_h = q * loads[0] ** 2 + sum(
        F(1, p ** max(e, f)) * c * loads[e] * loads[f]
        for e in range(height + 1) for f in range(height + 1) if e or f)
    tail = F(1, p ** height) * (
        2 * s * c * loads[0] * sum(loads) + (a - 2 * s) * c * loads[0] ** 2)
    need(tail >= 0, 'complete positive comparison tail')
    phi = phi_h + tail
    tail_s = s / p ** height
    tail_t = (b + height * s) / p ** height
    left = g * loads[0] ** 2 + sum(
        F(1, p ** e) * ((e + 1 + s - k) * c + k * w) * loads[e] ** 2
        for e in range(1, height + 1))
    left += ((tail_t - k * tail_s) * c + k * tail_s * w) * loads[0] ** 2
    residual = sum(F(1, p ** e) * v * (loads[e] - z * loads[0]) ** 2
                   for e in range(1, height + 1))
    residual += tail_s * v * (loads[0] - z * loads[0]) ** 2
    residual += sum(F(1, p ** f) * c * (loads[e] - loads[f]) ** 2
                    for e in range(1, height + 1) for f in range(e + 1, height + 1))
    residual += tail_s * c * sum((loads[e] - loads[0]) ** 2
                                  for e in range(1, height + 1))
    need(left - phi == residual >= 0, 'finite-array identity with exact infinite tail')


def run():
    count = 0
    for p, height, c, ratio, rr in product(
            (3, 5, 17, 19), (1, 2, 3), (F(), F(1), F(9, 5)),
            (F(), F(1, 7), F(1, 2), F(1)), (F(), F(1, 2), F(1))):
        theta = F(p - 1, 2 * p - 1)
        for loads in ([1] * (height + 1), list(range(1, height + 2)),
                      [3 if e % 2 else 1 for e in range(height + 1)]):
            check_identity(p, height, c, c * ratio, rr * theta, loads)
            count += 1
    p = 19
    s, theta = F(1, 18), F(18, 37)
    lam = s / (s + theta)
    kappa = s * (1 - lam) / theta
    need(lam == kappa == F(37, 361), '19 coefficients')
    need(F(19, 162) - kappa == F(865, 58482), '19 residual coefficient')
    gamma13 = F(148878188597300778613, 914721425816667898)
    gc = F(9, 5) * F(89, 64) * gamma13
    small = F(865, 58482) * gc
    need(small < F('6.025855'), 'actual-source residual bound')
    primes = (3, 5, 7, 11, 13, 17)
    full = prod(F(p * (p + 1), (p - 1) ** 2) for p in primes)
    need(full == F(357357, 20480), 'full original-label pair product')
    errors = {}
    for height, bound in ((16, F('0.000564917')), (20, F('0.000008522461'))):
        core = prod(sum(F(2 * j + 1, p ** j) for j in range(height + 1))
                    for p in primes)
        for p in primes:
            need(F(p * (p + 1), (p - 1) ** 2)
                 - sum(F(2 * j + 1, p ** j) for j in range(height + 1))
                 == F((2 * height + 3) * p - (2 * height + 1),
                      p ** height * (p - 1) ** 2), 'exact prime tail')
        error = F(2090, 9) * (full - core)
        need(error < bound, 'complete weighted old-test tail')
        errors[str(height)] = {'exact': str(error), 'strict_upper': str(bound)}
    print(json.dumps({'finite_array_identities': count,
                      'G_c_upper': str(gc), 'small_term': str(small),
                      'old_test_tail_errors': errors,
                      'verification': 'exact rational checks; no Lean'}, indent=2))


if __name__ == '__main__':
    run()
