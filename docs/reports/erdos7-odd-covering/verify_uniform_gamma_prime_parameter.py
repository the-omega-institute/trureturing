#!/usr/bin/env python3
"""Symbolically verify a uniform Gamma_{3,q} envelope for every q >= 5.

Python 3.9+ standard library only. Polynomial coefficients are exact Fractions.
This verifies identities and nonnegative polynomial coefficients on the entire
interval 0 <= y <= 1/4, not a sample of numerical q values. The accompanying
proof supplies the common-law layout inequality and the vertex reduction.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def poly(values):
    result = [F(v) for v in values]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def add(a, b):
    return poly([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def scale(a, scalar):
    return poly([F(scalar) * c for c in a])


def sub(a, b):
    return add(a, scale(b, -1))


def mul(a, b):
    result = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return poly(result)


def evaluate(a, x):
    return sum((coefficient * x**i for i, coefficient in enumerate(a)), F(0))


def interval_transform(a):
    # 4^n(1+t)^n P(t/(4(1+t))), n=deg P. Nonnegative coefficients
    # prove P >= 0 on [0,1/4); continuity includes the right endpoint.
    degree = len(a) - 1
    result = [F(0)] * (degree + 1)
    for i, coefficient in enumerate(a):
        for j in range(degree - i + 1):
            result[i + j] += coefficient * 4**(degree - i) * comb(degree - i, j)
    return poly(result)


def serial(a):
    return list(map(str, a))


def compute_certificate():
    zero, one, y = poly([0]), poly([1]), poly([0, 1])
    a = poly([0, 3, 2])  # (3q-1)/(q-1)^2 = 3y+2y^2.
    require(sub(a, scale(y, 2)) == poly([0, 1, 2]), 'positive-positive coefficient mismatch')
    caps = {
        'small_y': (poly([15, 28, 30]), poly([3, -5])),
        'large_y': (poly([5, 5, 10]), poly([1, -2])),
    }
    for _, denominator in caps.values():
        require(evaluate(denominator, F(0)) > 0 and evaluate(denominator, F(1, 4)) > 0,
                'a candidate envelope denominator is not positive')
    widths = ((F(1, 2), F(1)), (F(1), F(1, 2)), (F(1), F(1)))
    deletions = ((zero, zero), (y, zero), (zero, y))
    pure_densities = (sub(one, y), one)
    # Exactly these three branches can exceed small_y on [0,1/4].
    large_only = {(0, 2, 0, 0, 1), (1, 1, 0, 0, 0), (1, 1, 0, 1, 0)}
    records, ratios = [], {}
    minimum_density = F(1)
    for wi, di, zi, pi, ni in product(range(3), range(3), range(2), range(2), range(2)):
        w, v = widths[wi]
        alpha, beta = deletions[di]
        z = pure_densities[zi]
        x = (w + v) / 3
        d, e = sub(z, alpha), sub(z, beta)
        n, m = scale(d, w / 3), sub(scale(e, v / 3), scale(y, F(1, 6)))
        denominator = add(n, m)
        require(len(denominator) <= 2, 'a vertex denominator is not affine')
        for endpoint in (F(0), F(1, 4)):
            require(evaluate(n, endpoint) >= F(1, 12), 'selected root may vanish')
            require(evaluate(m, endpoint) >= F(1, 24), 'other root may vanish')
            minimum_density = min(minimum_density, evaluate(denominator, endpoint))
        extra = (d, scale(e, F(2, 3)))[pi]
        root_width = (w, v)[ni]
        numerator = add(denominator, add(scale(n, 3), extra))
        numerator = add(numerator, scale(y, x + w + 1))
        numerator = add(numerator, scale(sub(a, y), x + root_width + 1))
        key = (wi, di, zi, pi, ni)
        ratios[key] = numerator, denominator
        bound = 'large_y' if key in large_only else 'small_y'
        cap_numerator, cap_denominator = caps[bound]
        gap = sub(mul(cap_numerator, denominator), mul(numerator, cap_denominator))
        transformed = interval_transform(gap)
        require(all(c >= 0 for c in transformed), 'symbolic interval domination failed')
        records.append({'vertex_and_branch': list(key), 'dominating_branch': bound,
                        'numerator': serial(numerator), 'denominator': serial(denominator),
                        'cross_multiplied_gap': serial(gap),
                        'nonnegative_transformed_coefficients': serial(transformed)})
    require(len(records) == 72 and minimum_density == F(1, 4), 'vertex accounting mismatch')
    witnesses = {'small_y': (1, 2, 0, 0, 0), 'large_y': (1, 1, 0, 0, 0)}
    for label, key in witnesses.items():
        numerator, denominator = ratios[key]
        cap_numerator, cap_denominator = caps[label]
        require(mul(numerator, cap_denominator) == mul(cap_numerator, denominator),
                'a candidate branch is not attained by an envelope vertex')
    # The maximum of the two candidates is therefore the exact budget envelope.
    switch_numerator = sub(mul(caps['large_y'][0], caps['small_y'][1]),
                           mul(caps['small_y'][0], caps['large_y'][1]))
    require(switch_numerator == poly([0, -8, 31, 10]), 'branch-switch polynomial mismatch')
    require(evaluate(poly([-8, 31, 10]), F(0)) < 0
            < evaluate(poly([-8, 31, 10]), F(1, 4)), 'branch switch is outside the interval')

    # Actual modulus 3 absent: x >= 5/6, z >= 1-y, and the prior
    # monotone unsplit bound reduces to this rational function.
    absent_numerator, absent_denominator = poly([17, 31, 34]), poly([5, -8])
    unsplit_denominator = sub(scale(sub(one, y), F(5, 6)), scale(y, F(1, 2)))
    unsplit_numerator = add(unsplit_denominator, add(scale(sub(one, y), 2), scale(a, F(17, 6))))
    require(mul(unsplit_numerator, absent_denominator)
            == mul(absent_numerator, unsplit_denominator), 'absent branch identity failed')
    absent_gap = sub(mul(caps['small_y'][0], absent_denominator),
                     mul(absent_numerator, caps['small_y'][1]))
    require(absent_gap == poly([24, 12, -21, -70]), 'absent branch gap mismatch')
    require(all(c >= 0 for c in interval_transform(absent_gap)),
            'absent-modulus-3 branch is not dominated on the full interval')
    require(evaluate(absent_denominator, F(1, 4)) == 3 > 0,
            'absent branch denominator is not positive')

    specializations = []
    for q, old, expected, absent_expected in (
            (5, F(57, 4), F(55, 4), F(215, 24)),
            (7, F(123, 13), F(123, 13), F(208, 33)),
            (11, F(181, 25), F(181, 25), F(73, 15))):
        parameter = F(1, q - 1)
        values = {label: evaluate(n, parameter) / evaluate(d, parameter)
                  for label, (n, d) in caps.items()}
        envelope = max(values.values())
        absent = evaluate(absent_numerator, parameter) / evaluate(absent_denominator, parameter)
        require(envelope == expected and absent == absent_expected < envelope,
                'specialized exact bound mismatch')
        direct_q = max(F(15*q*q - 2*q + 17, (q - 1)*(3*q - 8)),
                       F(5*(q*q - q + 2), (q - 1)*(q - 3)))
        require(direct_q == envelope, 'q-form identity mismatch')
        specializations.append({'q': q, 'y': str(parameter),
                                'small_y_bound': str(values['small_y']),
                                'large_y_bound': str(values['large_y']),
                                'uniform_Gamma_bound': str(envelope),
                                'absent_modulus_3_bound': str(absent),
                                'previous_compatible_bound': str(old),
                                'improvement': str(old - envelope)})
    return {
        'schema': 'erdos7-uniform-gamma-prime-parameter-v1',
        'parameter_domain': '0 < y=1/(q-1) <= 1/4',
        'law': 'uniform on the complete actual {3,q} survivor set',
        'small_y_branch': '(30*y^2+28*y+15)/(3-5*y)',
        'large_y_branch': '5*(2*y^2+y+1)/(1-2*y)',
        'exact_budget_envelope': 'max(small_y_branch,large_y_branch)',
        'y_switch': '(-31+sqrt(1281))/20', 'q_switch': '(47+sqrt(1281))/16',
        'prime_formula': 'q=5:55/4; prime q>=7:(15*q^2-2*q+17)/((q-1)*(3*q-8))',
        'cofactor_coefficients': {'y': serial(y), 'a': serial(a),
                                 'a_minus_y': serial(sub(a, y)),
                                 'a_minus_2y': serial(sub(a, scale(y, 2)))},
        'polynomial_coefficient_order': 'constant to highest degree',
        'interval_transform': '4^n*(1+t)^n*P(t/(4*(1+t))), n=degree(P)',
        'symbolic_vertex_domination': records,
        'attaining_envelope_vertices': {label: list(key) for label, key in witnesses.items()},
        'minimum_vertex_survivor_density': str(minimum_density),
        'branch_difference_numerator': serial(switch_numerator),
        'absent_modulus_3': {'numerator': serial(absent_numerator),
                             'denominator': serial(absent_denominator),
                             'small_y_domination_gap': serial(absent_gap),
                             'gap_transformed_coefficients': serial(interval_transform(absent_gap))},
        'specializations': specializations,
        'scope': 'symbolic arithmetic verifies the stated analytic reduction; no Lean certification',
    }


def main():
    data = json.loads(read_artifact_text(Path(__file__).resolve().parent / 'certificates/uniform_gamma_prime_parameter_certificate.json'))
    expected = compute_certificate()
    require(data == expected, 'fixed certificate differs from symbolic reconstruction')
    print('Verified the exact two-branch budget envelope for every 0 <= y <= 1/4.')
    print('Uniform Gamma35 <= 55/4; Gamma37 <= 123/13; Gamma311 <= 181/25.')
    print('The absent-modulus-3 branch is dominated throughout the full parameter interval.')


if __name__ == '__main__':
    main()
