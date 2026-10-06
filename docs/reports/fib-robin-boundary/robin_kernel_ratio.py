"""Directed ratio-profile parameters from the existing actual diagonal data."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

import flint
from flint import arb, ctx, fmpq

from robin_kernel_diagonal import enclosure


def dyadic(pair):
    mantissa, exponent = map(int, pair)
    return fmpq(mantissa * (1 << max(exponent, 0)),
                1 << max(-exponent, 0))


def load_ball(row):
    low = dyadic(row['lower_dyadic'])
    high = dyadic(row['upper_dyadic'])
    if low > high:
        raise ValueError('Ordered exact source endpoints required')
    midpoint, radius = arb((low + high) / 2), arb((high - low) / 2)
    value = midpoint + arb(0, radius.upper())
    if not value.is_finite() or not value.contains(arb(low)) or not value.contains(arb(high)):
        raise ValueError('Source dyadics must be enclosed')
    return value


def produce(source, precision=192):
    if precision < 128:
        raise ValueError('At least 128 bits required')
    ctx.prec = precision
    raw = source.read_bytes()
    data = json.loads(raw)
    if data['parameter'] != 'q=(3-sqrt(5))/2=phi^(-2)':
        raise ValueError('The declared actual source is required')
    q, b, bprime, c = (load_ball(data[key]) for key in
                      ['q', 'B', 'Bprime', 'diagonal_coefficient'])
    if not (0 < q < 1 and b > 0 and bprime > 0 and c < 0):
        raise ValueError('Actual positive parameters and negative diagonal required')
    a = 1 / b
    slope = bprime / b**2
    d = a + slope
    # FIB384.5: delta >=94*q/2205, so this majorizes the actual mu0.
    mu_cap = (arb(2205) / (94 * q)).upper()
    root = -2 * c / (slope + (slope**2 - 2 * a * c).sqrt())
    ratio = root.exp()
    if not (arb(fmpq(1, 100)) < root < arb(fmpq(3, 100))):
        raise ValueError('The declared root bracket must be paid by source intervals')

    def profile(u):
        return a * u**2 / 2 + slope * u + c

    def allowance(u):
        return a * u**3 / 6 + d * u**2 / 2 + (2*d - a)*u + d + mu_cap*(2*u + 11)

    negative_u, positive_u = arb(fmpq(1, 100)), arb(fmpq(3, 100))
    negative_p, positive_p = profile(negative_u), profile(positive_u)
    if not negative_p < 0 < positive_p:
        raise ValueError('Separated ratio profile signs required')
    slope_min = min(a.lower(), slope.lower())
    monotone_threshold = (22 * mu_cap / slope_min).upper()
    negative_threshold = (allowance(negative_u) / (-negative_p).lower()).upper()
    positive_threshold = (allowance(positive_u) / positive_p.lower()).upper()
    endpoint = max(monotone_threshold, negative_threshold, positive_threshold).upper()
    mantissa, exponent = map(int, endpoint.man_exp())
    # Exact dyadic ceiling, then strict slack; no float conversion of a ball.
    if exponent >= 0:
        log_threshold = (mantissa << exponent) + 1
    else:
        denominator = 1 << -exponent
        log_threshold = (mantissa + denominator - 1) // denominator + 1
    if not (negative_p + allowance(negative_u)/log_threshold < 0
            and positive_p - allowance(positive_u)/log_threshold > 0
            and slope_min/log_threshold - 22*mu_cap/log_threshold**2 > 0):
        raise ValueError('The exported log threshold must verify all three inequalities')

    return {
        'scope': 'Directed parameters for the proposed FIB399 uniform actual ratio-kernel estimate. Only existing full diagonal data are consumed; Binet terms, inverse coefficients, PNT and prime panels are not recomputed. The analytic application is paper-only, not Lean verified; no signed H budget or RH proof.',
        'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__,
                    'precision_bits': precision},
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'source_name': source.name,
        'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'profile': 'p(u)=A*u^2/2+(D-A)*u+c_diag',
        'uniform_allowance': 'C(U)=A*U^3/6+D*U^2/2+(2D-A)*U+D+mu_cap*(2U+11)',
        'A': enclosure(a), 'D': enclosure(d), 'D_minus_A': enclosure(slope),
        'mu0_upper': enclosure(mu_cap), 'c_diag': enclosure(c),
        'log_ratio_root': enclosure(root), 'ratio_root': enclosure(ratio),
        'negative_u': '1/100', 'positive_u': '3/100',
        'negative_profile': enclosure(negative_p), 'positive_profile': enclosure(positive_p),
        'negative_allowance': enclosure(allowance(negative_u)),
        'positive_allowance': enclosure(allowance(positive_u)),
        'explicit_window_H_cap': '310/441',
        'U003_window_error_coefficient_upper': enclosure((arb(fmpq(310, 441))*positive_u*allowance(positive_u)).upper()),
        'monotonic_log_threshold_upper': enclosure(monotone_threshold),
        'common_log_threshold_strict_integer': log_threshold,
        'analytic_conditions': ['x>=exp(common_log_threshold_strict_integer)',
                                'negative band: x<=m and m+1<=exp(1/100)*x',
                                'positive cone: m>=exp(3/100)*x'],
        'not_claimed': ['a numerically sharp starting threshold',
                        'a Lean proof of the profile or cone',
                        'a numerical C_H certificate',
                        'a sign for the actual H-weighted sum', 'Robin or RH']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--precision', type=int, default=192)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = produce(args.source, args.precision)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in
                     ['log_ratio_root', 'ratio_root', 'common_log_threshold_strict_integer']}, indent=2))


if __name__ == '__main__':
    main()
