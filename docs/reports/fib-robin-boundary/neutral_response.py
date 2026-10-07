"""Moment-neutral tent probes for the existing actual Binet response kernel."""
import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
import sys

import flint
from flint import arb, ctx, fmpq

from binet_inverse_tail import endpoints


SOURCE_SHA256 = '28f07ec8e6574cbbb2a755a271fb0c4a0f85e0ab6fcc45e0f56f924fe1d2ee08'


def dyadic(pair):
    mantissa, exponent = map(int, pair)
    return fmpq(mantissa * 2**exponent) if exponent >= 0 else fmpq(mantissa, 2**(-exponent))


def enclosure(row):
    low, high = dyadic(row['lower_dyadic']), dyadic(row['upper_dyadic'])
    if low > high:
        raise ValueError('Ordered source coefficient endpoints required')
    return arb(low).union(arb(high))


def kernel(source, cutoff):
    data = source.read_bytes()
    if hashlib.sha256(data).hexdigest() != SOURCE_SHA256:
        raise ValueError('Published inverse-prefix artifact hash required')
    rows = json.loads(data)['inverse_coefficients']
    if len(rows) < cutoff or any(row['index'] != i for i, row in enumerate(rows, 1)):
        raise ValueError('Complete ordered source inverse prefix required')
    inverse = [arb(0)] + [enclosure(row['inverse_coefficient']) for row in rows[:cutoff]]
    logs = [arb(0)] + [arb(n).log() for n in range(1, cutoff+1)]
    result = [arb(0) for _ in range(cutoff+1)]
    for d in range(1, cutoff+1):
        for r in range(2, cutoff//d+1):
            result[d*r] += inverse[d]*logs[r]
    if any(not result[n] > 0 for n in range(2, cutoff+1)):
        raise ValueError('Positive actual response coefficient required')
    return result


def tent_moments(center, radius):
    first, second = arb(0), arb(0)
    for offset in range(1-radius, radius):
        n, height = center+offset, radius-abs(offset)
        u = arb(fmpq(1, n*(n+1)))
        r = arb(n).log() - n*arb(fmpq(1, n)).log1p()
        first += height*u
        second += height*u*r
    return first, second, second/first


def pulse(cutoff, j):
    N = 64*cutoff**3
    center = N//j
    radius = isqrt(center)//8
    left, right = center-3*radius+1, center+3*radius-1
    if not (radius >= cutoff and left > 2 and radius*radius <= left):
        raise ValueError('Positive geometry and square-root norm certificate required')
    if not (center >= 64*radius and
            (center+3*radius-1)*(center+3*radius) <
            2*(center-radius+1)*(center-radius+2)):
        raise ValueError('Tent weight-ratio certificate required')
    # Every divisor index reading a nonzero point of this pulse must equal j.
    if (N//(right+1)+1, N//left) != (j, j):
        raise ValueError('Exact integer quotient isolation required')
    minus = tent_moments(center-2*radius, radius)
    middle = tent_moments(center, radius)
    plus = tent_moments(center+2*radius, radius)
    Uminus, Vminus, rminus = minus
    Uzero, Vzero, rzero = middle
    Uplus, Vplus, rplus = plus
    if not rminus < rzero < rplus:
        raise ValueError('Strictly ordered same-source moment ratios required')
    t = (rplus-rzero)/(rplus-rminus)
    alpha, beta = Uzero*t/Uminus, Uzero*(1-t)/Uplus
    if not (0 < alpha < 2 and 0 < beta < 2):
        raise ValueError('Positive side weights below two required')
    first = (Uzero-alpha*Uminus-beta*Uplus)/2
    second = (Vzero-alpha*Vminus-beta*Vplus)/2
    if not (first.contains(0) and second.contains(0)):
        raise ValueError('Both exact moment identities must have enclosing residuals')
    return {'index': j, 'center': center, 'radius': radius,
            'nonzero_support': [left, right],
            'left_weight': endpoints(alpha), 'right_weight': endpoints(beta),
            'first_moment_residual': endpoints(first),
            'second_moment_residual': endpoints(second)}, first, second


def produce(source, cutoffs=(8, 34, 144), precision=256):
    if precision < 192 or not cutoffs or any(c < 2 for c in cutoffs):
        raise ValueError('At least 192 bits and integer cutoffs >=2 required')
    if list(cutoffs) != sorted(set(cutoffs)):
        raise ValueError('Distinct increasing cutoffs required')
    ctx.prec = precision
    k = kernel(source, max(cutoffs))
    results = []
    for cutoff in cutoffs:
        pulses, first, second, response = [], arb(0), arb(0), arb(0)
        previous_left = None
        for j in range(2, cutoff+1):
            row, u, v = pulse(cutoff, j)
            left, right = row['nonzero_support']
            if previous_left is not None and not right+1 < previous_left:
                raise ValueError('Disjoint pulse supports with a zero gap required')
            previous_left = left
            pulses.append(row)
            first += u
            second += v
            response += k[j]*fmpq(row['radius'], 2)
        N = 64*cutoff**3
        mass = sum(k[2:cutoff+1], arb(0))
        ratio = response/arb(N).sqrt()
        lower_comparison = mass/(16*arb(cutoff).sqrt())
        if not (first.contains(0) and second.contains(0) and
                (ratio-lower_comparison).lower() > 0):
            raise ValueError('Same-input total moments and response lower comparison required')
        results.append({'cutoff': cutoff, 'N': N, 'pulse_count': len(pulses),
                        'square_root_input_norm_upper_exact': '1',
                        'adjacent_increment_upper_exact': '1',
                        'first_moment_residual': endpoints(first),
                        'second_moment_residual': endpoints(second),
                        'response': endpoints(response),
                        'response_over_sqrt_N': endpoints(ratio),
                        'kernel_mass_over_16_sqrt_cutoff': endpoints(lower_comparison),
                        'pulses': pulses})
    return {'scope': 'Method probes for homogeneous perturbations, not the actual FIB input, prime error, Robin or RH. General construction in FIB section390 is not Lean-verified; finite ball enclosures check its application.',
            'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__,
                        'precision_bits': precision},
            'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'inverse_source': source.name, 'inverse_source_sha256': SOURCE_SHA256,
            'reused': 'Published inverse coefficients only; no inverse regeneration or old producer run.',
            'kernel': 'k=gamma*log with actual Binet gamma=beta^(-1)',
            'moments': ['sum f(m)/(m(m+1))=0',
                        'sum f(m)*(log(m)/m-log(m+1)/(m+1))=0'],
            'results': results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path(__file__).with_name('binet-inverse-tail.json'))
    parser.add_argument('--cutoffs', type=int, nargs='+', default=[8, 34, 144])
    parser.add_argument('--precision', type=int, default=256)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    for protected in [args.source, Path(__file__)]:
        if (args.output.resolve() == protected.resolve() or
                (args.output.exists() and protected.exists() and args.output.samefile(protected))):
            raise ValueError('Output must not overwrite the input artifact or producer')
    result = produce(args.source, args.cutoffs, args.precision)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps([{'cutoff': row['cutoff'], 'N': row['N'],
                       'response_over_sqrt_N': row['response_over_sqrt_N']['display']}
                      for row in result['results']], indent=2))


if __name__ == '__main__':
    main()
