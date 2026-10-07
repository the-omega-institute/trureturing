"""Directed Cesaro smoothing of new finite signed prime-discrepancy heads.

Every prime power up to the exact cutoff is retained. The same continuous
main term participates in all cross terms. This is a finite-head coupling
allowance, not positivity of the complete Weil form or an RH certificate.
"""
import argparse
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx, fmpq, fmpz


def interval(value):
    if not value.is_finite():
        raise ValueError('Finite directed interval required')
    return {
        'lower_dyadic': [str(v) for v in value.lower().man_exp()],
        'upper_dyadic': [str(v) for v in value.upper().man_exp()],
        'display': str(value),
    }


def square_primitive(coefficients, t):
    """Antiderivative of (a+b*t+c*exp(t/2)+d*exp(-t/2)) squared."""
    a, b, c, d = coefficients
    return ((a*a+2*c*d)*t+a*b*t*t+b*b*t*t*t/3
            +c*c*t.exp()-d*d*(-t).exp()
            +2*c*(t/2).exp()*(2*(a+b*t)-4*b)
            +2*d*(-t/2).exp()*(-2*(a+b*t)-4*b))


def square_integral(coefficients, left, right):
    return square_primitive(coefficients, right)-square_primitive(coefficients, left)


def continuum_coefficients(midpoint, end, width):
    """Exact positive-half convolution of the tent with exp(abs(s)/2)."""
    zero = arb(0)
    ew = (width/2).exp()
    ea = (end/2).exp()
    if midpoint < width:
        return [-4*arb(1), 4/width, 4*(ew-2)/width, 4*ew/width]
    if midpoint < end-width:
        return [zero, zero, 8*((width/2).cosh()-1)/width, zero]
    if midpoint < end:
        return [ea*(2-2*end/width+4/width), 2*ea/width,
                4*((-width/2).exp()-2)/width, zero]
    return [ea*(2+2*end/width-4/width), -2*ea/width,
            4*(-width/2).exp()/width, zero]


def compute_heads(precision=192, cutoffs=('17/2', '69/2', '289/2'),
                  tent_width='1/8', frequency_bands=(8, 16)):
    if precision < 128:
        raise ValueError('At least 128 bits required')
    ctx.prec = precision
    width = arb(fmpq(tent_width))
    if not 0 < width < arb(2).log():
        raise ValueError('Negative prime tents must not cross the positive half-line')
    if not cutoffs or not frequency_bands:
        raise ValueError('Nonempty cutoff and frequency families required')
    results = []
    for cutoff in cutoffs:
        exact = Fraction(cutoff)
        count = exact.numerator//exact.denominator
        first, second = 0, 1
        while second < count:
            first, second = second, first+second
        if count < 2 or second != count:
            raise ValueError('The cutoff integer must be a Fibonacci number at least two')
        end = arb(fmpq(cutoff)).log()
        if not end > 2*width:
            raise ValueError('Distinct continuum pieces required')
        atoms = []
        for n in range(2, count+1):
            factors = fmpz(n).factor()
            if len(factors) == 1:
                prime, exponent = factors[0]
                weight = arb(int(prime)).log()/arb(n).sqrt()
                atoms.append((arb(n).log(), weight, n, int(prime), int(exponent)))
        points = [arb(0), width, end-width, end, end+width]
        for center, weight, n, prime, exponent in atoms:
            points.extend([center-width, center, center+width])
        # Midpoints only propose an order; every adjacent order is certified.
        points.sort(key=lambda value: float(value.mid()))
        if not all(left < right for left, right in zip(points, points[1:])):
            raise ValueError('Piecewise breakpoint order not certified')
        signed = arb(0)
        unsigned = arb(0)
        prime_energy = arb(0)
        continuum_energy = arb(0)
        for left, right in zip(points, points[1:]):
            midpoint = (left+right)/2
            constant, slope = arb(0), arb(0)
            for center, weight, n, prime, exponent in atoms:
                if midpoint < center-width or midpoint > center+width:
                    continue
                if midpoint < center:
                    constant += weight*(1-center/width)
                    slope += weight/width
                elif midpoint > center:
                    constant += weight*(1+center/width)
                    slope -= weight/width
                else:
                    raise ValueError('Atom piece not certified')
            p = [constant, slope, arb(0), arb(0)]
            j = continuum_coefficients(midpoint, end, width)
            signed += square_integral([x-y for x, y in zip(p, j)], left, right)
            unsigned += square_integral([x+y for x, y in zip(p, j)], left, right)
            prime_energy += square_integral(p, left, right)
            continuum_energy += square_integral(j, left, right)
        # The measure and smoothing are even; integrate the full line.
        signed *= 2
        unsigned *= 2
        prime_energy *= 2
        continuum_energy *= 2
        cross_twice = (unsigned-signed)/2
        if not (signed > 0 and unsigned > signed and cross_twice > 0):
            raise ValueError('Signed cross-term improvement not certified')
        recombined = prime_energy+continuum_energy-cross_twice
        if not (signed-recombined).contains(0):
            raise ValueError('Common-measure energy accounting lost')
        variation = 2*sum((a[1] for a in atoms), arb(0))+4*((end/2).exp()-1)
        if not variation > 0:
            raise ValueError('Positive exact total variation required')
        bands = []
        for band in frequency_bands:
            half = width*band/2
            if not 0 < width*band < 2*arb.pi():
                raise ValueError('Nonzero band Fourier floor required')
            sinc = half.sin()/half
            if not sinc > 0:
                raise ValueError('Positive sinc floor required')
            floor = width*width*sinc**4
            signed_allowance = 2*arb.pi()*signed/floor
            unsigned_allowance = 2*arb.pi()*unsigned/floor
            variation_allowance = 2*band*variation*variation
            ratio = signed_allowance/variation_allowance
            if not ratio < 1:
                raise ValueError('Preregistered finite-head allowance improvement failed')
            bands.append({
                'band_exact': str(band),
                'Fourier_floor_squared_interval': interval(floor),
                'signed_band_upper_allowance_interval': interval(signed_allowance),
                'unsigned_band_upper_allowance_interval': interval(unsigned_allowance),
                'total_variation_band_upper_allowance_interval': interval(variation_allowance),
                'signed_to_total_variation_allowance_ratio_interval': interval(ratio),
            })
        results.append({
            'cutoff_X_exact': cutoff,
            'Fibonacci_integer': count,
            'logarithmic_cut_A_interval': interval(end),
            'positive_prime_power_atoms': [
                {'n': a[2], 'prime': a[3], 'exponent': a[4]} for a in atoms],
            'positive_half_piece_count': len(points)-1,
            'smoothed_signed_energy_interval': interval(signed),
            'smoothed_unsigned_energy_interval': interval(unsigned),
            'prime_prime_energy_interval': interval(prime_energy),
            'continuum_continuum_energy_interval': interval(continuum_energy),
            'twice_prime_continuum_cross_term_interval': interval(cross_twice),
            'signed_to_unsigned_energy_ratio_interval': interval(signed/unsigned),
            'total_variation_interval': interval(variation),
            'bands': bands,
        })
    return results


def produce(precision=192):
    results = compute_heads(precision)
    return {
        'scope': 'Same signed finite prime-discrepancy head; a low/complement allowance input, not full-form positivity, cofinal control, RH/Robin/Lean or a priority claim',
        'precision_bits': precision,
        'tent_width_exact': '1/8',
        'measure': 'sum_n<=floor(X) Lambda(n)/sqrt(n)(delta_log(n)+delta_-log(n)) minus indicator_abs(t)<=log(X) exp(abs(t)/2)dt',
        'published_mechanism': 'Coppola-Laporta1411.1739v1 weighted Gallagher/Plancherel lemma; finite-measure and angular-frequency application',
        'phase_or_cutoff_selection': 'None; three exact Fibonacci-plus-half heads and two exact bands preregistered',
        'all_prime_powers_retained': True,
        'same_prime_and_continuum_cross_terms_retained': True,
        'new_arithmetic_heads_only': True,
        'old_theta_actions_or_matrices_replayed': False,
        'all_six_preregistered_improvement_checks': True,
        'actual_low_block_sign': 'Unproved',
        'same_sequence_cofinal_estimate': 'Unproved',
        'RH_and_full_Robin': 'Unresolved',
        'Lean_certification': False,
        'heads': results,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precision', type=int, default=192)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name(
        'signed-head-result.json'))
    args = parser.parse_args()
    result = produce(args.precision)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({
        'heads': [{
            'X': h['cutoff_X_exact'],
            'prime_power_atoms': len(h['positive_prime_power_atoms']),
            'signed_to_unsigned': h['signed_to_unsigned_energy_ratio_interval']['display'],
            'band_allowance_ratios': [b['signed_to_total_variation_allowance_ratio_interval']['display']
                                     for b in h['bands']],
        } for h in result['heads']],
        'same_sequence_cofinal_estimate': 'Unproved',
    }, indent=2))
