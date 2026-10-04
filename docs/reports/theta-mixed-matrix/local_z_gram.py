"""Replay the four-column whole-line Z Gram from retained H/PH balls.

Input enclosures and mathematical supplier bounds are premises, not facts
independently proved by this reader. No forward solver or old grid is rerun.
"""
import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx, fmpq


def exact(item):
    mantissa, exponent = item['dyadic']
    return arb(int(mantissa))*arb(2)**int(exponent)


def dyadic(pair):
    if not isinstance(pair, list) or len(pair) != 2:
        raise ValueError('Two-field dyadic endpoint required')
    return arb(int(pair[0]))*arb(2)**int(pair[1])


def span(item):
    if not isinstance(item, dict) or set(item) != {'lower_dyadic', 'upper_dyadic'}:
        raise ValueError('Exact interval endpoint fields required')
    lo, hi = dyadic(item['lower_dyadic']), dyadic(item['upper_dyadic'])
    if not lo.is_finite() or not hi.is_finite() or not lo <= hi:
        raise ValueError('Nonfinite or reversed sample endpoints')
    return (lo+hi)/2+arb(0, ((hi-lo)/2).upper())


def upper(value):
    if not value.is_finite():
        raise RuntimeError('Nonfinite Gram coefficient')
    value = value.upper()
    return {'display': str(value), 'dyadic': [str(v) for v in value.man_exp()]}


def interval(value):
    if not value.is_finite():
        raise RuntimeError('Nonfinite Gram entry')
    return {'lower_dyadic': [str(v) for v in value.lower().man_exp()],
            'upper_dyadic': [str(v) for v in value.upper().man_exp()]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--samples', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--precision', type=int, default=192)
    args = parser.parse_args()
    if args.precision < 192:
        parser.error('Use at least192 bits to reconstruct saved endpoints')
    ctx.prec = args.precision
    canonical = Path(__file__).resolve().parent
    inputs = {}

    def load(name):
        data = (canonical/name).read_bytes()
        inputs[name] = hashlib.sha256(data).hexdigest()
        return json.loads(data)

    high = load('high-trial-bounds-result.json')
    strip = load('strip-root-bounds-result.json')
    projection = load('continuous-projection-result.json')
    ground = load('ground-residual-result.json')
    load('common-trials.json')
    sample_path = args.samples or canonical/'local-high-input-samples.json'
    sample_bytes = sample_path.read_bytes()
    samples = json.loads(sample_bytes)
    sample_inputs = {'common-trials.json', 'high-trial-bounds-result.json',
                     'strip-root-bounds-result.json', 'continuous-projection-result.json'}
    if set(samples['input_sha256']) != sample_inputs:
        raise ValueError('Complete sample supplier hash set required')
    for key, value in samples['input_sha256'].items():
        if key not in inputs or inputs[key] != value:
            raise ValueError('Retained sample/supplier hash mismatch')
    expected = {'bandwidth_N': 64, 'trial_gamma_terms': 1024,
                'trial_prime_cutoff': 64, 'sample_spacing_h': '1/256',
                'even': True, 'indices': '[0,1024]'}
    if any(samples.get(k) != v for k, v in expected.items()):
        raise ValueError('Retained sample parameter mismatch')
    if len(samples['samples']) != 1025:
        raise ValueError('Complete1025-point source required')
    if ground['bandwidth_N'] != 64:
        raise ValueError('Ground supplier parameter mismatch')
    FB = exact(high['trial_B_frobenius_upper'])
    D = exact(strip['retained_forward_line_L2_operator_upper'])*FB
    R0 = exact(high['retained_forward_derivative_norm_upper'][0])
    CH = exact(projection['forward_pointwise_envelope_coefficient_upper'])
    delta, h, b = arb(fmpq(1, 8)), arb(fmpq(1, 256)), arb.pi()/2
    ratio = (-delta*2*arb.pi()/h).exp()
    quadrature = 2*D**2*ratio/(1-ratio)
    Zsup = CH*(2/b)**2*arb(-2).exp()+(arb(64)/arb.pi()).sqrt()*R0*FB
    tail = Zsup*exact(projection['forward_physical_and_discrete_L1_tail_upper'])
    gram = [[arb(0) for _ in range(4)] for _ in range(4)]
    for k, row in enumerate(samples['samples']):
        if row['index'] != k or len(row['H']) != 4 or len(row['PH']) != 4:
            raise ValueError('Ordered four-column sample rows required')
        H = [span(x) for x in row['H']]
        PH = [span(x) for x in row['PH']]
        Z = [H[a]-PH[a] for a in range(4)]
        for i in range(4):
            for j in range(4):
                gram[i][j] += h*(2 if k else 1)*H[i]*Z[j]
    for i in range(4):
        for j in range(4):
            gram[i][j] += arb(0, (quadrature+tail).upper())
    checks = 0
    for i in range(4):
        for j in range(i):
            if not gram[i][j].overlaps(gram[j][i]):
                raise RuntimeError('Gram transpose enclosure mismatch')
            checks += 1
    # Actual Gram is Hermitian. The maximum absolute row sum bounds its
    # operator norm; this uses entries for the same four fixed vectors.
    row_sums = [sum((abs(x) for x in row), arb(0)).upper() for row in gram]
    gram_norm = row_sums[0]
    for row_sum in row_sums[1:]:
        gram_norm = gram_norm.max(row_sum)
    Znorm = gram_norm.sqrt()
    gnorm = exact(ground['Qv0_norm_upper'])
    common_norm = (Znorm**2+gnorm**2).sqrt()
    result = {
        'scope': 'Paper-model four-column whole-line Z Gram and same-family norm bounds from retained sample premises; no complete residual Gram or restricted sign',
        'input_sha256': inputs,
        'retained_sample_sha256': hashlib.sha256(sample_bytes).hexdigest(),
        'retained_sample_filename': sample_path.name,
        'precision_bits': ctx.prec,
        'localized_integrand': 'H_i Z_j; exact <H_i,Z_j>=<Z_i,Z_j>',
        'strip_product_L1_upper': upper(D**2),
        'infinite_integral_lattice_error_upper': upper(quadrature),
        'omitted_physical_and_lattice_integral_error_upper': upper(tail),
        'entry_intervals': [[interval(v) for v in row] for row in gram],
        'entry_displays': [[str(v) for v in row] for row in gram],
        'transpose_overlap_checks': checks,
        'Gram_absolute_row_sum_upper': [upper(x) for x in row_sums],
        'Z_operator_norm_upper': upper(Znorm),
        'same_five_generator_real_norm_upper': upper(common_norm),
        'whole_line_CZ_evaluated': False,
        'common_residual_Gram_evaluated': False,
        'restricted_matrix_sign': 'Unverified', 'Lean_certification': False,
    }
    output = args.output or canonical/'local-z-gram-result.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
