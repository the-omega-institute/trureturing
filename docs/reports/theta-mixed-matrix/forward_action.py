"""Complete low-band action error using saved original-theta coefficients."""
import hashlib
import json
import sys
from pathlib import Path

import flint
from flint import arb, ctx, fmpq

ctx.prec = 128
canonical = Path(__file__).resolve().parent
derivative_bytes = (canonical / 'derivative-bandwidth-result.json').read_bytes()
center_bytes = (canonical / 'sharp-center-result.json').read_bytes()
derivative = json.loads(derivative_bytes)
center = json.loads(center_bytes)
if derivative['bandwidth_N'] != 64 or center['bandwidth_N'] != 64:
    raise RuntimeError('Saved supplier bandwidth mismatch')


def value(item):
    mantissa, exponent = item['dyadic']
    return arb(int(mantissa)) * arb(2)**int(exponent)


norms = [value(x).sqrt() for x in derivative['derivative_norm_squared_upper']]
sup = [(norms[j] * norms[j+1]).sqrt() for j in range(3)]
N = arb(64)
terms = 1024
last = arb(fmpq(4*(terms-1)+1, 2))
sigma = 1 / (2*last*last)
weighted_second = sup[2] + 2*N*sup[1] + N*N*sup[0]
gamma_error = sup[0] * sigma * weighted_second
prime_cutoff = 64
K0 = value(center['K0_upper'])
b = arb(fmpq(3, 8))
r = (-2*b).exp()
prime_error = (2*K0*K0*r**(prime_cutoff+1)
               *((prime_cutoff+1)-prime_cutoff*r)/(1-r)**2)
total_error = gamma_error + prime_error
if not total_error < arb(fmpq(1, 1000)):
    raise RuntimeError('Declared full forward-action target not obtained')


def endpoint(x):
    if not x.is_finite():
        raise RuntimeError('Nonfinite coefficient enclosure')
    upper = x.upper()
    return {'display': str(upper), 'dyadic': [str(k) for k in upper.man_exp()]}


result = {
    'scope': 'Paper model coefficient calculation; not a matrix, Lean or RH certificate',
    'runtime': {'python': sys.version.split()[0],
                'python_flint': flint.__version__, 'precision_bits': ctx.prec},
    'input_data_sha256': {
        'derivative-bandwidth-result.json': hashlib.sha256(derivative_bytes).hexdigest(),
        'sharp-center-result.json': hashlib.sha256(center_bytes).hexdigest()},
    'bandwidth_N': 64, 'retained_gamma_terms': terms,
    'retained_gamma_indices': '0 through 1023',
    'retained_prime_cutoff': prime_cutoff,
    'original_derivative_grid_rerun': False,
    's_derivative_sup_upper': [endpoint(x) for x in sup],
    'sigma_upper': endpoint(sigma),
    'weighted_second_norm_coefficient_upper': endpoint(weighted_second),
    'gamma_action_error_upper': endpoint(gamma_error),
    'full_two_direction_prime_action_error_upper': endpoint(prime_error),
    'full_forward_action_error_upper': endpoint(total_error),
    'input_scope': 'Uniform on unit even low-band inputs; mean and multiplication '
                   'terms remain exact; high trials require separate derivative inputs',
}
Path(__file__).with_name('forward-action-result.json').write_text(
    json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
