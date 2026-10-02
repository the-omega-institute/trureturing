"""New-width Legendre kernel and actual even tail from attributed scalar input.

Only the author's support-independent moment packet is reused. The kernel,
normalization, convolution matrix and filtered column use a=log(3). Source
moment containment remains an author-attested premise, not this program's result.
Classical Legendre seed and convolution formulas: Liu, Appendix D.3.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
from flint import arb, fmpq, ctx

parser = argparse.ArgumentParser()
parser.add_argument('--moments', type=Path, required=True)
parser.add_argument('--size', type=int, required=True)
parser.add_argument('--bits', type=int, required=True)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
if not 1 <= args.size <= 256 or args.bits < 2048:
    raise ValueError('Use at most256 actual even columns and at least2048 bits.')
packet = args.moments.read_bytes()
packet_sha = hashlib.sha256(packet).hexdigest()
if packet_sha != 'f8cb5c681a22755b980d2e98d781353fe9ce058fe33eb8a7753585e2c52b2f93':
    raise ValueError('Unpinned source moment packet.')
source = json.loads(packet)
if source['schema'] != 'SOURCE_MOMENTS_V1':
    raise ValueError('Wrong moment schema.')
parameters = source['parameters']
if (parameters['omega'], parameters['beta'], parameters['outputBits']) != (256, '7/2', 1024):
    raise ValueError('Source normalization mismatch.')
rows = source['rows']
if len(rows) != 1024 or [r['q'] for r in rows] != list(range(1024)):
    raise ValueError('Incomplete moments.')
if any(int(r['hi']) - int(r['lo']) != 3 for r in rows):
    raise ValueError('Unexpected source interval widths.')
ctx.prec = args.bits
started = time.monotonic()
size = args.size
degree = 2 * (size - 1)
expanded_degree = 2 * degree
a = arb(3).log()
z = 512 * a
kernel_coefficients, band_coefficients = [], []
pole_power, band_power, factorial = arb(1), arb(1), 1
for q, row in enumerate(rows):
    moment_center = arb(fmpq(int(row['lo']) + int(row['hi']), 2**1025))
    sign = 1 if q % 2 == 0 else -1
    kernel_coefficients.append((2 * pole_power + sign * band_power * moment_center) / factorial)
    band_coefficients.append((256 / arb.pi()) * sign * band_power / (factorial * (2*q + 1)))
    pole_power *= a*a
    band_power *= z*z
    factorial *= (2*q + 1) * (2*q + 2)

def boundary_moments(coefficients, last_degree):
    b = [arb(0) for _ in range(last_degree + 1)]
    for q, coefficient in enumerate(coefficients):
        m = 2*q
        weight = arb(1) / (m + 1)
        for j in range(min(m, last_degree) + 1):
            b[j] += coefficient * weight
            weight *= arb(m-j) / (m+j+2)
    return [2 * (1 if j % 2 == 0 else -1) * value for j, value in enumerate(b)]

b = boundary_moments(kernel_coefficients, expanded_degree + 1)
band_b = boundary_moments(band_coefficients, degree + 1)
print(json.dumps({'stage': 'boundary_seeds', 'elapsed_seconds': time.monotonic()-started}), flush=True)

def zero_row(boundary, j):
    if j == 0:
        return 2 * (boundary[0] + boundary[1])
    return 2 * (boundary[j+1] - boundary[j-1]) / (2*j+1)

previous_two = {j: zero_row(b, j) for j in range(0, expanded_degree + 1, 2)}
previous_one = {j: (previous_two[j-1] - previous_two[j+1] + 2*(b[j+1]-b[j-1])) / (2*j+1)
                for j in range(1, expanded_degree, 2)}
matrix = [[arb(0) for _ in range(size)] for _ in range(size)]
normal = [arb(4*j + 1).sqrt() for j in range(size)]
for j in range(size):
    matrix[0][j] = (a/2) * normal[j] * previous_two[2*j]
for r in range(2, degree + 1):
    current = {j: previous_two[j] - (arb(2*r-1)/(2*j+1)) * (previous_one[j+1]-previous_one[j-1])
               for j in range(r, expanded_degree-r+1, 2)}
    if r % 2 == 0:
        i = r//2
        for j in range(i, size):
            matrix[i][j] = (a/2) * normal[i] * normal[j] * current[2*j]
    previous_two, previous_one = previous_one, current
for i in range(size):
    for j in range(i):
        matrix[i][j] = matrix[j][i]

delta = arb(2)**(-49158)
tail = [(1-delta if j == 0 else arb(0)) - (a/2)*normal[j]*zero_row(band_b, 2*j)
        for j in range(size)]
for i in range(size):
    for j in range(i, size):
        matrix[i][j] += 81 * tail[i] * tail[j]
        matrix[j][i] = matrix[i][j]

def upper_power(value):
    mantissa, exponent = map(int, value.upper().man_exp())
    if mantissa <= 0:
        return None
    bits = mantissa.bit_length()
    return exponent+bits-1+(mantissa != 1 << (bits-1))

def export(values):
    centers, maximum_power = [], None
    for row in values:
        exported = []
        for value in row:
            if not value.is_finite():
                raise ValueError('Nonfinite arithmetic enclosure.')
            mantissa, exponent = map(int, value.mid().man_exp())
            exponent += 512
            center = mantissa << exponent if exponent >= 0 else (mantissa+(1 << (-exponent-1))) >> (-exponent)
            exported.append(center)
            power = upper_power(value.rad())
            if power is not None:
                maximum_power = power if maximum_power is None else max(maximum_power, power)
        centers.append(exported)
    entry_power = max(-513, maximum_power if maximum_power is not None else -513)+1
    return {'integer_centers': centers, 'common_denominator_power': 512,
            'maximum_native_radius_exponent': maximum_power,
            'arithmetic_operator_error_upper_power_of_two': entry_power+(size-1).bit_length()}

J = export(matrix)
H = export([tail])
result = {'cutoff': 9, 'even_dimension': size, 'precision_bits': args.bits,
          'moment_source_sha256': packet_sha,
          'moment_containment_premise': 'Author packet and Appendix D.1; not independently replayed here',
          'basis': 'sqrt((4j+1)/(2log3))*P_(2j)(u/log3),j=0..size-1',
          'J': J, 'tail_column': H,
          'kernel_analytic_operator_error_upper_power_of_two': -207,
          'tail_column_analytic_norm_error_upper_power_of_two': -768,
          'J_total_operator_error_upper_power_of_two': -206,
          'elapsed_seconds': time.monotonic()-started,
          'scope': 'New-width kernel, actual filtered tail and conditional directed source input. '
                   'No author implementation/matrix reuse, finite sign certificate or RH proof.'}
if J['arithmetic_operator_error_upper_power_of_two'] > -400 or H['arithmetic_operator_error_upper_power_of_two'] > -400:
    raise ValueError('Insufficient new-width arithmetic precision.')
args.out.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['J','tail_column']}
                 | {'J_arithmetic_error_power':J['arithmetic_operator_error_upper_power_of_two']}), flush=True)
