"""Actual c9 even prime compressions by directed support-cell integration.

Legendre recurrence is classical. This program does not use an old certificate.
The enclosure is a numerical/source input, not a Lean theorem or form sign.
"""
import argparse
import json
import math
import time
from pathlib import Path
from flint import arb, arb_mat, arb_poly, ctx

parser = argparse.ArgumentParser()
parser.add_argument('--size', type=int, required=True)
parser.add_argument('--bits', type=int, required=True)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
if not 1 <= args.size <= 256 or args.bits < 1024:
    raise ValueError('Use actual leading columns, at least 1024 bits.')
ctx.prec = args.bits
size = args.size
started = time.monotonic()
a = arb(3).log()
logs = {p: arb(p).log() for p in [2, 3, 5, 7]}
powers = {2: (2, 1), 3: (3, 1), 4: (2, 2),
          5: (5, 1), 7: (7, 1), 8: (2, 3)}
weight = {n: logs[p] / arb(n).sqrt() for n, (p, j) in powers.items()}
shift = {n: arb(1) if n == 3 else j * logs[p] / a
         for n, (p, j) in powers.items()}
ends = [arb(0), shift[4] - 1, 1 - shift[2], shift[5] - 1,
        shift[7] - 1, shift[8] - 1, arb(1)]
if not all(x < y for x, y in zip(ends, ends[1:])):
    raise ValueError('Support switches are not certified in order.')
negative = [[2, 3], [2, 3, 4], [2, 3, 4], [2, 3, 4, 5],
            [2, 3, 4, 5, 7], [2, 3, 4, 5, 7, 8]]
positive = [[2], [2], [], [], [], []]

def even_legendre(offset):
    linear = arb_poly([offset, 1])
    previous, current = arb_poly([1]), linear
    result = [previous]
    for degree in range(2, 2 * size - 1):
        following = ((2 * degree - 1) * linear * current
                     - (degree - 1) * previous) * (arb(1) / degree)
        previous, current = current, following
        if degree % 2 == 0:
            result.append(current)
    return result

plain = even_legendre(arb(0))
translated = {(n, -1): even_legendre(-shift[n]) for n in powers}
translated[(2, 1)] = even_legendre(shift[2])
normal = [arb(4 * i + 1).sqrt() for i in range(size)]
A, B = arb_mat(size, size), arb_mat(size, size)

for cell, (left, right) in enumerate(zip(ends, ends[1:])):
    cols = []
    for j in range(size):
        q = (arb(7) / 2) * plain[j]
        for n in negative[cell]:
            q -= weight[n] * translated[(n, -1)][j]
        for n in positive[cell]:
            q -= weight[n] * translated[(n, 1)][j]
        cols.append(q)
    for i in range(size):
        for j in range(i, size):
            first = (plain[i] * cols[j]).integral()
            second = (cols[i] * cols[j]).integral()
            scale = normal[i] * normal[j]
            A[i, j] += scale * (first(right) - first(left))
            B[i, j] += scale * (second(right) - second(left))
    print(json.dumps({'cell_completed': cell + 1,
                      'elapsed_seconds': time.monotonic() - started}), flush=True)

for i in range(size):
    for j in range(i + 1, size):
        A[j, i], B[j, i] = A[i, j], B[i, j]

# Rational centers use one exact 2^-512 grid. Its rounding costs at most2^-513.
def ceil_log2_dyadic(mantissa, exponent):
    mantissa, exponent = int(mantissa), int(exponent)
    if mantissa <= 0:
        raise ValueError('A positive upper radius is required.')
    bits = mantissa.bit_length()
    return exponent + bits - 1 + (mantissa != 1 << (bits - 1))

def export(matrix):
    data, maximum_radius_exponent = [], None
    for i in range(size):
        row = []
        for j in range(size):
            entry = matrix[i, j]
            if not entry.is_finite():
                raise ValueError('Nonfinite matrix enclosure.')
            mantissa, exponent = map(int, entry.mid().man_exp())
            scaled_exponent = exponent + 512
            if scaled_exponent >= 0:
                center = mantissa << scaled_exponent
            else:
                k = -scaled_exponent
                center = (mantissa + (1 << (k - 1))) >> k
            row.append(center)
            rad_m, rad_e = entry.rad().upper().man_exp()
            if rad_m:
                this_exponent = ceil_log2_dyadic(rad_m, rad_e)
                maximum_radius_exponent = (this_exponent if maximum_radius_exponent is None
                                          else max(maximum_radius_exponent, this_exponent))
        data.append(row)
    radius_exponent = -513 if maximum_radius_exponent is None else max(-513, maximum_radius_exponent)
    entry_error_exponent = radius_exponent + 1
    norm_error_exponent = entry_error_exponent + (size - 1).bit_length()
    return {'integer_centers': data, 'common_denominator_power': 512,
            'maximum_native_radius_exponent': maximum_radius_exponent,
            'operator_error_upper_power_of_two': norm_error_exponent}

export_A, export_B = export(A), export(B)
D00 = B[0, 0] - sum((A[0, j] * A[j, 0] for j in range(size)), arb(0))
result = {'cutoff': 9, 'even_dimension': size, 'precision_bits': args.bits,
          'basis': 'sqrt((4j+1)/(2log3))*P_(2j)(u/log3),j=0..size-1',
          'source': 'Actual six support cells, all2,3,4,5,7,8 paired shifts; n9 endpointzero.',
          'A': export_A, 'B': export_B,
          'actual_D00_ball': D00.str(40), 'actual_D00_certified_positive': bool(D00 > 0),
          'elapsed_seconds': time.monotonic() - started,
          'input_precision_at_least_400_bits': max(export_A['operator_error_upper_power_of_two'],
                                                 export_B['operator_error_upper_power_of_two']) <= -400,
          'scope': 'Directed ball source input for actual A_M and trueM9² compression. '
                   'NoJ/inverse-compression/finite-sign certificate or RH proof; no old source matrices.'}
args.out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ['A', 'B']}
                 | {'A_error_power': export_A['operator_error_upper_power_of_two'],
                    'B_error_power': export_B['operator_error_upper_power_of_two']}), flush=True)

if not result['input_precision_at_least_400_bits']:
    raise SystemExit(2)
