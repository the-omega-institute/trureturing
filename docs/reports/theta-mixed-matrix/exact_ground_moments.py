"""Evaluate the95 exact-ground direction moments from the accepted basis.

The DLMF basis and contour mean allowances are reused. No Schur sign follows.
"""
import argparse
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import time
from flint import acb, arb, ctx, fmpq

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--canonical', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--coefficients', type=Path, default=Path(__file__).resolve().with_name('low-full-action-coefficients.json'))
parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name('exact-ground-moments-result.json'))
args = parser.parse_args()
canonical = args.canonical.resolve()
spec = importlib.util.spec_from_file_location('theta_moment_root', canonical/'strip_root_bounds.py')
root = importlib.util.module_from_spec(spec)
spec.loader.exec_module(root)
ctx.prec = 192
raw = args.coefficients.read_bytes()
coefficients = json.loads(raw)
for name, sha in coefficients['input_sha256'].items():
    if hashlib.sha256((canonical/name).read_bytes()).hexdigest() != sha:
        raise ValueError('Ground-moment supplier hash mismatch')
if (coefficients['bandwidth_N'], coefficients['low_orthonormal_columns'],
    coefficients['sample_spacing_h']) != (64, 95, '1/256'):
    raise ValueError('Exact ground-moment basis mismatch')
norms = [(arb(64*(2*j+1))/arb.pi()).sqrt() for j in range(95)]
factorials = [math.prod(range(1, 2*j+2, 2)) for j in range(96)]


def spherical(j, z):
    return z**j/factorials[j]*(-z*z/4).hypgeom_0f1(arb(fmpq(2*j+3, 2)))


def basis_values(x):
    if x.is_zero():
        return [norms[0]]+[arb(0)]*94
    z = acb(32*x)
    js = [acb(0) for _ in range(96)]
    js[94], js[95] = spherical(94, z), spherical(95, z)
    for j in range(94, 0, -1):
        js[j-1] = (2*j+1)*js[j]/z-js[j+1]
    cosine, sine = z.cos(), z.sin()
    phase = [cosine, -sine, -cosine, sine]
    return [(norms[j]*js[j]*phase[j % 4]).real for j in range(95)]


def interval(value):
    if not value.is_finite():
        raise ValueError('Nonfinite ground direction moment')
    return {'lower_dyadic': [str(v) for v in value.lower().man_exp()],
            'upper_dyadic': [str(v) for v in value.upper().man_exp()]}


started = time.perf_counter()
h = arb(fmpq(1, 256))
moments = [arb(0) for _ in range(95)]
for k in range(1025):
    x = arb(k)*h
    v0 = 2*(x/2).cosh()*root.coherent_root(acb(x)).real
    p = basis_values(x)
    for j in range(95):
        moments[j] += h*(2 if k else 1)*v0*p[j]
m, exponent = coefficients['low_exact_ground_moment_quadrature_and_tail_upper']['dyadic']
error = arb(int(m))*arb(2)**int(exponent)
moments = [v+arb(0, error.upper()) for v in moments]
square_norm = sum((v*v for v in moments), arb(0))
if not square_norm > 0:
    raise ValueError('Exact direction norm not separated from zero')
result = {
    'scope': 'Candidate directed exact e=E*Pv0=E*v0 direction; no95 low actions, common matrix or restricted sign',
    'coefficient_sha256': hashlib.sha256(raw).hexdigest(),
    'input_sha256': coefficients['input_sha256'], 'precision_bits': ctx.prec,
    'bandwidth_N': 64, 'orthonormal_columns': 95,
    'sample_spacing_h': '1/256', 'core_radius': 4,
    'basis_source': 'The existing high-trials DLMF Legendre/spherical-Bessel basis; no new basis method',
    'component_intervals': [interval(v) for v in moments],
    'component_displays': [str(v) for v in moments],
    'direction_norm_interval': interval(square_norm.sqrt()),
    'direction_norm_display': str(square_norm.sqrt()),
    'elapsed_seconds': time.perf_counter()-started,
    'restricted_matrix_sign': 'Unverified', 'Lean_certification': False,
}
args.output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
