"""Whole-line high samples with a finite physical sinc convolution.

This supplies per-column local enclosures under the paper-model supplier
premises, not a complete action, common residual Gram or sign certificate.
Classical Bessel/DFT capabilities and canonical supplier bounds are reused.
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
parser.add_argument('--precision', type=int, default=192)
parser.add_argument('--output', type=Path)
parser.add_argument('--samples-output', type=Path)
args = parser.parse_args()
if args.precision < 128:
    parser.error('Use at least128 bits for this local-vector experiment')
canonical = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('theta_root_supplier', canonical/'strip_root_bounds.py')
supplier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(supplier)
ctx.prec = args.precision
inputs = {}


def load(name):
    data = (canonical/name).read_bytes()
    inputs[name] = hashlib.sha256(data).hexdigest()
    return json.loads(data)


def exact(item):
    mantissa, exponent = item['dyadic']
    return arb(int(mantissa))*arb(2)**int(exponent)


def upper(x):
    if not x.is_finite():
        raise RuntimeError('Nonfinite local-vector bound')
    x = x.upper()
    return {'display': str(x), 'dyadic': [str(v) for v in x.man_exp()]}


def enclosure(x):
    if not x.is_finite():
        raise RuntimeError('Nonfinite local-vector sample')
    return {'display': str(x), 'lower': upper(x.lower()), 'upper': upper(x.upper())}


trials = load('common-trials.json')
high = load('high-trial-bounds-result.json')
strip = load('strip-root-bounds-result.json')
projection = load('continuous-projection-result.json')
if inputs['common-trials.json'] != high['input_sha256']['common-trials.json']:
    raise RuntimeError('Trial coefficient mismatch')
if inputs['high-trial-bounds-result.json'] != strip['input_sha256']['high-trial-bounds-result.json']:
    raise RuntimeError('High supplier mismatch')
if any(inputs[k] != v for k, v in projection['input_sha256'].items()):
    raise RuntimeError('Projection supplier mismatch')
if trials['coefficient_exponent'] != -40:
    raise RuntimeError('Unexpected exact dyadic precision')
if (high['bandwidth_N'], high['trial_gamma_terms'], high['trial_prime_cutoff']) != (64, 1024, 64):
    raise RuntimeError('Whole-line family mismatch')
weights = [[arb(int(v))*arb(2)**-40 for v in row] for row in trials['trial_coefficients_B']]
norms = [(arb(64*(2*j+1))/arb.pi()).sqrt() for j in range(95)]
double_factorials = [math.prod(range(1, 2*j+2, 2)) for j in range(96)]


def spherical(j, z):
    return z**j/double_factorials[j]*(-z*z/4).hypgeom_0f1(arb(fmpq(2*j+3, 2)))


def input_values(x):
    if x.is_zero():
        basis = [norms[0]]+[arb(0)]*94
    else:
        z = acb(32*x)
        js = [acb(0) for _ in range(96)]
        js[94], js[95] = spherical(94, z), spherical(95, z)
        for j in range(94, 0, -1):
            js[j-1] = (2*j+1)*js[j]/z-js[j+1]
        cosine, sine = z.cos(), z.sin()
        phase = [cosine, -sine, -cosine, sine]
        basis = [(norms[j]*js[j]*phase[j % 4]).real for j in range(95)]
    p = [sum((weights[j][a]*basis[j] for j in range(95)), arb(0)) for a in range(4)]
    s = supplier.coherent_root(acb(x)).real
    return p, s


started = time.perf_counter()
length, input_last, output_last = 32768, 1024, 2112
h, R, X, delta = arb(fmpq(1, 256)), arb(128), arb(4), arb(fmpq(1, 8))
prime_terms = []
for prime in range(2, 65):
    if any(prime % d == 0 for d in range(2, math.isqrt(prime)+1)):
        continue
    power = prime
    while power <= 64:
        prime_terms.append((power, arb(prime).log()/arb(power).sqrt()))
        power *= prime
prime_terms.sort()
if [n for n, _ in prime_terms] != high['retained_prime_powers']:
    raise RuntimeError('Complete prime-power family mismatch')
local = [input_values(arb(k)*h) for k in range(input_last+1)]
samples = [[acb(0) for _ in range(length)] for _ in range(4)]
means = [arb(0) for _ in range(4)]
for k, (p, s) in enumerate(local):
    x = arb(k)*h
    v0 = 2*(x/2).cosh()*s
    for a in range(4):
        samples[a][k] = acb(s*p[a])
        if k:
            samples[a][-k] = samples[a][k]
        means[a] += h*(2 if k else 1)*v0*p[a]
input_seconds = time.perf_counter()-started

start = time.perf_counter()
symbols = [arb(0) for _ in range(length)]
psi0, psiJ = arb(fmpq(1, 4)).digamma(), arb(fmpq(4097, 4)).digamma()
for n in range(1, length//2+1):
    xi = 2*arb.pi()*n/R
    value = acb(arb(fmpq(1, 4)), xi/2).digamma().real-psi0+psiJ-acb(arb(fmpq(4097, 4)), xi/2).digamma().real
    symbols[n] = value
    if n != length//2:
        symbols[-n] = value
gamma_samples = []
for a in range(4):
    transform = acb.dft(samples[a])
    gamma_samples.append(acb.dft([symbols[n]*transform[n] for n in range(length)], inverse=True))
gamma_seconds = time.perf_counter()-start

start = time.perf_counter()
cgamma = psi0-arb.pi().log()
Hgrid = [[acb(0) for _ in range(length)] for _ in range(4)]
for k, (p, s) in enumerate(local):
    x = arb(k)*h
    prime_action = [arb(0) for _ in range(4)]
    for n, weight in prime_terms:
        shift = arb(n).log()
        pp, sp = input_values(x+shift)
        pm, sm = input_values(x-shift)
        for a in range(4):
            prime_action[a] += weight*(sp*pp[a]+sm*pm[a])
    v0 = 2*(x/2).cosh()*s
    for a in range(4):
        value = s*gamma_samples[a][k].real+cgamma*s*s*p[a]-s*prime_action[a]+arb(fmpq(3, 8))*v0*means[a]
        Hgrid[a][k] = acb(value)
        if k:
            Hgrid[a][-k] = acb(value)
prime_seconds = time.perf_counter()-start

# Paper-model analytic error application. Numerical balls already
# enclose the finite DFT, special functions, primes and finite mean sum.
FB, M, B, V, A0 = (exact(high['trial_B_frobenius_upper']),
                  exact(high['finite_multiplier_sup_upper']),
                  exact(strip['s_line_L2_upper']),
                  exact(strip['v0_line_L2_upper']),
                  exact(strip['s_real_sup_upper']))
b, UX = arb.pi()/2, (2*X).exp()
Cs = (2*arb.pi()*arb(fmpq(7, 6))*(2*arb.pi()+3)).sqrt()
physical_integral = (-b*UX).exp()*(UX/b+1/b**2)
f_tail = Cs*(arb(64)/arb.pi()).sqrt()*FB*physical_integral
gap = R-2*X
wrapped_kernel = 2*(-gap/2).exp()/((1-(-R/2).exp())*(1-(-2*gap).exp()))
gamma_wrap = wrapped_kernel*B*FB
gamma_physical = (2*M/h+2*1024)*f_tail
frequency_step = 2*arb.pi()/R
gamma_alias = M/R*2*B*(64*delta).exp()*FB*(-delta*arb.pi()/h).exp()/(1-(-delta*frequency_step).exp())
poisson_ratio = (-delta*2*arb.pi()/h).exp()
mean_error = 2*V*(64*delta).exp()*FB*poisson_ratio/(1-poisson_ratio)
mean_error += (arb(64)/arb.pi()).sqrt()*FB*2*Cs*physical_integral
v0_sup = 2*Cs*(2/b)**2*arb(-2).exp()
H_error = A0*(gamma_wrap+gamma_physical+gamma_alias)+arb(fmpq(3, 8))*v0_sup*mean_error
for a in range(4):
    for k in range(input_last+1):
        value = Hgrid[a][k].real+arb(0, H_error.upper())
        Hgrid[a][k] = acb(value)
        if k:
            Hgrid[a][-k] = acb(value)

start = time.perf_counter()
kernel = [acb(0) for _ in range(length)]
for k in range(length):
    index = k if k < length//2 else k-length
    t = arb(index)*h
    kernel[k] = acb(arb(64)/arb.pi() if index == 0 else (64*t).sin()/(arb.pi()*t))
kernel_hat = acb.dft(kernel)
PHgrid = []
for a in range(4):
    transform = acb.dft(Hgrid[a])
    PHgrid.append(acb.dft([kernel_hat[n]*transform[n] for n in range(length)], inverse=True))
projection_seconds = time.perf_counter()-start
projection_error = exact(projection['combined_sinc_quadrature_and_physical_tail_pointwise_error_upper'])
H_outside = exact(projection['forward_pointwise_envelope_coefficient_upper'])*UX**2*(-b*UX).exp()
selected = []
max_radius = arb(0)
for k in range(output_last+1):
    values = []
    for a in range(4):
        Hvalue = Hgrid[a][k].real if k <= input_last else arb(0, H_outside.upper())
        PHvalue = h*PHgrid[a][k].real+arb(0, projection_error)
        Zvalue = Hvalue-PHvalue
        max_radius = max_radius.max(Zvalue.rad())
        if k in (0, 64, 256, 1024, 2048, 2112):
            values.append(enclosure(Zvalue))
    if values:
        selected.append({'x': str(fmpq(k, 256)), 'Z_columns': values})
result = {
    'scope': 'Directed per-column local samples of the fixed whole-line Z=QH_1024,64 EB under paper-model supplier premises; no complete action, common residual Gram or sign',
    'precision_bits': ctx.prec, 'input_sha256': inputs,
    'classical_sources': ['DLMF10.54.2 Legendre integral', 'DLMF10.51.1 spherical recurrence', 'Tao Proposition3 Poisson and strip transport', 'canonical finite Gamma convolution identity'],
    'input_bandwidth_N': 64, 'trial_gamma_terms': 1024,
    'prime_power_count': len(prime_terms), 'sample_spacing_h': '1/256',
    'DFT_length': length, 'physical_period': 128,
    'input_radius': 4, 'local_output_radius': '33/4',
    'distinct_nonnegative_local_output_points': output_last+1,
    'four_columns': 4, 'sharp_frequency_mask_used': False,
    'timings_seconds': {'input': input_seconds, 'gamma': gamma_seconds,
                        'primes': prime_seconds, 'sinc_projection': projection_seconds},
    'model_errors_upper': {'periodic_gamma_wrap': upper(gamma_wrap),
                                 'gamma_physical_tail': upper(gamma_physical),
                                 'finite_DFT_gamma_alias': upper(gamma_alias),
                                 'mean_quadrature_and_physical_tail': upper(mean_error),
                                 'forward_H_analytic_pointwise': upper(H_error),
                                 'sinc_quadrature_and_physical_tail': upper(projection_error),
                                 'maximum_local_Z_radius': upper(max_radius)},
    'selected_local_Z_enclosures': selected,
    'whole_line_CZ_evaluated': False, 'common_Gram_evaluated': False,
    'matrix_sign_certified': False, 'Lean_certification': False,
}


def interval(x):
    if not x.is_finite():
        raise RuntimeError('Nonfinite retained sample')
    return {'lower_dyadic': [str(v) for v in x.lower().man_exp()],
            'upper_dyadic': [str(v) for v in x.upper().man_exp()]}


saved_samples = []
for k in range(input_last+1):
    H = [Hgrid[a][k].real for a in range(4)]
    PH = [h*PHgrid[a][k].real+arb(0, projection_error) for a in range(4)]
    saved_samples.append({'index': k, 'H': [interval(v) for v in H],
                          'PH': [interval(v) for v in PH]})
sample_path = args.samples_output or canonical/'local-high-input-samples.json'
sample_data = {
    'scope': 'Paper-model per-column H and continuous PH enclosures; no joint numerical operator radius or complete residual Gram',
    'input_sha256': inputs, 'precision_bits': ctx.prec,
    'bandwidth_N': 64, 'trial_gamma_terms': 1024, 'trial_prime_cutoff': 64,
    'sample_spacing_h': '1/256', 'even': True, 'indices': '[0,1024]',
    'samples': saved_samples,
}
sample_text = json.dumps(sample_data, separators=(',', ':'))+'\n'
sample_path.write_text(sample_text)
result['retained_sample_sha256'] = hashlib.sha256(sample_text.encode()).hexdigest()
result['retained_sample_filename'] = sample_path.name

output = args.output or canonical/'local-high-result.json'
output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k: v for k, v in result.items() if k != 'selected_local_Z_enclosures'}, indent=2))
