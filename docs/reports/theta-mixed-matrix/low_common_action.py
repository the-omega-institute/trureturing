"""Evaluate the actual95 low actions and localized low/mixed theta blocks.

Reuses accepted full-Gamma allowances, exact ground moments and high
actions. Paper estimates are premises; no Schur sign or Lean certificate.
"""
import argparse
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import time

from flint import acb, arb, arb_mat, ctx, fmpq


def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def exact(item):
    m, e = item['dyadic']
    return arb(int(m))*arb(2)**int(e)


def span(item):
    a, b = item['lower_dyadic'], item['upper_dyadic']
    lower = arb(int(a[0]))*arb(2)**int(a[1])
    upper = arb(int(b[0]))*arb(2)**int(b[1])
    if not lower <= upper:
        raise ValueError('Invalid ordered endpoint pair')
    return lower.union(upper)


def bound(value):
    if not value.is_finite():
        raise ValueError('Nonfinite low common-action bound')
    value = value.upper()
    return {'display': str(value), 'dyadic': [str(v) for v in value.man_exp()]}


def interval(value):
    if not value.is_finite():
        raise ValueError('Nonfinite low common-action interval')
    return {'lower_dyadic': [str(v) for v in value.lower().man_exp()],
            'upper_dyadic': [str(v) for v in value.upper().man_exp()]}


def sample_pair(value):
    # Outward quantization is part of the saved data enclosure.
    scaled = value*arb(2)**80
    return [str(scaled.lower().floor().unique_fmpz()),
            str(scaled.upper().ceil().unique_fmpz())]


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--canonical', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--coefficients', type=Path, default=Path(__file__).resolve().with_name('low-full-action-coefficients.json'))
parser.add_argument('--moments', type=Path, default=Path(__file__).resolve().with_name('exact-ground-moments-result.json'))
parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name('low-common-action-result.json'))
parser.add_argument('--samples-output', type=Path, default=Path(__file__).resolve().with_name('low-common-action-samples.json'))
parser.add_argument('--precision', type=int, default=192)
args = parser.parse_args()
if args.precision < 192:
    parser.error('At least192 bits are required')
canonical = args.canonical.resolve()
root = module(canonical/'strip_root_bounds.py', 'theta_low_action_root')
ctx.prec = args.precision
sources = {}


def load(name):
    raw = (canonical/name).read_bytes()
    sources[name] = hashlib.sha256(raw).hexdigest()
    return json.loads(raw)


coeff_raw, moment_raw = args.coefficients.read_bytes(), args.moments.read_bytes()
coeff = json.loads(coeff_raw)
moments = json.loads(moment_raw)
if moments['coefficient_sha256'] != hashlib.sha256(coeff_raw).hexdigest():
    raise ValueError('Ground direction/allowance mismatch')
for supplier in (coeff, moments):
    for name, sha in supplier['input_sha256'].items():
        if hashlib.sha256((canonical/name).read_bytes()).hexdigest() != sha:
            raise ValueError('Low supplier hash mismatch: '+name)
if (coeff['bandwidth_N'], coeff['low_orthonormal_columns'],
    coeff['sample_spacing_h'], coeff['physical_period']) != (64, 95, '1/256', 128):
    raise ValueError('Fixed low-family parameters required')
if (moments['bandwidth_N'], moments['orthonormal_columns'],
    moments['sample_spacing_h'], moments['core_radius']) != (64, 95, '1/256', 4):
    raise ValueError('Fixed ground-direction parameters required')
e = [span(v) for v in moments['component_intervals']]
if len(e) != 95:
    raise ValueError('Exactly95 ground components required')
low_source = load('local-high-input-samples.json')
high_source = load('high-full-action-samples.json')
high_action = load('high-full-action-result.json')
high_bounds = load('high-trial-bounds-result.json')
strip = load('strip-root-bounds-result.json')
projection = load('continuous-projection-result.json')
offgrid = load('off-grid-action-result.json')
gram = load('local-z-gram-result.json')
trials = load('common-trials.json')
for supplier in (low_source, high_source, high_action, high_bounds,
                 strip, projection, offgrid, gram):
    for name, sha in supplier['input_sha256'].items():
        if name in sources and sources[name] != sha:
            raise ValueError('Saved high supplier hash mismatch: '+name)
if high_action['retained_sample_sha256'] != sources['high-full-action-samples.json']:
    raise ValueError('High action/sample mismatch')
if gram['retained_sample_sha256'] != sources['local-high-input-samples.json']:
    raise ValueError('Z Gram/sample mismatch')
for source in (low_source, high_source):
    if len(source['samples']) != 1025 or source['bandwidth_N'] != 64:
        raise ValueError('Complete fixed-band high sample source required')
    if (source['sample_spacing_h'], source['even'], source['indices']) != ('1/256', True, '[0,1024]'):
        raise ValueError('High-source lattice mismatch')
if (high_source['Z_definition_gamma_terms'], high_source['action_gamma'],
    high_source['action_prime_cutoff']) != (1024, 'full', 64):
    raise ValueError('Retained high-action semantics mismatch')
if (low_source['trial_gamma_terms'], low_source['trial_prime_cutoff']) != (1024, 64):
    raise ValueError('Fixed Z-definition semantics mismatch')
if trials['coefficient_exponent'] != -40:
    raise ValueError('Exact correction-map precision mismatch')

started = time.perf_counter()
timings = {}
length, last, count = 32768, 1024, 95
h, R, alpha, c = arb(fmpq(1, 256)), arb(128), arb(fmpq(1, 8)), arb(fmpq(3, 8))
norms = [(arb(64*(2*j+1))/arb.pi()).sqrt() for j in range(count)]
factorials = [math.prod(range(1, 2*j+2, 2)) for j in range(count+1)]


def spherical(j, z):
    return z**j/factorials[j]*(-z*z/4).hypgeom_0f1(arb(fmpq(2*j+3, 2)))


def basis_values(x):
    # Inherited unweighted DLMF basis; it is not the four-column high family.
    if x.is_zero():
        return [norms[0]]+[arb(0)]*(count-1)
    z = acb(32*x)
    js = [acb(0) for _ in range(count+1)]
    js[94], js[95] = spherical(94, z), spherical(95, z)
    for j in range(94, 0, -1):
        js[j-1] = (2*j+1)*js[j]/z-js[j+1]
    cosine, sine = z.cos(), z.sin()
    phase = [cosine, -sine, -cosine, sine]
    return [(norms[j]*js[j]*phase[j % 4]).real for j in range(count)]


roots, v0, basis = [], [], [[] for _ in range(count)]
Z, QHZ = [[] for _ in range(4)], [[] for _ in range(4)]
for k in range(last+1):
    x = arb(k)*h
    s = root.coherent_root(acb(x)).real
    roots.append(s)
    v0.append(2*(x/2).cosh()*s)
    p = basis_values(x)
    for j in range(count):
        basis[j].append(p[j])
    lo, hi = low_source['samples'][k], high_source['samples'][k]
    if lo['index'] != k or hi['index'] != k:
        raise ValueError('Ordered source rows required')
    if any(len(row[key]) != 4 for row, key in
           ((lo, 'H'), (lo, 'PH'), (hi, 'HZ'), (hi, 'PHZ'))):
        raise ValueError('Four-column high source required')
    for a in range(4):
        Z[a].append(span(lo['H'][a])-span(lo['PH'][a]))
        QHZ[a].append(span(hi['HZ'][a])-span(hi['PHZ'][a]))
timings['basis_and_saved_high_inputs'] = time.perf_counter()-started
print('Low basis and saved high inputs loaded', flush=True)

start = time.perf_counter()
psi0 = arb(fmpq(1, 4)).digamma()
symbols = [arb(0) for _ in range(length)]
for n in range(1, length//2+1):
    xi = 2*arb.pi()*n/R
    symbols[n] = acb(arb(fmpq(1, 4)), xi/2).digamma().real-psi0
    if n != length//2:
        symbols[-n] = symbols[n]
Gamma = []
for j in range(count):
    sampled = [acb(0) for _ in range(length)]
    for k in range(last+1):
        sampled[k] = acb(roots[k]*basis[j][k])
        if k:
            sampled[-k] = sampled[k]
    transformed = acb.dft(sampled)
    output = acb.dft([symbols[n]*transformed[n] for n in range(length)], inverse=True)
    Gamma.append([output[k].real for k in range(last+1)])
timings['full_Gamma95'] = time.perf_counter()-start
print('Full Gamma95 evaluated', flush=True)

start = time.perf_counter()
prime_terms = []
for prime in range(2, 65):
    if any(prime % d == 0 for d in range(2, math.isqrt(prime)+1)):
        continue
    n = prime
    while n <= 64:
        prime_terms.append((n, arb(prime).log()/arb(n).sqrt()))
        n *= prime
prime_terms.sort()
if [n for n, _ in prime_terms] != high_bounds['retained_prime_powers']:
    raise ValueError('Complete retained prime powers required')
prime_core = [[arb(0) for _ in range(last+1)] for _ in range(count)]
for n, weight in prime_terms:
    tau = arb(n).log()
    for k in range(last+1):
        x = arb(k)*h
        pp, pm = basis_values(x+tau), basis_values(x-tau)
        sp = root.coherent_root(acb(x+tau)).real
        sm = root.coherent_root(acb(x-tau)).real
        for j in range(count):
            prime_core[j][k] += weight*(sp*pp[j]+sm*pm[j])
timings['direct_prime95'] = time.perf_counter()-start
print('Direct retained prime95 evaluated', flush=True)

start = time.perf_counter()
core_error = exact(coeff['low_H_core_Gamma_and_mean_analytic_error_upper'])
projection_error = exact(coeff['low_continuous_PH_analytic_error_upper'])
cgamma = psi0-arb.pi().log()
kernel = [acb(0) for _ in range(length)]
for m in range(-2*last, 2*last+1):
    x = arb(m)*h
    kernel[m % length] = acb(arb(64)/arb.pi() if m == 0 else (64*x).sin()/(arb.pi()*x))
khat = acb.dft(kernel)
HL, PHL, QHL = [], [], []
maxH, maxQ = arb(0), arb(0)
for j in range(count):
    sampled = [acb(0) for _ in range(length)]
    column = []
    for k in range(last+1):
        s = roots[k]
        value = (s*Gamma[j][k]+cgamma*s*s*basis[j][k]
                 -s*prime_core[j][k]+c*v0[k]*e[j]+arb(0, core_error.upper()))
        column.append(value)
        maxH = maxH.max(value.rad())
        sampled[k] = acb(value)
        if k:
            sampled[-k] = sampled[k]
    transformed = acb.dft(sampled)
    output = acb.dft([khat[n]*transformed[n] for n in range(length)], inverse=True)
    projected = [h*output[k].real+arb(0, projection_error.upper()) for k in range(last+1)]
    HL.append(column)
    PHL.append(projected)
    QHL.append([column[k]-projected[k] for k in range(last+1)])
    for value in QHL[-1]:
        maxQ = maxQ.max(value.rad())
timings['local_H95_and_continuous_P95'] = time.perf_counter()-start
print('Local H95 and continuous P95 evaluated', flush=True)

start = time.perf_counter()
factors = [h*(2 if k else 1) for k in range(last+1)]
weightedH = arb_mat([[factors[k]*HL[j][k] for k in range(last+1)] for j in range(count)])
EH = arb_mat(basis)*weightedH.transpose()
KK = weightedH*arb_mat(QHL).transpose()
J = weightedH*arb_mat(Z).transpose()
HQ = weightedH*arb_mat(QHZ).transpose()
Dl = exact(coeff['low_full_H_line_L2_upper'])
Ul = exact(coeff['low_strip_unit_ball_upper'])
Uh = exact(strip['common_high_line_L2_operator_upper'])
Dh = exact(offgrid['retained_prime_full_HZ_line_L2_upper'])
Jh = exact(coeff['low_full_H_physical_and_lattice_tail_upper'])
b = arb.pi()/2
Bl = (arb(64)/arb.pi()).sqrt()
Hl_sup = exact(coeff['low_full_H_pointwise_envelope_coefficient_upper'])*(2/b)**2*arb(-2).exp()
Zsup = (exact(projection['forward_pointwise_envelope_coefficient_upper'])*(2/b)**2*arb(-2).exp()
        +Bl*exact(high_bounds['retained_forward_derivative_norm_upper'][0])*exact(high_bounds['trial_B_frobenius_upper']))
QHZsup = (exact(offgrid['retained_prime_full_HZ_pointwise_envelope_coefficient_upper'])*(2/b)**2*arb(-2).exp()
          +Bl*Dh)
r = (-2*arb.pi()*arb(fmpq(1, 8))/h).exp()
allowances = {}
checks = {}
for label, matrix, line, sup, symmetric in (
    ('E_HL', EH, Ul*Dl, Bl, True),
    ('K_Gram', KK, Dl**2, Hl_sup+Bl*Dl, True),
    ('K_Z', J, Dl*Uh, Zsup, False),
    ('HL_QHZ', HQ, Dl*Dh, QHZsup, False)):
    quadrature, tail = 2*line*r/(1-r), sup*Jh
    error = quadrature+tail
    for i in range(matrix.nrows()):
        for j in range(matrix.ncols()):
            matrix[i, j] += arb(0, error.upper())
    checks[label] = 0
    if symmetric:
        for i in range(matrix.nrows()):
            for j in range(i):
                if not matrix[i, j].overlaps(matrix[j, i]):
                    raise ValueError('Whole-line transpose mismatch: '+label)
                checks[label] += 1
    allowances[label] = {'quadrature_upper': bound(quadrature), 'omitted_lattice_upper': bound(tail)}
M = alpha*J+HQ
TLL = EH+alpha*arb_mat([[int(i == j) for j in range(count)] for i in range(count)])
timings['localized_low_and_mixed_blocks'] = time.perf_counter()-start
saved = {
    'scope': 'Full-Gamma primes-through64 H_L and continuous P64 H_L; omitted primes are a separate whole-L2 allowance',
    'input_sha256': sources, 'coefficient_sha256': hashlib.sha256(coeff_raw).hexdigest(),
    'ground_moment_sha256': hashlib.sha256(moment_raw).hexdigest(),
    'precision_bits': ctx.prec, 'bandwidth_N': 64, 'low_columns': count,
    'action_gamma': 'full', 'action_prime_cutoff': 64,
    'sample_spacing_h': '1/256', 'core_radius': 4, 'even': True,
    'sample_dyadic_exponent': -80,
    'samples': [{'index': k, 'H': [sample_pair(HL[j][k]) for j in range(count)],
                 'PH': [sample_pair(PHL[j][k]) for j in range(count)]} for k in range(last+1)],
}
sample_bytes = (json.dumps(saved, separators=(',', ':'))+'\n').encode()
args.samples_output.write_bytes(sample_bytes)
result = {
    'scope': 'Actual95 low actions and whole-line low/mixed blocks, full Gamma and retained primes64; no restricted sign or Lean certification',
    'input_sha256': sources, 'coefficient_sha256': hashlib.sha256(coeff_raw).hexdigest(),
    'ground_moment_sha256': hashlib.sha256(moment_raw).hexdigest(),
    'retained_sample_sha256': hashlib.sha256(sample_bytes).hexdigest(),
    'retained_sample_filename': args.samples_output.name,
    'precision_bits': ctx.prec, 'bandwidth_N': 64, 'low_columns': count,
    'DFT_length': length, 'physical_period': 128, 'sample_spacing_h': '1/256',
    'core_radius': 4, 'action_gamma': 'full', 'action_prime_powers': [n for n, _ in prime_terms],
    'timings_seconds': timings, 'whole_line_allowances': allowances,
    'transpose_overlap_checks': checks,
    'maximum_local_H_column_radius_upper': bound(maxH),
    'maximum_local_QH_column_radius_upper': bound(maxQ),
    'retained_TLL_entry_intervals': [[interval(TLL[i, j]) for j in range(count)] for i in range(count)],
    'retained_K_Gram_entry_intervals': [[interval(KK[i, j]) for j in range(count)] for i in range(count)],
    'retained_K_Z_entry_intervals': [[interval(J[i, j]) for j in range(4)] for i in range(count)],
    'retained_K_CZ_entry_intervals': [[interval(M[i, j]) for j in range(4)] for i in range(count)],
    'low_actions_evaluated': True, 'low_and_mixed_blocks_evaluated': True,
    'common_residual_Gram_evaluated': False, 'restricted_Schur_sign': 'Unverified',
    'Lean_certification': False,
}
args.output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'timings_seconds': timings, 'maximum_local_H_column_radius_upper': bound(maxH),
                  'maximum_local_QH_column_radius_upper': bound(maxQ),
                  'transpose_overlap_checks': checks, 'retained_sample_bytes': len(sample_bytes)}, indent=2), flush=True)
