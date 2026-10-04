"""Apply full Gamma and retained primes to the saved actual four Z columns.

Paper-model analytic supplier premises remain external to this experiment.
Localized factors pay whole-line Gram tails; no residual/Schur sign follows.
"""
import argparse
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import time

from flint import acb, arb, ctx, fmpq


def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def exact(item):
    m, e = item['dyadic']
    return arb(int(m))*arb(2)**int(e)


def upper(x):
    if not x.is_finite():
        raise RuntimeError('Nonfinite high-action upper bound')
    x = x.upper()
    return {'display': str(x), 'dyadic': [str(v) for v in x.man_exp()]}


def interval(x):
    if not x.is_finite():
        raise RuntimeError('Nonfinite high-action enclosure')
    return {'lower_dyadic': [str(v) for v in x.lower().man_exp()],
            'upper_dyadic': [str(v) for v in x.upper().man_exp()]}


def row_norm(gram):
    sums = [sum((abs(v) for v in row), arb(0)).upper() for row in gram]
    largest = sums[0]
    for value in sums[1:]:
        largest = largest.max(value)
    return largest.sqrt()


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--canonical', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--coefficients', type=Path)
parser.add_argument('--output', type=Path)
parser.add_argument('--samples-output', type=Path)
parser.add_argument('--precision', type=int, default=192)
args = parser.parse_args()
if args.precision < 192:
    parser.error('At least192 bits are required for saved endpoint replay')
canonical = args.canonical.resolve()
root = module(canonical/'strip_root_bounds.py', 'theta_saved_action_root')
reader = module(canonical/'local_z_gram.py', 'theta_saved_action_reader')
ctx.prec = args.precision
sources = {}


def load(name):
    data = (canonical/name).read_bytes()
    sources[name] = hashlib.sha256(data).hexdigest()
    return json.loads(data)


samples = load('local-high-input-samples.json')
high = load('high-trial-bounds-result.json')
strip = load('strip-root-bounds-result.json')
projection = load('continuous-projection-result.json')
gram0 = load('local-z-gram-result.json')
gamma = load('full-gamma-periodic-result.json')
forward = load('forward-action-result.json')
load('common-trials.json')
load('ground-residual-result.json')
coefficient_bytes = (args.coefficients or canonical/'off-grid-action-result.json').read_bytes()
coefficients = json.loads(coefficient_bytes)
for supplier in (samples, high, strip, projection, gram0, gamma, coefficients):
    for key, sha in supplier['input_sha256'].items():
        if key in sources and sources[key] != sha:
            raise ValueError('Action source hash mismatch: '+key)
if gram0['retained_sample_sha256'] != sources['local-high-input-samples.json']:
    raise ValueError('Gram/sample source mismatch')
expected = {'bandwidth_N': 64, 'trial_gamma_terms': 1024,
            'trial_prime_cutoff': 64, 'sample_spacing_h': '1/256',
            'even': True, 'indices': '[0,1024]'}
if any(samples.get(k) != v for k, v in expected.items()):
    raise ValueError('Fixed vector/sample parameters mismatch')
if len(samples['samples']) != 1025:
    raise ValueError('Complete1025 source rows required')

started = time.perf_counter()
timings = {}
length, last = 32768, 1024
h, R = arb(fmpq(1, 256)), arb(128)
c, alpha, delta = arb(fmpq(3, 8)), arb(fmpq(1, 8)), arb(fmpq(1, 8))
nu = arb.pi()/h
H = [[arb(0) for _ in range(length)] for _ in range(4)]
Z = [[arb(0) for _ in range(last+1)] for _ in range(4)]
roots = []
v0 = []
for k, row in enumerate(samples['samples']):
    if row['index'] != k or len(row['H']) != 4 or len(row['PH']) != 4:
        raise ValueError('Ordered four-column H/PH rows required')
    s = root.coherent_root(acb(arb(k)*h)).real
    roots.append(s)
    v0.append(2*(arb(k)*h/2).cosh()*s)
    for a in range(4):
        H[a][k] = reader.span(row['H'][a])
        Z[a][k] = H[a][k]-reader.span(row['PH'][a])
        if k:
            H[a][-k] = H[a][k]
means = [sum((h*(2 if k else 1)*v0[k]*Z[a][k]
              for k in range(last+1)), arb(0)) for a in range(4)]
timings['saved_input_and_mean'] = time.perf_counter()-started

start = time.perf_counter()
symbols = [arb(0) for _ in range(length)]
psi0 = arb(fmpq(1, 4)).digamma()
for n in range(1, length//2+1):
    xi = 2*arb.pi()*n/R
    symbols[n] = acb(arb(fmpq(1, 4)), xi/2).digamma().real-psi0
    if n != length//2:
        symbols[-n] = symbols[n]
gamma_core = []
for a in range(4):
    sz = [acb(0) for _ in range(length)]
    for k in range(last+1):
        sz[k] = acb(roots[k]*Z[a][k])
        if k:
            sz[-k] = sz[k]
    transformed = acb.dft(sz)
    output = acb.dft([symbols[n]*transformed[n] for n in range(length)], inverse=True)
    gamma_core.append([output[k].real for k in range(last+1)])
timings['full_Gamma'] = time.perf_counter()-start

start = time.perf_counter()
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
    raise ValueError('Complete retained prime-power family mismatch')
Hhat = [acb.dft([acb(v) for v in row]) for row in H]
phase = {m: ((arb(m)/4).sin(), (arb(m)/4).cos())
         for m in range(-2*last, 2*last+1)}
prime_core = [[arb(0) for _ in range(last+1)] for _ in range(4)]
offgrid_error = exact(coefficients['off_lattice_Z_analytic_pointwise_error_upper'])
padding_checks = 0
for n, weight in prime_terms:
    tau = arb(n).log()
    sin_high = (nu*tau).sin()
    sin_low, cos_low = (64*tau).sin(), (64*tau).cos()
    shifted_kernel = [acb(0) for _ in range(length)]
    for m, (sin_m, cos_m) in phase.items():
        t = arb(m)*h+tau
        if t.contains(0):
            raise RuntimeError('Prime shift denominator not separated from zero')
        cardinal = (-1 if m % 2 else 1)*sin_high
        lower = sin_m*cos_low+cos_m*sin_low
        shifted_kernel[m % length] = acb((cardinal-lower)/(arb.pi()*t))
    khat = acb.dft(shifted_kernel)
    shifted = [acb.dft([khat[j]*Hhat[a][j] for j in range(length)], inverse=True)
               for a in range(4)]
    # Independent direct finite sums check the implemented padding/phase
    # arithmetic only; the off-grid allowance supplies the analytic tail.
    if n in (2, 64):
        for k in (0, 256, last):
            for a in range(4):
                direct = arb(0)
                for j in range(-last, last+1):
                    t = arb(k-j)*h+tau
                    direct += h*H[a][j % length]*((nu*t).sin()-(64*t).sin())/(arb.pi()*t)
                if not direct.overlaps(h*shifted[a][k].real):
                    raise RuntimeError('Shifted finite sinc/padding mismatch')
                padding_checks += 1
    for k in range(last+1):
        x = arb(k)*h
        sp = root.coherent_root(acb(x+tau)).real
        sm = root.coherent_root(acb(x-tau)).real
        for a in range(4):
            # Evenness transports the negative shift through output-k.
            zp = h*shifted[a][k].real+arb(0, offgrid_error.upper())
            zm = h*shifted[a][(-k) % length].real+arb(0, offgrid_error.upper())
            prime_core[a][k] += weight*(sp*zp+sm*zm)
timings['prime_off_grid_and_padding_checks'] = time.perf_counter()-start

start = time.perf_counter()
core_error = exact(coefficients['same_high_core_gamma_and_mean_analytic_error_upper'])
cgamma = psi0-arb.pi().log()
HZ = [[arb(0) for _ in range(length)] for _ in range(4)]
maximum_HZ_radius = arb(0)
for a in range(4):
    for k in range(last+1):
        s = roots[k]
        value = (s*gamma_core[a][k]+cgamma*s*s*Z[a][k]
                 -s*prime_core[a][k]+c*v0[k]*means[a]
                 +arb(0, core_error.upper()))
        maximum_HZ_radius = maximum_HZ_radius.max(value.rad())
        HZ[a][k] = value
        if k:
            HZ[a][-k] = value
kernel = [acb(0) for _ in range(length)]
for m in range(-2*last, 2*last+1):
    t = arb(m)*h
    kernel[m % length] = acb(arb(64)/arb.pi() if m == 0 else (64*t).sin()/(arb.pi()*t))
khat = acb.dft(kernel)
PHZ, QHZ = [], []
projection_error = exact(coefficients['retained_prime_full_HZ_sinc_projection_pointwise_error_upper'])
maximum_QHZ_radius = arb(0)
for a in range(4):
    transformed = acb.dft([acb(v) for v in HZ[a]])
    output = acb.dft([khat[j]*transformed[j] for j in range(length)], inverse=True)
    projected = [h*output[k].real+arb(0, projection_error.upper()) for k in range(last+1)]
    PHZ.append(projected)
    QHZ.append([HZ[a][k]-projected[k] for k in range(last+1)])
    for value in QHZ[-1]:
        maximum_QHZ_radius = maximum_QHZ_radius.max(value.rad())
timings['local_action_and_continuous_projection'] = time.perf_counter()-start

start = time.perf_counter()
line_u = exact(strip['common_high_line_L2_operator_upper'])
line_hz = exact(coefficients['retained_prime_full_HZ_line_L2_upper'])
ratio = (-2*arb.pi()*delta/h).exp()
q_zhz = 2*line_u*line_hz*ratio/(1-ratio)
q_hzhz = 2*line_hz**2*ratio/(1-ratio)
b = arb.pi()/2
FB = exact(high['trial_B_frobenius_upper'])
Zsup = (exact(projection['forward_pointwise_envelope_coefficient_upper'])*(2/b)**2*arb(-2).exp()
        +(arb(64)/arb.pi()).sqrt()*exact(high['retained_forward_derivative_norm_upper'][0])*FB)
HZsup = exact(coefficients['retained_prime_full_HZ_pointwise_envelope_coefficient_upper'])*(2/b)**2*arb(-2).exp()
QHZsup = HZsup+(arb(64)/arb.pi()).sqrt()*line_hz
JHZ = exact(coefficients['retained_prime_full_HZ_physical_and_lattice_L1_tail_upper'])
tail_zhz, tail_hzhz = Zsup*JHZ, QHZsup*JHZ
ZH = [[arb(0) for _ in range(4)] for _ in range(4)]
QQ = [[arb(0) for _ in range(4)] for _ in range(4)]
for k in range(last+1):
    factor = h*(2 if k else 1)
    for i in range(4):
        for j in range(4):
            ZH[i][j] += factor*Z[i][k]*HZ[j][k]
            QQ[i][j] += factor*HZ[i][k]*QHZ[j][k]
checks = {}
for label, G, error in (('Z_HZ', ZH, q_zhz+tail_zhz),
                        ('QHZ_Gram', QQ, q_hzhz+tail_hzhz)):
    for row in G:
        for j in range(4):
            row[j] += arb(0, error.upper())
    checks[label] = 0
    for i in range(4):
        for j in range(i):
            if not G[i][j].overlaps(G[j][i]):
                raise RuntimeError('Action Gram transpose mismatch: '+label)
            checks[label] += 1
ZZ = [[reader.span(v) for v in row] for row in gram0['entry_intervals']]
ZC64 = [[alpha*ZZ[i][j]+ZH[i][j] for j in range(4)] for i in range(4)]
CC64 = [[alpha**2*ZZ[i][j]+alpha*(ZH[i][j]+ZH[j][i])+QQ[i][j]
         for j in range(4)] for i in range(4)]
normZ = exact(gram0['Z_operator_norm_upper'])
normCZ64 = row_norm(CC64)
omitted_prime = exact(forward['full_two_direction_prime_action_error_upper'])*normZ
ZC_error = normZ*omitted_prime
CC_error = 2*normCZ64*omitted_prime+omitted_prime**2
ZC = [[v+arb(0, ZC_error.upper()) for v in row] for row in ZC64]
CC = [[v+arb(0, CC_error.upper()) for v in row] for row in CC64]
timings['whole_line_localized_Grams'] = time.perf_counter()-start

saved = {
    'scope': 'Actual local HZ and continuous PHZ enclosures for the full-Gamma primes-through64 action on the fixed finite-J Z columns; full prime omission is an L2 allowance, not a pointwise enclosure',
    'input_sha256': sources,
    'action_coefficient_sha256': hashlib.sha256(coefficient_bytes).hexdigest(),
    'precision_bits': ctx.prec, 'bandwidth_N': 64,
    'Z_definition_gamma_terms': 1024, 'action_gamma': 'full',
    'action_prime_cutoff': 64, 'sample_spacing_h': '1/256',
    'even': True, 'indices': '[0,1024]',
    'samples': [{'index': k, 'HZ': [interval(HZ[a][k]) for a in range(4)],
                 'PHZ': [interval(PHZ[a][k]) for a in range(4)]} for k in range(last+1)]
}
saved_bytes = (json.dumps(saved, separators=(',', ':'))+'\n').encode()
sample_path = args.samples_output or canonical/'high-full-action-samples.json'
sample_path.write_bytes(saved_bytes)
result = {
    'scope': 'Paper-model directed full-Gamma high action and localized whole-line four-column action Grams with complete omitted-prime L2 transport; no full common residual Gram or restricted Schur sign',
    'input_sha256': sources,
    'action_coefficient_sha256': hashlib.sha256(coefficient_bytes).hexdigest(),
    'retained_sample_sha256': hashlib.sha256(saved_bytes).hexdigest(),
    'retained_sample_filename': sample_path.name,
    'precision_bits': ctx.prec, 'DFT_length': length,
    'physical_period': 128, 'input_and_local_output_radius': 4,
    'sample_spacing_h': '1/256', 'action_gamma': 'full',
    'action_prime_powers': [n for n, _ in prime_terms],
    'Z_definition_gamma_terms': 1024,
    'direct_shifted_sinc_scalar_overlap_checks': padding_checks,
    'transpose_overlap_checks': checks, 'timings_seconds': timings,
    'maximum_local_HZ_column_radius_upper': upper(maximum_HZ_radius),
    'maximum_local_QHZ_column_radius_upper': upper(maximum_QHZ_radius),
    'Z_HZ_integral_quadrature_error_upper': upper(q_zhz),
    'Z_HZ_omitted_lattice_integral_error_upper': upper(tail_zhz),
    'QHZ_Gram_integral_quadrature_error_upper': upper(q_hzhz),
    'QHZ_Gram_omitted_lattice_integral_error_upper': upper(tail_hzhz),
    'complete_omitted_prime_L2_Z_action_upper': upper(omitted_prime),
    'complete_prime_Z_CZ_entry_perturbation_upper': upper(ZC_error),
    'complete_prime_CZ_Gram_entry_perturbation_upper': upper(CC_error),
    'retained_prime_CZ_operator_norm_upper': upper(normCZ64),
    'full_prime_CZ_operator_norm_upper': upper(normCZ64+omitted_prime),
    'retained_Z_HZ_entry_intervals': [[interval(v) for v in row] for row in ZH],
    'retained_QHZ_Gram_entry_intervals': [[interval(v) for v in row] for row in QQ],
    'full_Z_CZ_entry_intervals': [[interval(v) for v in row] for row in ZC],
    'full_CZ_Gram_entry_intervals': [[interval(v) for v in row] for row in CC],
    'full_Z_CZ_entry_displays': [[str(v) for v in row] for row in ZC],
    'full_CZ_Gram_entry_displays': [[str(v) for v in row] for row in CC],
    'four_column_high_action_evaluated': True,
    'common_residual_Gram_evaluated': False,
    'restricted_Schur_sign': 'Unverified', 'Lean_certification': False,
}
(args.output or canonical/'high-full-action-result.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
