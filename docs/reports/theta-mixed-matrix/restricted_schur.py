"""Assemble the common residual Gram and check the exact-ground restriction.

Classical norm transport, Householder and interval LDL are reused methods.
All paper operator/analytic suppliers remain premises; no Lean certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
from flint import arb, arb_mat, ctx, fmpq


def exact(item):
    m, e = item['dyadic']
    return arb(int(m))*arb(2)**int(e)


def span(item):
    lo, hi = item['lower_dyadic'], item['upper_dyadic']
    a, b = arb(int(lo[0]))*arb(2)**int(lo[1]), arb(int(hi[0]))*arb(2)**int(hi[1])
    if not a <= b:
        raise ValueError('Ordered finite intervals required')
    return a.union(b)


def matrix(values, rows, columns):
    if len(values) != rows or any(len(row) != columns for row in values):
        raise ValueError('Exact matrix shape required')
    return arb_mat([[span(v) for v in row] for row in values])


def interval(v):
    if not v.is_finite():
        raise ValueError('Finite matrix enclosure required')
    return {'lower_dyadic': [str(x) for x in v.lower().man_exp()],
            'upper_dyadic': [str(x) for x in v.upper().man_exp()]}


def bound(v):
    if not v.is_finite():
        raise ValueError('Finite operator allowance required')
    v = v.upper()
    return {'display': str(v), 'dyadic': [str(x) for x in v.man_exp()]}


def symmetric(v):
    return (v+v.transpose())/2


def row_norm_squared(v):
    result = arb(0)
    for i in range(v.nrows()):
        result = result.max(sum((abs(v[i, j]) for j in range(v.ncols())), arb(0)).upper())
    return result.upper()


def interval_ldl(v):
    n = v.nrows()
    lower = [[arb(0) for _ in range(n)] for _ in range(n)]
    pivots = []
    for j in range(n):
        pivot = v[j, j]-sum(((lower[j][k]*lower[j][k])*pivots[k] for k in range(j)), arb(0))
        if not pivot > 0:
            return pivots, j, pivot
        pivots.append(pivot)
        lower[j][j] = arb(1)
        for i in range(j+1, n):
            lower[i][j] = (v[i, j]-sum((lower[i][k]*lower[j][k]*pivots[k] for k in range(j)), arb(0)))/pivot
    return pivots, None, None


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--canonical', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--low-action', type=Path, default=Path(__file__).resolve().with_name('low-common-action-result.json'))
parser.add_argument('--moments', type=Path, default=Path(__file__).resolve().with_name('exact-ground-moments-result.json'))
parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name('restricted-schur-result.json'))
parser.add_argument('--extra-gap', default='1/10')
parser.add_argument('--precision', type=int, default=192)
args = parser.parse_args()
if args.precision < 192:
    parser.error('At least192 bits required')
ctx.prec = args.precision
try:
    gap_rational = fmpq(args.extra_gap)
except (ValueError, TypeError):
    parser.error('The extra gap must be an exact rational')
if gap_rational < 0:
    parser.error('The extra gap must be nonnegative')
canonical = args.canonical.resolve()
sources = {}


def load(path):
    raw = path.read_bytes()
    sources[path.name] = hashlib.sha256(raw).hexdigest()
    return json.loads(raw)


low = load(args.low_action)
moments = load(args.moments)
high = load(canonical/'high-full-action-result.json')
gram = load(canonical/'local-z-gram-result.json')
trials = load(canonical/'common-trials.json')
stable = load(canonical/'stable-ground-result.json')
forward = load(canonical/'forward-action-result.json')
for supplier in (low, moments, high, gram, stable):
    for name, sha in supplier['input_sha256'].items():
        if name in sources and sources[name] != sha:
            raise ValueError('Common matrix data hash mismatch: '+name)
        if (canonical/name).is_file() and hashlib.sha256((canonical/name).read_bytes()).hexdigest() != sha:
            raise ValueError('Canonical matrix supplier mismatch: '+name)
if low['ground_moment_sha256'] != sources[args.moments.name]:
    raise ValueError('Exact ground direction mismatch')
if (low['bandwidth_N'], low['low_columns'], low['action_gamma'], low['core_radius'],
    low['sample_spacing_h'], low['physical_period']) != (64, 95, 'full', 4, '1/256', 128):
    raise ValueError('Common retained operator parameters required')
if low['action_prime_powers'] != high['action_prime_powers']:
    raise ValueError('Same retained prime family required')
if not (low['low_actions_evaluated'] and low['low_and_mixed_blocks_evaluated']):
    raise ValueError('Evaluated low/mixed inputs required')
if (moments['bandwidth_N'], moments['orthonormal_columns']) != (64, 95):
    raise ValueError('Exact ground basis required')
if (high['action_gamma'], high['Z_definition_gamma_terms']) != ('full', 1024):
    raise ValueError('Full action on the fixed finite-J high family required')
if trials['coefficient_exponent'] != -40:
    raise ValueError('Exact correction-map dyadics required')
rawA = trials['correction_map_A']
if len(rawA) != 4 or any(len(row) != 95 for row in rawA):
    raise ValueError('Fixed4x95 correction map required')

started = time.perf_counter()
alpha, delta = arb(fmpq(1, 8)), arb(fmpq(383682545007734, 10**16))
A = arb_mat([[arb(int(v))*arb(2)**-40 for v in row] for row in rawA])
TLL = matrix(low['retained_TLL_entry_intervals'], 95, 95)
KK = matrix(low['retained_K_Gram_entry_intervals'], 95, 95)
J = matrix(low['retained_K_Z_entry_intervals'], 95, 4)
M = matrix(low['retained_K_CZ_entry_intervals'], 95, 4)
ZZ = matrix(gram['entry_intervals'], 4, 4)
ZH = matrix(high['retained_Z_HZ_entry_intervals'], 4, 4)
QQ = matrix(high['retained_QHZ_Gram_entry_intervals'], 4, 4)
ZC64 = alpha*ZZ+ZH
CC64 = alpha**2*ZZ+alpha*(ZH+ZH.transpose())+QQ
F64 = symmetric(TLL-J*A-A.transpose()*J.transpose()+A.transpose()*ZC64*A)
RGram64 = symmetric(KK-M*A-A.transpose()*M.transpose()+A.transpose()*CC64*A)
rho = row_norm_squared(RGram64).sqrt().upper()
normA = sum((A[i, j]**2 for i in range(4) for j in range(95)), arb(0)).sqrt().upper()
normZ = exact(gram['Z_operator_norm_upper'])
rs = (1+normZ**2*normA**2).sqrt().upper()
Ep = exact(forward['full_two_direction_prime_action_error_upper'])
epsR = (Ep*rs).upper()
form_error = (Ep*rs**2).upper()
residual_error = (2*rho*epsR+epsR**2).upper()
prime_budget = (form_error+residual_error/delta).upper()
identity = arb_mat([[int(i == j) for j in range(95)] for i in range(95)])
Flower = F64-RGram64/delta-prime_budget*identity

# The interval Householder encloses the frame of the TRUE e, not a
# floating approximation. Its exact formula makes the94 columns isometric.
e = [span(v) for v in moments['component_intervals']]
if len(e) != 95:
    raise ValueError('Exactly95 enclosed ground components required')
enorm = sum((v*v for v in e), arb(0)).sqrt()
if not enorm > 0:
    raise ValueError('Nonzero exact ground direction required')
v = e[:]
v[0] += enorm
vv = sum((x*x for x in v), arb(0))
if not vv > 0:
    raise ValueError('Stable Householder denominator required')
frame = arb_mat([[arb(int(i == j))-2*v[i]*v[j]/vv for j in range(1, 95)] for i in range(95)])
beta = exact(stable['second_schur_allowance_upper'])
restricted = symmetric(frame.transpose()*Flower*frame)
gap = arb(gap_rational)
shifted = restricted-(beta+gap)*arb_mat([[int(i == j) for j in range(94)] for i in range(94)])
pivots, failure_index, failed_pivot = interval_ldl(shifted)
success = failure_index is None
result = {
    'scope': 'Directed common residual Gram and interval LDL on the exact-ground restriction at c=3/8 under the paper operator/analytic supplier premises; no Lean certification, cofinality, Robin or RH result',
    'input_sha256': sources, 'precision_bits': ctx.prec,
    'target_c': '3/8', 'bandwidth_N': 64, 'low_columns': 95,
    'restricted_columns': 94, 'full_high_floor_lower': '0.0383682545007734',
    'retained_action_gamma': 'full', 'retained_action_prime_cutoff': 64,
    'complete_prime_transport': True,
    'residual_retained_operator_norm_upper': bound(rho),
    'A_frobenius_upper': bound(normA), 'joint_trial_operator_norm_upper': bound(rs),
    'complete_prime_joint_residual_error_upper': bound(epsR),
    'complete_prime_corrected_form_error_upper': bound(form_error),
    'complete_prime_residual_Gram_error_upper': bound(residual_error),
    'complete_prime_Schur_operator_allowance_upper': bound(prime_budget),
    'second_schur_allowance_upper': stable['second_schur_allowance_upper'],
    'extra_gap_exact_rational': str(gap_rational),
    'direction_norm_interval': interval(enorm),
    'Householder_denominator_interval': interval(vv),
    'ground_component_uncertainty_transported': True,
    'retained_common_residual_Gram_entry_intervals': [[interval(RGram64[i, j]) for j in range(95)] for i in range(95)],
    'restricted_full_Schur_lower_entry_intervals': [[interval(restricted[i, j]) for j in range(94)] for i in range(94)],
    'LDL_positive_pivot_intervals': [interval(x) for x in pivots],
    'LDL_pivots_are_eigenvalues': False,
    'LDL_failed_pivot_index': failure_index,
    'LDL_failed_pivot_interval': None if success else interval(failed_pivot),
    'restricted_lower_comparison_checked': success,
    'elapsed_seconds': time.perf_counter()-started,
    'Lean_certification': False, 'cofinal_positivity': 'Unverified',
    'RH_and_full_Robin': 'Unresolved',
}
args.output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({key: result[key] for key in ('residual_retained_operator_norm_upper',
    'complete_prime_Schur_operator_allowance_upper', 'extra_gap_exact_rational',
    'LDL_failed_pivot_index', 'restricted_lower_comparison_checked', 'elapsed_seconds')}, indent=2))
