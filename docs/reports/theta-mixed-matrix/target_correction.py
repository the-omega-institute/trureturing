"""Choose a new exact correction map for a new target of the same theta form.

Saved actions and Grams are reused; no old producer or comparison is replayed.
All paper operator, exact-ground, minimal-domain and supplier premises remain.
"""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from flint import arb, arb_mat, ctx, fmpq


def exact(item):
    m, e = item['dyadic']
    value = arb(int(m))*arb(2)**int(e)
    if not value.is_finite():
        raise ValueError('Finite saved endpoint required')
    return value


def span(item):
    lo, hi = item['lower_dyadic'], item['upper_dyadic']
    a, b = arb(int(lo[0]))*arb(2)**int(lo[1]), arb(int(hi[0]))*arb(2)**int(hi[1])
    if not a.is_finite() or not b.is_finite() or not a <= b:
        raise ValueError('Ordered finite saved interval required')
    return a.union(b)


def matrix(items, rows, columns):
    if len(items) != rows or any(len(row) != columns for row in items):
        raise ValueError('Exact matrix shape required')
    return arb_mat([[span(v) for v in row] for row in items])


def interval(value):
    if not value.is_finite():
        raise ValueError('Finite matrix interval required')
    return {'lower_dyadic': [str(v) for v in value.lower().man_exp()],
            'upper_dyadic': [str(v) for v in value.upper().man_exp()]}


def endpoint(value, lower=False):
    if not value.is_finite():
        raise ValueError('Finite scalar endpoint required')
    value = value.lower() if lower else value.upper()
    return {'display': str(value), 'dyadic': [str(v) for v in value.man_exp()]}


def symmetric(value):
    return (value+value.transpose())/2


def row_norm(value):
    return max(sum((abs(value[i, j]) for j in range(value.ncols())), arb(0)).upper()
               for i in range(value.nrows())).upper()


def ldl(value):
    n = value.nrows()
    lower = [[arb(0) for _ in range(n)] for _ in range(n)]
    pivots = []
    for j in range(n):
        pivot = value[j, j]-sum((lower[j][k]*lower[j][k]*pivots[k]
                                for k in range(j)), arb(0))
        if not pivot > 0:
            return pivots, j, pivot
        pivots.append(pivot)
        lower[j][j] = arb(1)
        for i in range(j+1, n):
            lower[i][j] = (value[i, j]-sum((lower[i][k]*lower[j][k]*pivots[k]
                                          for k in range(j)), arb(0)))/pivot
    return pivots, None, None


def quantize_midpoint(value):
    m, e = value.mid().man_exp()
    exponent = int(e)+40
    q = Fraction(int(m))*(2**exponent if exponent >= 0 else Fraction(1, 2**-exponent))
    return str(round(q))


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--canonical', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--output', type=Path)
parser.add_argument('--target-c', default='9/20')
parser.add_argument('--finite-margin', default='1/100')
parser.add_argument('--gap', default='1/1000')
parser.add_argument('--precision', type=int, default=192)
args = parser.parse_args()
if args.precision < 192:
    parser.error('At least 192 bits required')
try:
    target, finite_margin, gap = (fmpq(v) for v in (args.target_c, args.finite_margin, args.gap))
except (ValueError, TypeError):
    parser.error('Exact rational target and margins required')
if not fmpq(3, 8) < target < fmpq(1, 2) or finite_margin <= 0 or gap < 0:
    parser.error('Target must be in (3/8,1/2), finite margin positive and gap nonnegative')
ctx.prec = args.precision
canonical = args.canonical.resolve()
output = args.output or Path(__file__).resolve().with_name(
    'target-correction-c'+str(target).replace('/', '-')+'-result.json')
sources = {}


def load(name):
    raw = (canonical/name).read_bytes()
    sources[name] = hashlib.sha256(raw).hexdigest()
    return json.loads(raw)


low = load('low-common-action-result.json')
high = load('high-full-action-result.json')
gram = load('local-z-gram-result.json')
moments = load('exact-ground-moments-result.json')
restricted_old = load('restricted-schur-result.json')
transport = load('sharper-threshold-transport-result.json')
coupling = load('actual-coupling-result.json')
forward = load('forward-action-result.json')
trials = load('common-trials.json')
for supplier in (low, high, gram, moments, restricted_old, transport, coupling):
    for name, sha in supplier['input_sha256'].items():
        if name in sources and sources[name] != sha:
            raise ValueError('Target correction supplier hash mismatch: '+name)
if (low['bandwidth_N'], low['low_columns'], low['action_gamma'], low['core_radius'],
    low['sample_spacing_h'], low['physical_period']) != (64, 95, 'full', 4, '1/256', 128):
    raise ValueError('The same evaluated full-Gamma low family is required')
if not low['low_actions_evaluated'] or not low['low_and_mixed_blocks_evaluated']:
    raise ValueError('Evaluated low and mixed blocks required')
if (high['action_gamma'], high['Z_definition_gamma_terms']) != ('full', 1024):
    raise ValueError('Full action on the unchanged finite-J1024 Z required')
if not high['four_column_high_action_evaluated'] or low['action_prime_powers'] != high['action_prime_powers']:
    raise ValueError('Same evaluated retained prime family required')
if (moments['bandwidth_N'], moments['orthonormal_columns']) != (64, 95):
    raise ValueError('The same exact ground components required')
if low['ground_moment_sha256'] != sources['exact-ground-moments-result.json']:
    raise ValueError('Common exact ground binding required')
if not restricted_old['ground_component_uncertainty_transported']:
    raise ValueError('The supplied true-ground norm must have transported uncertainty')
if (restricted_old['target_c'], restricted_old['low_columns'], restricted_old['bandwidth_N']) != ('3/8', 95, 64):
    raise ValueError('The inherited ground norm has incompatible parameters')
if transport['base_c'] != '3/8' or transport['high_gap_supplier'] != 'sharper-exterior-result.json':
    raise ValueError('Same stronger base exterior supplier required')
if coupling['base_c'] != '3/8' or not coupling['joint_comparison_checked']:
    raise ValueError('Accepted actual base coupling cap required')
if trials['coefficient_exponent'] != -40:
    raise ValueError('The inherited basis and Z definition require exponent -40')

g = arb(target-fmpq(3, 8))
delta = (exact(transport['base_high_gap_lower'])-g).lower()
result = {
    'scope': 'New target-dependent exact correction for the same paper form; saved actions reused, all operator/ground/domain/numerical premises retained; no Lean, cofinal, RH or full Robin certificate',
    'input_sha256': sources, 'precision_bits': ctx.prec,
    'base_c': '3/8', 'target_c': str(target),
    'finite_margin_exact': str(finite_margin), 'joint_gap_test_exact': str(gap),
    'bandwidth_N': 64, 'low_columns': 95, 'restricted_columns': 94,
    'new_correction_map_selected': False, 'saved_actions_recomputed': False,
    'same_ground_and_minimal_domain_required': True,
    'LDL_pivots_are_eigenvalues': False, 'cofinal_RH_and_full_Robin': 'Unresolved',
    'Lean_certification': False,
}
if not delta > 0:
    result.update({'comparison_checked': False, 'failed_stage': 'exterior_gap',
                   'exterior_gap_interval': interval(delta)})
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'target_c': str(target), 'comparison_checked': False,
                      'failed_stage': 'exterior_gap'}))
    raise SystemExit(0)

enorm = span(restricted_old['direction_norm_interval'])
enlower = enorm.lower()
if not 0 < enlower <= 1:
    raise ValueError('The same unit-ground component norm must lie in (0,1]')
ground_remainder = (1-enlower*enlower).sqrt().upper()
epsilon = (exact(transport['polynomial_H_tail_upper'])+g*ground_remainder).upper()
knorm = (exact(coupling['complete_K_operator_norm_upper'])+g*ground_remainder).upper()
alpha = arb(fmpq(1, 8))-g
d = (epsilon*(1+knorm/delta)).upper()
gamma = (alpha-d).lower()
if not gamma > 0:
    raise ValueError('Positive complementary low gap required')
beta = (d*d/gamma).upper()

TLL = matrix(low['retained_TLL_entry_intervals'], 95, 95)
KK = matrix(low['retained_K_Gram_entry_intervals'], 95, 95)
J = matrix(low['retained_K_Z_entry_intervals'], 95, 4)
M0 = matrix(low['retained_K_CZ_entry_intervals'], 95, 4)
ZZ = symmetric(matrix(gram['entry_intervals'], 4, 4))
ZH = matrix(high['retained_Z_HZ_entry_intervals'], 4, 4)
QQ = matrix(high['retained_QHZ_Gram_entry_intervals'], 4, 4)
alpha0 = arb(fmpq(1, 8))
ZC0 = alpha0*ZZ+ZH
CC0 = alpha0*alpha0*ZZ+alpha0*(ZH+ZH.transpose())+QQ
ZC = ZC0-g*ZZ
CC = symmetric(CC0-g*(ZC0+ZC0.transpose())+g*g*ZZ)
Mbar = M0-g*J
selection = CC.inv()*Mbar.transpose()
raw_a = [[quantize_midpoint(selection[i, j]) for j in range(95)] for i in range(4)]
A = arb_mat([[arb(int(v))*arb(2)**-40 for v in row] for row in raw_a])
identity = arb_mat([[int(i == j) for j in range(95)] for i in range(95)])
Fbar = symmetric(TLL-g*identity-J*A-A.transpose()*J.transpose()+A.transpose()*ZC*A)
RGram = symmetric(KK-Mbar*A-A.transpose()*Mbar.transpose()+A.transpose()*CC*A)
rho = row_norm(RGram).sqrt().upper()
norm_a = sum((A[i, j]*A[i, j] for i in range(4) for j in range(95)), arb(0)).sqrt().upper()
norm_z = exact(gram['Z_operator_norm_upper'])
za = (norm_z*norm_a).upper()
rs = (1+za*za).sqrt().upper()
prime = exact(forward['full_two_direction_prime_action_error_upper'])
if not prime >= 0 or not norm_z > 0:
    raise ValueError('Nonnegative prime error and positive supplied Z norm required')
eps_r = (prime*rs).upper()
form_error = (prime*rs*rs).upper()
gram_error = (2*rho*eps_r+eps_r*eps_r).upper()
prime_budget = (form_error+gram_error/delta).upper()
lower = Fbar-RGram/delta-prime_budget*identity

e = [span(v) for v in moments['component_intervals']]
if len(e) != 95:
    raise ValueError('Exactly 95 ground components required')
v = e[:]
v[0] += enorm
vv = sum((x*x for x in v), arb(0))
if not vv > 0:
    raise ValueError('Stable true-ground Householder denominator required')
frame = arb_mat([[arb(int(i == j))-2*v[i]*v[j]/vv for j in range(1, 95)] for i in range(95)])
restricted = symmetric(frame.transpose()*lower*frame)
test = restricted-(beta+arb(finite_margin))*arb_mat([[int(i == j) for j in range(94)] for i in range(94)])
pivots, failure, failed_pivot = ldl(test)
result.update({
    'new_correction_map_selected': True, 'coefficient_exponent': -40,
    'new_correction_map_A': raw_a,
    'selection_rule': 'Exact nearest dyadics from midpoints of the new retained 4x4 least-squares solve; final comparisons use exact selected dyadics',
    'target_high_gap_lower': endpoint(delta, lower=True),
    'ground_unresolved_norm_upper': endpoint(ground_remainder),
    'target_H_low_tail_upper': endpoint(epsilon),
    'target_K_operator_norm_upper': endpoint(knorm),
    'target_low_tail_allowance_upper': endpoint(d),
    'target_complementary_low_gap_lower': endpoint(gamma, lower=True),
    'target_second_Schur_allowance_upper': endpoint(beta),
    'new_A_frobenius_upper': endpoint(norm_a), 'new_ZA_norm_upper': endpoint(za),
    'new_joint_trial_norm_upper': endpoint(rs),
    'retained_bar_residual_norm_upper': endpoint(rho),
    'complete_prime_residual_error_upper': endpoint(eps_r),
    'complete_prime_form_error_upper': endpoint(form_error),
    'complete_prime_Gram_error_upper': endpoint(gram_error),
    'complete_prime_Schur_allowance_upper': endpoint(prime_budget),
    'new_bar_residual_Gram_entry_intervals': [[interval(RGram[i, j]) for j in range(95)] for i in range(95)],
    'new_restricted_actual_Schur_lower_entry_intervals': [[interval(restricted[i, j]) for j in range(94)] for i in range(94)],
    'restricted_comparison_checked': failure is None,
    'restricted_positive_pivot_intervals': [interval(v) for v in pivots],
    'restricted_failed_pivot_index': failure,
    'restricted_failed_pivot_interval': None if failure is None else interval(failed_pivot),
})
if failure is not None:
    result.update({'comparison_checked': False, 'failed_stage': 'restricted_comparison'})
else:
    extra = (g*ground_remainder*(1+ground_remainder*za)).upper()
    le = (za+(rho+eps_r+extra)/delta).upper()
    lt = (epsilon/delta).upper()
    b = (d/gamma).upper()
    lift = arb_mat([[1, 0, 0], [b, 1, 0], [(le+lt*b).upper(), lt, 1]])
    metric = lift.transpose()*lift
    energy = arb_mat([[arb(finite_margin), 0, 0], [0, gamma, 0], [0, 0, delta]])
    comparison = energy-arb(gap)*metric
    joint_pivots, joint_failure, joint_failed = ldl(comparison)
    result.update({
        'actual_bar_rank_one_residual_error_upper': endpoint(extra),
        'actual_inverse_coupling_on_E_upper': endpoint(le),
        'actual_inverse_coupling_on_tail_upper': endpoint(lt),
        'joint_lifting_matrix_entry_intervals': [[interval(lift[i, j]) for j in range(3)] for i in range(3)],
        'joint_positive_pivot_intervals': [interval(v) for v in joint_pivots],
        'joint_failed_pivot_index': joint_failure,
        'joint_failed_pivot_interval': None if joint_failure is None else interval(joint_failed),
        'comparison_checked': joint_failure is None,
        'failed_stage': None if joint_failure is None else 'joint_comparison',
    })
    if joint_failure is None:
        inverse_row = row_norm(comparison.inv())
        metric_row = row_norm(metric)
        excess = (1/(inverse_row*metric_row)).lower()
        result.update({'joint_inverse_norm_upper': endpoint(inverse_row),
                       'lifting_norm_squared_upper': endpoint(metric_row),
                       'target_ground_orthogonal_gap_lower': endpoint(arb(gap)+excess, lower=True)})
output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k: v for k, v in result.items() if k.endswith('_upper') or k.endswith('_lower') or
                  k in ('target_c', 'comparison_checked', 'failed_stage', 'restricted_failed_pivot_index')}, indent=2))
