"""Use saved actual coupling Grams in a joint three-block coercivity bound.

No action, integration grid or previous restricted matrix is recomputed.
All operator, exact-ground, analytic and numerical suppliers remain premises.
"""
import argparse
import hashlib
import json
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
    a = arb(int(lo[0]))*arb(2)**int(lo[1])
    b = arb(int(hi[0]))*arb(2)**int(hi[1])
    if not a.is_finite() or not b.is_finite() or not a <= b:
        raise ValueError('Ordered finite saved interval required')
    return a.union(b)


def matrix(items, rows, columns):
    if len(items) != rows or any(len(row) != columns for row in items):
        raise ValueError('Exact matrix shape required')
    return arb_mat([[span(v) for v in row] for row in items])


def interval(value):
    if not value.is_finite():
        raise ValueError('Finite matrix endpoint required')
    return {'lower_dyadic': [str(v) for v in value.lower().man_exp()],
            'upper_dyadic': [str(v) for v in value.upper().man_exp()]}


def endpoint(value, lower=False):
    if not value.is_finite():
        raise ValueError('Finite coercivity endpoint required')
    value = value.lower() if lower else value.upper()
    return {'display': str(value), 'dyadic': [str(v) for v in value.man_exp()]}


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


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--canonical', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name('actual-coupling-result.json'))
parser.add_argument('--target-c', default='21/50')
parser.add_argument('--precision', type=int, default=192)
args = parser.parse_args()
if args.precision < 192:
    parser.error('At least 192 bits required')
try:
    target = fmpq(args.target_c)
except (ValueError, TypeError):
    parser.error('Exact rational target required')
if not fmpq(3, 8) <= target < fmpq(1, 2):
    parser.error('Target must lie in [3/8,1/2)')
ctx.prec = args.precision
canonical = args.canonical.resolve()
sources = {}


def load(name):
    raw = (canonical/name).read_bytes()
    sources[name] = hashlib.sha256(raw).hexdigest()
    return json.loads(raw)


low = load('low-common-action-result.json')
forward = load('forward-action-result.json')
transport = load('sharper-threshold-transport-result.json')
stable = load('stable-ground-result.json')
gram = load('local-z-gram-result.json')
trials = load('common-trials.json')
restricted = load('restricted-schur-result.json')
for supplier in (low, transport, stable, gram, restricted):
    for name, sha in supplier['input_sha256'].items():
        if name in sources and sources[name] != sha:
            raise ValueError('Actual coupling supplier hash mismatch: '+name)
if (low['bandwidth_N'], low['low_columns'], low['action_gamma']) != (64, 95, 'full'):
    raise ValueError('Saved full-Gamma bandwidth 64 and 95-column family required')
if not low['low_actions_evaluated'] or not low['low_and_mixed_blocks_evaluated']:
    raise ValueError('Evaluated common low suppliers required')
if (transport['base_c'], transport['target_c'], transport['high_gap_supplier']) != ('3/8', '41/100', 'sharper-exterior-result.json'):
    raise ValueError('Accepted stronger high gap for the same base operator required')
if (stable['alpha'], stable['rank']) != ('1/8', 95):
    raise ValueError('Same stable-ground parameters required')
if not restricted['restricted_lower_comparison_checked'] or not restricted['ground_component_uncertainty_transported']:
    raise ValueError('Checked comparison on the true ground complement required')
if (restricted['target_c'], restricted['bandwidth_N'], restricted['low_columns'],
    fmpq(restricted['extra_gap_exact_rational'])) != ('3/8', 64, 95, fmpq(1, 10)):
    raise ValueError('Accepted fixed-base restricted comparison required')
if restricted['second_schur_allowance_upper'] != stable['second_schur_allowance_upper']:
    raise ValueError('The old comparison allowance must match its supplied constant')
raw_a = trials['correction_map_A']
if trials['coefficient_exponent'] != -40 or len(raw_a) != 4 or any(len(row) != 95 for row in raw_a):
    raise ValueError('The same exact 4x95 correction map is required')

kk = matrix(low['retained_K_Gram_entry_intervals'], 95, 95)
epsilon = exact(transport['polynomial_H_tail_upper'])
prime_error = exact(forward['full_two_direction_prime_action_error_upper'])
delta = exact(transport['base_high_gap_lower'])
if not epsilon >= 0 or not prime_error >= 0 or not delta > 0:
    raise ValueError('Nonnegative tails and positive high gap required')
k64_squared = row_norm(kk)
ke = (k64_squared.sqrt()+prime_error).upper()
knorm = (ke*ke+epsilon*epsilon).sqrt().upper()
d = (epsilon*(1+knorm/delta)).upper()
gamma = (arb(fmpq(1, 8))-d).lower()
if not gamma > 0:
    raise ValueError('Positive complementary low gap required')
beta = (d*d/gamma).upper()
a = (arb(fmpq(1, 10))+exact(stable['second_schur_allowance_upper'])-beta).lower()
if not a > 0:
    raise ValueError('Positive restricted second-Schur margin required')

A = arb_mat([[arb(int(v))*arb(2)**-40 for v in row] for row in raw_a])
gz = matrix(gram['entry_intervals'], 4, 4)
gz = (gz+gz.transpose())/2
gz_pivots, failure, unused = ldl(gz)
if failure is not None:
    raise ValueError('Positive actual Z Gram required for the inverse cap')
cap_matrix = arb(fmpq(49, 100))*gz.inv()-A*A.transpose()
cap_matrix = (cap_matrix+cap_matrix.transpose())/2
cap_pivots, failure, unused = ldl(cap_matrix)
if failure is not None:
    raise ValueError('The actual ZA squared norm cap 49/100 was not certified')
rho = (exact(restricted['residual_retained_operator_norm_upper'])
       +exact(restricted['complete_prime_joint_residual_error_upper'])).upper()
le = (arb(fmpq(7, 10))+rho/delta).upper()
lt = (epsilon/delta).upper()
b = (d/gamma).upper()
lifting = arb_mat([[1, 0, 0], [b, 1, 0], [(le+lt*b).upper(), lt, 1]])
metric = lifting.transpose()*lifting
energy = arb_mat([[a, 0, 0], [0, gamma, 0], [0, 0, delta]])
base_gap = arb(target-fmpq(3, 8))
comparison = energy-base_gap*metric
pivots, failure, failed_pivot = ldl(comparison)
passed = failure is None
result = {
    'scope': 'Actual K/ZA norms and joint three-block form bound under the unchanged paper operator/ground/supplier premises; no action or old matrix reassembly, Lean, cofinal, RH or Robin certificate',
    'input_sha256': sources, 'precision_bits': ctx.prec,
    'base_c': '3/8', 'target_c': str(target), 'base_gap_exact': str(target-fmpq(3, 8)),
    'retained_K_Gram_norm_squared_upper': endpoint(k64_squared),
    'complete_K_on_E_norm_upper': endpoint(ke),
    'complete_K_operator_norm_upper': endpoint(knorm),
    'new_low_tail_upper': endpoint(d),
    'new_complementary_low_gap_lower': endpoint(gamma, lower=True),
    'new_second_schur_allowance_upper': endpoint(beta),
    'new_finite_center_gap_lower': endpoint(a, lower=True),
    'ZA_squared_norm_cap_exact': '49/100',
    'Z_Gram_positive_pivot_intervals': [interval(v) for v in gz_pivots],
    'weighted_ZA_cap_positive_pivot_intervals': [interval(v) for v in cap_pivots],
    'inverse_coupling_on_E_upper': endpoint(le),
    'inverse_coupling_on_low_complement_upper': endpoint(lt),
    'low_shear_upper': endpoint(b),
    'joint_lifting_matrix_entry_intervals': [[interval(lifting[i, j]) for j in range(3)] for i in range(3)],
    'energy_diagonal_lower': [endpoint(energy[i, i], lower=True) for i in range(3)],
    'joint_comparison_pivot_intervals': [interval(v) for v in pivots],
    'joint_comparison_failed_pivot_index': failure,
    'joint_comparison_failed_pivot_interval': None if passed else interval(failed_pivot),
    'joint_comparison_checked': passed, 'pivots_are_eigenvalues': False,
    'same_ground_and_operator_family_required': True,
    'cofinal_RH_and_full_Robin': 'Unresolved', 'Lean_certification': False,
}
if passed:
    inverse_row = row_norm(comparison.inv())
    metric_row = row_norm(metric)
    excess = (1/(inverse_row*metric_row)).lower()
    result['comparison_inverse_norm_upper'] = endpoint(inverse_row)
    result['lifting_operator_norm_squared_upper'] = endpoint(metric_row)
    result['target_ground_orthogonal_gap_lower'] = endpoint(excess, lower=True)
    result['base_ground_orthogonal_gap_lower'] = endpoint(base_gap+excess, lower=True)
args.output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k: v for k, v in result.items() if k.endswith('_upper') or k.endswith('_lower') or k in ('target_c', 'joint_comparison_checked')}, indent=2))
