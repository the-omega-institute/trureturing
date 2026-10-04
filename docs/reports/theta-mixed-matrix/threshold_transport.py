"""Transport the fixed theta comparison using two quantified Schur shears.

This evaluates paper-model coefficients from saved data only.
No action grid, eigenvector solve, generic theorem or Lean certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, ctx, fmpq


def exact(item):
    m, e = item['dyadic']
    return arb(int(m))*arb(2)**int(e)


def endpoint(value, lower=False):
    if not value.is_finite():
        raise ValueError('Finite transport endpoint required')
    value = value.lower() if lower else value.upper()
    return {'display': str(value), 'dyadic': [str(v) for v in value.man_exp()]}


def shear(value):
    return ((4+value*value).sqrt()+value)/2


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--canonical', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name('threshold-transport-result.json'))
parser.add_argument('--target-c', default='39/100')
parser.add_argument('--high-gap-supplier', help='Saved stronger coercivity supplier for the same fixed base operator')
parser.add_argument('--precision', type=int, default=192)
args = parser.parse_args()
if args.precision < 192:
    parser.error('At least192 bits required')
ctx.prec = args.precision
try:
    target_rational = fmpq(args.target_c)
except (ValueError, TypeError):
    parser.error('Exact rational target required')
if not 0 <= target_rational < fmpq(1, 2):
    parser.error('Target must lie in[0,1/2)')
canonical = args.canonical.resolve()
sources = {}


def load(name):
    raw = (canonical/name).read_bytes()
    sources[name] = hashlib.sha256(raw).hexdigest()
    return json.loads(raw)


stable = load('stable-ground-result.json')
center = load('sharp-center-result.json')
restricted = load('restricted-schur-result.json')
gram = load('local-z-gram-result.json')
for supplier in (stable, restricted, gram):
    for name, sha in supplier['input_sha256'].items():
        if name in sources and sources[name] != sha:
            raise ValueError('Transport supplier hash mismatch')
if not restricted['restricted_lower_comparison_checked']:
    raise ValueError('Positive exact-ground restricted comparison required')
if (restricted['target_c'], restricted['low_columns'], restricted['bandwidth_N']) != ('3/8', 95, 64):
    raise ValueError('Fixed base model required')
if (center['bandwidth_N'], center['sufficient_polynomial_degree']) != (64, 94):
    raise ValueError('Degree94 low complement required')
if fmpq(center['ellipse_radius']) != fmpq(3, 2):
    raise ValueError('The polynomial tail requires exact ellipse radius3/2')
if (stable['alpha'], stable['rank']) != ('1/8', 95):
    raise ValueError('Stable-ground parameter mismatch')
a = arb(fmpq(restricted['extra_gap_exact_rational']))
if not a > 0:
    raise ValueError('Strict positive restricted center margin required')
alpha = arb(fmpq(1, 8))
delta = arb(fmpq(383682545007734, 10**16))
if args.high_gap_supplier:
    higher = load(args.high_gap_supplier)
    if (higher['bandwidth_N'], higher['base_c'], fmpq(higher['exterior_radius'])) != (64, '3/8', fmpq(3, 2)):
        raise ValueError('Stronger high gap must belong to the same base model')
    if not higher['positive_high_gap_checked'] or not higher['exterior_above_saved_interior_checked']:
        raise ValueError('Checked stronger exterior high gap required')
    for name in ('joint-high-floor-result.json', 'derivative-bandwidth-result.json', 'strip-root.md'):
        raw = (canonical/name).read_bytes()
        if higher['input_sha256'][name] != hashlib.sha256(raw).hexdigest():
            raise ValueError('Stronger high-gap supplier hash mismatch')
    delta = exact(higher['base_high_gap_lower'])
    if not delta.is_finite() or not delta > 0:
        raise ValueError('Finite positive stronger high gap required')
d = exact(stable['L_one_sided_polynomial_tail_upper'])
gamma = alpha-d
if not gamma > 0:
    raise ValueError('Strict complementary low gap required')
b_low = (d/gamma).upper()
low_gap = (a.min(gamma).lower()/shear(b_low)**2).lower()
# SC12: epsilon94=32*Mellipse*(2/3)^94. Dividing rounded upper
# bounds for e94 and the center norm would not justify an upper epsilon.
epsilon = (32*exact(center['ellipse_column_norm_upper'])*arb(fmpq(2, 3))**94).upper()
rho = (exact(restricted['residual_retained_operator_norm_upper'])
       +exact(restricted['complete_prime_joint_residual_error_upper'])).upper()
l_center = (exact(gram['Z_operator_norm_upper'])*exact(restricted['A_frobenius_upper'])
            +rho/delta).upper()
l_tail = (epsilon/delta).upper()
l_all = (l_center*l_center+l_tail*l_tail).sqrt().upper()
global_gap = (low_gap.min(delta).lower()/shear(l_all)**2).lower()
target_margin = (global_gap-(arb(target_rational)-arb(fmpq(3, 8)))).lower()
result = {
    'scope': 'Quantified two-Schur coercivity and bounded parameter transport under the paper supplier/ground premises; no Lean, cofinal, Robin or RH conclusion',
    'input_sha256': sources, 'precision_bits': ctx.prec,
    'base_c': '3/8', 'target_c': str(target_rational),
    'complementary_low_gap_lower': endpoint(gamma, lower=True),
    'low_shear_off_diagonal_norm_upper': endpoint(b_low),
    'low_ground_orthogonal_gap_lower': endpoint(low_gap, lower=True),
    'polynomial_H_tail_upper': endpoint(epsilon),
    'full_inverse_coupling_on_E_upper': endpoint(l_center),
    'full_inverse_coupling_on_low_complement_upper': endpoint(l_tail),
    'full_inverse_coupling_operator_norm_upper': endpoint(l_all),
    'base_ground_orthogonal_gap_lower': endpoint(global_gap, lower=True),
    'target_ground_orthogonal_gap_lower': endpoint(target_margin, lower=True),
    'positive_scalar_transport_check': bool(target_margin > 0),
    'same_unit_ground_and_operator_family_required': True,
    'cofinal_positivity': 'Unverified', 'RH_and_full_Robin': 'Unresolved',
    'Lean_certification': False,
}
if args.high_gap_supplier:
    result['high_gap_supplier'] = args.high_gap_supplier
    result['base_high_gap_lower'] = endpoint(delta, lower=True)
args.output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
