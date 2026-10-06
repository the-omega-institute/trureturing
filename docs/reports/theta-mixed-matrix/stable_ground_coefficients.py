"""Projected-ground coefficients from the canonical joint-kernel suppliers.

No old integration grid is repeated; no retained direction or sign is supplied.
"""
from pathlib import Path
from flint import arb, fmpq, ctx
import hashlib
import json
import argparse

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--precision', type=int, default=128)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
if args.precision < 64:
    parser.error('Precision must be at least 64 bits')
ctx.prec = args.precision
canonical = Path(__file__).resolve().parent
inputs = {}


def load(name):
    data = canonical.joinpath(name).read_bytes()
    inputs[name] = hashlib.sha256(data).hexdigest()
    return json.loads(data)


def exact(item):
    mantissa, exponent = item['dyadic']
    return arb(int(mantissa))*arb(2)**int(exponent)


def bound(x, side):
    if not x.is_finite():
        raise RuntimeError('Nonfinite stable-ground coefficient')
    y = x.lower() if side == 'lower' else x.upper()
    return {'display': str(y), 'dyadic': [str(t) for t in y.man_exp()]}


center = load('sharp-center-result.json')
ground = load('ground-residual-result.json')
if center['sufficient_polynomial_degree'] != 94 or center['bandwidth_N'] != 64 or ground['bandwidth_N'] != 64:
    raise RuntimeError('Center/ground source parameter mismatch')
alpha = arb(fmpq(1, 8))
d = exact(center['ellipse_tail_e_at_degree_upper'])/2
if not d < alpha:
    raise RuntimeError('Positive complementary center gap missing')
lower = exact(ground['Pv0_norm_lower'])*(1-(d/alpha)**2).sqrt()
if not lower > 0:
    raise RuntimeError('Nonzero polynomial-ground projection not certified')
result = {
    'scope': 'Paper-model coefficient application; exact ground direction, entries, restricted sign and RH remain unresolved',
    'precision_bits': ctx.prec,
    'input_sha256': inputs, 'alpha': '1/8', 'rank': 95,
    'L_one_sided_polynomial_tail_upper': bound(d, 'upper'),
    'projected_ground_norm_lower': bound(lower, 'lower'),
    'projected_ground_inverse_norm_upper': bound(1/lower, 'upper'),
    'complementary_center_gap_lower': bound(alpha-d, 'lower'),
    'second_schur_allowance_upper': bound(d*d/(alpha-d), 'upper'),
    'joint_premises': ['S=alpha I+L bounded self-adjoint', 'S p0=0 exactly',
                      'norm L(I-EE*) <= e94/2', 'canonical lower bound for norm p0'],
    'old_grids_rerun': False, 'retained_ground_direction_evaluated': False,
    'restricted_matrix_sign': 'Unverified', 'Lean_certification': False,
}
output = args.output or canonical/'stable-ground-result.json'
output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
