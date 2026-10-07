"""Sharpen the exterior row envelope without evaluating theta or an old grid.

Consumes the saved interior floor and leakage for the same paper operator.
The resulting high-gap supplier can be used by threshold_transport.py.
"""
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, ctx, fmpq


def exact(item):
    m, e = item['dyadic']
    value = arb(int(m))*arb(2)**int(e)
    if not value.is_finite():
        raise ValueError('Finite exterior supplier endpoint required')
    return value


def endpoint(value, lower=False):
    if not value.is_finite():
        raise ValueError('Finite exterior endpoint required')
    value = value.lower() if lower else value.upper()
    return {'display': str(value), 'dyadic': [str(v) for v in value.man_exp()]}


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--canonical', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name('sharper-exterior-result.json'))
parser.add_argument('--precision', type=int, default=192)
args = parser.parse_args()
if args.precision < 192:
    parser.error('At least 192 bits required')
ctx.prec = args.precision
canonical = args.canonical.resolve()
sources = {}


def read(name):
    raw = (canonical/name).read_bytes()
    sources[name] = hashlib.sha256(raw).hexdigest()
    return raw


joint = json.loads(read('joint-high-floor-result.json'))
read('strip-root.md')
read('derivative-bandwidth-result.json')
if (joint['bandwidth_N'], joint['matrix_c'], fmpq(joint['radius'])) != (64, '3/8', fmpq(3, 2)):
    raise ValueError('The saved bandwidth 64, c=3/8, radius 3/2 model is required')
if joint['derivative_source'] != 'derivative-bandwidth-result.json':
    raise ValueError('Canonical derivative supplier required')
if joint['derivative_source_sha256'] != sources[joint['derivative_source']]:
    raise ValueError('Saved leakage supplier hash mismatch')
if not joint['passed_joint_2_over_5'] or not joint['passed_high_above_3_over_8']:
    raise ValueError('Accepted joint high-floor supplier required')
interior = exact(joint['interior_joint_floor_lower'])
leakage = exact(joint['leakage_product_upper'])
if not interior > 0 or not leakage >= 0:
    raise ValueError('Positive interior and nonnegative leakage bounds required')

pi = arb.pi()
b = pi/2
cs2 = 2*pi*arb(fmpq(7, 6))*(2*pi+3)
u = arb(3).exp()
if not b*u/2 > 1 or not b*u > 1:
    raise ValueError('Exterior envelope monotonicity must be certified')
r = (-b).exp()
if not 0 < r < 1:
    raise ValueError('Geometric row summation requires 0<r<1')
weight_sum = r/((1-r)*(1-r))-r
row = (2*cs2*(2/(b*arb(1).exp()))*weight_sum*u*(-b*u/2).exp()).upper()
gamma_loss = (8*cs2*u*u*(-2*b*u).exp()).upper()
exterior = (arb(fmpq(1, 2))-row-gamma_loss).lower()
if not exterior > interior:
    raise ValueError('The sharper exterior must leave the saved interior as the bottleneck')
global_floor = exterior.min(interior).lower()
high_floor = (global_floor-leakage).lower()
delta = (high_floor-arb(fmpq(3, 8))).lower()
if not delta > 0:
    raise ValueError('A strictly positive base high gap is required')
result = {
    'scope': 'Real exterior row envelope and stronger coercivity for the unchanged paper operator; saved interior/leakage reused; no action or grid evaluation, Lean, cofinal, RH or Robin certificate',
    'input_sha256': sources, 'precision_bits': ctx.prec,
    'bandwidth_N': 64, 'base_c': '3/8', 'exterior_radius': '3/2',
    'full_two_direction_row_tail_upper': endpoint(row),
    'exterior_Gamma_loss_upper': endpoint(gamma_loss),
    'exterior_W_floor_lower': endpoint(exterior, lower=True),
    'reused_interior_joint_floor_lower': endpoint(interior, lower=True),
    'global_joint_floor_lower': endpoint(global_floor, lower=True),
    'reused_leakage_product_upper': endpoint(leakage),
    'complete_high_form_floor_lower': endpoint(high_floor, lower=True),
    'base_high_gap_lower': endpoint(delta, lower=True),
    'exterior_above_saved_interior_checked': bool(exterior > interior),
    'positive_high_gap_checked': bool(delta > 0),
    'same_operator_and_supplier_premises_required': True,
    'Lean_certification': False, 'cofinal_RH_and_full_Robin': 'Unresolved',
}
args.output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
