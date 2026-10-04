"""Full-Gamma periodization coefficients on the same high family.

No sample, action, Gram or sign is supplied. The associated application
is a paper-model application, with actual action samples still separate.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

from flint import arb, ctx, fmpq

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--precision', type=int, default=192)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
if args.precision < 128:
    parser.error('Use at least128 bits for the directed coefficients')
ctx.prec = args.precision
canonical = Path(__file__).resolve().parent
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
        raise RuntimeError('Nonfinite full-Gamma coefficient')
    x = x.upper()
    return {'display': str(x), 'dyadic': [str(v) for v in x.man_exp()]}


strip = load('strip-root-bounds-result.json')
high = load('high-trial-bounds-result.json')
if inputs['high-trial-bounds-result.json'] != strip['input_sha256']['high-trial-bounds-result.json']:
    raise RuntimeError('Supplier mismatch')
U = exact(strip['common_high_line_L2_operator_upper'])
B, A0 = exact(strip['s_line_L2_upper']), exact(strip['s_real_sup_upper'])
K = [exact(x) for x in high['K_envelope_upper']]
delta, h, b = arb(fmpq(1, 8)), arb(fmpq(1, 256)), arb(fmpq(3, 8))
R, X = arb(128), arb(4)
L = [U*(arb(2*math.factorial(2*r))/(arb.pi()*(2*delta)**(2*r+1))).sqrt() for r in range(3)]
F0 = K[0]*L[0]*(-b).exp()
F2 = (K[2]*L[0]+2*K[1]*L[1]+K[0]*L[2])*(-b).exp()
W1 = F0/b
Cm = 18*arb(fmpq(1, 2)).exp()*F2+(4*arb(fmpq(-1, 2)).exp()*F0+W1)/(1-arb(-2).exp())
wrap = Cm*2*(-(R-X)/2).exp()/(1-(-R/2).exp())
nu, step = arb.pi()/h, 2*arb.pi()/R
if not nu >= 1/(2*delta) or not 1/(4*b) < 1:
    raise RuntimeError('Geometric decay condition failed')
G = 4+(1+4*nu**2).log()/2
fold = 4*B*U/R*G*(-delta*nu).exp()/(1-(-delta*step/2).exp())
UX = (2*X).exp()
tail = K[0]*L[0]*(-b*UX).exp()/(b*UX)
delete = G*tail/h
result = {
    'scope': 'Paper-model full-Gamma periodization and folded-mode coefficients on the same five-generator family; no samples/action/Gram/sign',
    'input_sha256': inputs, 'precision_bits': ctx.prec,
    'period_R': 128, 'sample_spacing_h': '1/256', 'input_and_output_core_X': 4,
    'real_u_derivative_sup_upper': [upper(x) for x in L],
    'weighted_f_sup_upper': upper(F0), 'weighted_f_second_sup_upper': upper(F2),
    'weighted_f_L1_upper': upper(W1), 'weighted_full_gamma_pointwise_coefficient_upper': upper(Cm),
    'full_gamma_core_periodization_error_upper': upper(wrap),
    'full_gamma_folded_mode_error_upper': upper(fold),
    'full_gamma_omitted_periodized_sample_error_upper': upper(delete),
    'outer_s_full_gamma_local_error_upper': upper(A0*(wrap+fold+delete)),
    'full_multiplier_boundedness_assumed': False,
    'trial_Z_finite_J_definition_changed': False, 'numerical_samples_evaluated': False,
    'Lean_certification': False,
}
output = args.output or canonical/'full-gamma-periodic-result.json'
output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
