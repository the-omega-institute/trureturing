"""Directed off-lattice Z and retained-prime full-action coefficient inputs.

Paper-model supplier premises are reused; actions and common Grams are separate.
"""
import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx, fmpq

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--precision', type=int, default=192)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
if args.precision < 128:
    parser.error('Use at least128 bits for directed action coefficients')
ctx.prec = args.precision
canonical = Path(__file__).resolve().parent
inputs = {}


def load(name):
    data = (canonical/name).read_bytes()
    inputs[name] = hashlib.sha256(data).hexdigest()
    return json.loads(data)


def exact(item):
    m, e = item['dyadic']
    return arb(int(m))*arb(2)**int(e)


def upper(x):
    if not x.is_finite():
        raise RuntimeError('Nonfinite action interface coefficient')
    x = x.upper()
    return {'display': str(x), 'dyadic': [str(v) for v in x.man_exp()]}


def envelopes(d):
    if not isinstance(d, fmpq) or not 0 <= d <= fmpq(7, 48):
        raise RuntimeError('Wide envelope outside the established strip')
    d = arb(d)
    a = arb.pi()*(2*d).cos()
    C = 2*arb.pi()*arb(fmpq(7, 6))/(d/2).cos()
    if not a > 2:
        raise RuntimeError('Wide envelope monotonicity missing')
    A = (C*(2*arb.pi()+3)*(-a).exp()).sqrt()
    B = (C*(-a).exp()*(2*arb.pi()*(1/a+1/a**2)+3/a)).sqrt()
    V = (4*arb.pi()*arb(fmpq(7, 6))*(-a).exp()
         *(2*arb.pi()*(1/a+2/a**2+2/a**3)+3*(1/a+1/a**2))).sqrt()
    return A, B, V


strip = load('strip-root-bounds-result.json')
high = load('high-trial-bounds-result.json')
projection = load('continuous-projection-result.json')
gram = load('local-z-gram-result.json')
gamma = load('full-gamma-periodic-result.json')
forward = load('forward-action-result.json')
for supplier in (projection, gamma):
    for key, value in supplier['input_sha256'].items():
        if key in inputs and inputs[key] != value:
            raise RuntimeError('Source hash mismatch')
delta, h, c = arb(fmpq(1, 8)), arb(fmpq(1, 256)), arb(fmpq(3, 8))
nu, F = arb.pi()/h, 2*arb.pi()/h
ratio = (-delta*F).exp()
FB = exact(high['trial_B_frobenius_upper'])
UH = exact(strip['retained_forward_line_L2_operator_upper'])*FB
Knu = ((2*nu*delta).sinh()/(2*arb.pi()*delta)).sqrt()
tail_nu = UH*(-delta*nu).exp()/(arb.pi()*delta).sqrt()
quad_nu = 2*UH*Knu*ratio/(1-ratio)
JX = exact(projection['forward_physical_and_discrete_L1_tail_upper'])
offgrid = tail_nu+quad_nu+nu/arb.pi()*JX+exact(projection['combined_sinc_quadrature_and_physical_tail_pointwise_error_upper'])
A, V = exact(strip['s_strip_sup_upper']), exact(strip['v0_line_L2_upper'])
A0, U = exact(strip['s_real_sup_upper']), exact(strip['common_high_line_L2_operator_upper'])
L0 = exact(gamma['real_u_derivative_sup_upper'][0])
Cm = exact(gamma['weighted_full_gamma_pointwise_coefficient_upper'])
Rreal = exact(gram['same_five_generator_real_norm_upper'])
M, W = exact(high['finite_multiplier_sup_upper']), exact(high['retained_prime_weight_sum_upper'])
wide_exact = fmpq(7, 48)
wide = arb(wide_exact)
Ap, Bp, Vp = envelopes(wide_exact)
Dp = Ap**2*(M+8+2*W)*(64*wide).exp()+c*Vp
Up = (Vp**2+(Dp*FB)**2).sqrt()
epsilon = wide-delta
cutoff = 1/(4*epsilon)
Gcut = 4+(1+4*cutoff**2).log()/2
DHZ = A*arb(2).sqrt()*Gcut*Ap*Up+A**2*(8+2*W)*U+c*Rreal*V
b, UX = arb.pi()/2, arb(8).exp()
Cs = (2*arb.pi()*arb(fmpq(7, 6))*(2*arb.pi()+3)).sqrt()
CHZ = Cs*(Cm+(8+2*W)*A0*L0+2*c*Rreal)
physical = (-b*UX).exp()*(UX/b+1/b**2)
JHZ = CHZ*physical
K64 = exact(projection['sinc_line_L2_upper'])
HZprojection = 2*DHZ*K64*ratio/(1-ratio)+64/arb.pi()*JHZ
mean_error = 2*V*U*ratio/(1-ratio)+2*Cs*L0*physical
v0sup = 2*Cs*(2/b)**2*arb(-2).exp()
core_error = exact(gamma['outer_s_full_gamma_local_error_upper'])+c*v0sup*mean_error
prime_offgrid_error = 2*W*A0**2*offgrid
prime_omission = exact(forward['full_two_direction_prime_action_error_upper'])*Rreal
result = {
    'scope': 'Paper-model same-family off-grid and full-Gamma retained-prime action inputs; no numerical action/Gram/sign',
    'input_sha256': inputs, 'precision_bits': ctx.prec,
    'H_cardinal_Fourier_tail_pointwise_upper': upper(tail_nu),
    'H_cardinal_lattice_quadrature_pointwise_upper': upper(quad_nu),
    'off_lattice_Z_analytic_pointwise_error_upper': upper(offgrid),
    'wide_strip_same_high_line_L2_upper': upper(Up),
    'retained_prime_full_HZ_line_L2_upper': upper(DHZ),
    'retained_prime_full_HZ_pointwise_envelope_coefficient_upper': upper(CHZ),
    'retained_prime_full_HZ_physical_and_lattice_L1_tail_upper': upper(JHZ),
    'retained_prime_full_HZ_sinc_projection_pointwise_error_upper': upper(HZprojection),
    'same_high_real_mean_quadrature_and_tail_upper': upper(mean_error),
    'same_high_core_gamma_and_mean_analytic_error_upper': upper(core_error),
    'same_high_prime_off_grid_input_error_upper': upper(prime_offgrid_error),
    'complete_omitted_prime_L2_action_error_same_family_upper': upper(prime_omission),
    'full_Gamma_evaluated': False, 'common_residual_Gram_evaluated': False,
    'Lean_certification': False,
}
(args.output or canonical/'off-grid-action-result.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
