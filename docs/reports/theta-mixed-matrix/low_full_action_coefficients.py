"""Candidate transport of accepted action allowances to the95 low inputs.

This evaluates new scalar interfaces only, not low actions or a Schur sign.
"""
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, ctx, fmpq

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--canonical', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--output', type=Path, default=Path(__file__).resolve().with_name('low-full-action-coefficients.json'))
args = parser.parse_args()
ctx.prec = 192
sources = {}


def load(name):
    data = (args.canonical/name).read_bytes()
    sources[name] = hashlib.sha256(data).hexdigest()
    return json.loads(data)


def exact(item):
    m, e = item['dyadic']
    return arb(int(m))*arb(2)**int(e)


def upper(value):
    if not value.is_finite():
        raise RuntimeError('Nonfinite low-action allowance')
    value = value.upper()
    return {'display': str(value), 'dyadic': [str(v) for v in value.man_exp()]}


strip = load('strip-root-bounds-result.json')
gamma = load('full-gamma-periodic-result.json')
projection = load('continuous-projection-result.json')
forward = load('forward-action-result.json')
high = load('high-trial-bounds-result.json')
for supplier in (strip, gamma, projection):
    for name, sha in supplier['input_sha256'].items():
        if name in sources and sources[name] != sha:
            raise ValueError('Low interface supplier hash mismatch')
delta, wide = arb(fmpq(1, 8)), arb(fmpq(7, 48))
h, c = arb(fmpq(1, 256)), arb(fmpq(3, 8))
Ul = (64*delta).exp().upper()
Uw = (64*wide).exp().upper()
Uh = exact(strip['common_high_line_L2_operator_upper'])
if not Uh > 0:
    raise ValueError('Positive original line allowance required')
scale = Ul/Uh
L0 = exact(gamma['real_u_derivative_sup_upper'][0])*scale
Cm = exact(gamma['weighted_full_gamma_pointwise_coefficient_upper'])*scale
gamma_local = exact(gamma['outer_s_full_gamma_local_error_upper'])*scale
# Wider contour values use the already accepted exact rational7/48.
aw = arb.pi()*(2*wide).cos()
Cw = 2*arb.pi()*arb(fmpq(7, 6))/(wide/2).cos()
if not aw > 2:
    raise ValueError('Wider envelope monotonicity missing')
Aw = (Cw*(2*arb.pi()+3)*(-aw).exp()).sqrt()
cutoff = 1/(4*(wide-delta))
Gcut = 4+(1+4*cutoff**2).log()/2
A = exact(strip['s_strip_sup_upper'])
A0 = exact(strip['s_real_sup_upper'])
V = exact(strip['v0_line_L2_upper'])
W = exact(high['retained_prime_weight_sum_upper'])
D = A*arb(2).sqrt()*Gcut*Aw*Uw+A**2*(8+2*W)*Ul+c*V
Cs = (2*arb.pi()*arb(fmpq(7, 6))*(2*arb.pi()+3)).sqrt()
b, UX = arb.pi()/2, arb(8).exp()
physical = (-b*UX).exp()*(UX/b+1/b**2)
CH = Cs*(Cm+(8+2*W)*A0*L0+2*c)
JH = CH*physical
ratio = (-2*arb.pi()*delta/h).exp()
K64 = exact(projection['sinc_line_L2_upper'])
PHerror = 2*D*K64*ratio/(1-ratio)+64/arb.pi()*JH
mean_error = 2*V*Ul*ratio/(1-ratio)+2*Cs*L0*physical
v0sup = 2*Cs*(2/b)**2*arb(-2).exp()
result = {
    'scope': 'Candidate low-unit-ball action and ground-moment allowances; no95 low actions, common matrices or sign evaluated',
    'input_sha256': sources, 'precision_bits': ctx.prec,
    'bandwidth_N': 64, 'low_orthonormal_columns': 95,
    'sample_spacing_h': '1/256', 'physical_period': 128,
    'low_strip_unit_ball_upper': upper(Ul),
    'low_wide_strip_unit_ball_upper': upper(Uw),
    'low_full_Gamma_core_analytic_error_upper': upper(gamma_local),
    'low_full_H_line_L2_upper': upper(D),
    'low_full_H_pointwise_envelope_coefficient_upper': upper(CH),
    'low_full_H_physical_and_lattice_tail_upper': upper(JH),
    'low_continuous_PH_analytic_error_upper': upper(PHerror),
    'low_exact_ground_moment_quadrature_and_tail_upper': upper(mean_error),
    'low_H_core_Gamma_and_mean_analytic_error_upper': upper(gamma_local+c*v0sup*mean_error),
    'low_complete_omitted_prime_L2_action_upper': forward['full_two_direction_prime_action_error_upper'],
    'low_actions_evaluated': False, 'Schur_sign_certified': False,
    'Lean_certification': False,
}
args.output.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
