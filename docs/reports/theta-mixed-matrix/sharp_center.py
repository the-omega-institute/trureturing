"""Actual sharp-center column majorants; no original derivative grid rerun."""
import ast
import hashlib
import json
import sys
from pathlib import Path
import flint
from flint import arb, fmpq, ctx

ctx.prec = 128
canonical = Path(__file__).resolve().parent
source = canonical / 'derivative_bandwidth.py'
tree = ast.parse(source.read_text())
prefix = []
found_grid = False
for node in tree.body:
    if isinstance(node, ast.Assign) and any(
            isinstance(t, ast.Name) and t.id == 'bounds' for t in node.targets):
        found_grid = True
        break
    prefix.append(node)
if not found_grid:
    raise RuntimeError('Canonical coefficient setup boundary not found')
env = {'__file__': str(source)}
exec(compile(ast.Module(body=prefix, type_ignores=[]), str(source), 'exec'), env)
K0, K1 = env['K'][:2]
supplier_bytes = (canonical / 'derivative-bandwidth-result.json').read_bytes()
supplier = json.loads(supplier_bytes)


def from_endpoint(item):
    man, exponent = item['dyadic']
    return arb(int(man)) * arb(2)**int(exponent)


norm2 = [from_endpoint(v) for v in supplier['derivative_norm_squared_upper']]
R = arb(3)
b = arb(fmpq(3, 8))
N = arb(64)
c = arb(fmpq(3, 8))
alpha = arb(fmpq(1, 8))
delta = arb(fmpq(383682545007734, 10**16))
pi = arb.pi()
uR = (2*R).exp()
a0, a1 = [v.sqrt() for v in norm2[:2]]
X0, X1 = [(R*R*v+k*k*(-2*b*uR).exp()/(8*b)).sqrt()
          for v, k in zip(norm2[:2], [K0, K1])]
# Standard one-dimensional H1 bound ||s||_infty^2 <= ||s||_2 ||s'||_2.
s_inf = (a0*a1).sqrt()
V0 = (2*R).sqrt()+2*K0*uR**arb(fmpq(-3, 4))*(-b*uR).exp()/b
V1 = (2*R**3/3).sqrt()+K0*uR**arb(fmpq(-1, 4))*(-b*uR).exp()/b
r = (-b).exp()
J = 2*K0*K0*((-b).exp()/b).sqrt()*(r/(1-r)**2-r)
terms = 1024
mN = arb(0)
for k in range(terms):
    ak = arb(fmpq(4*k+1, 2))
    mN += 2*N*N/(ak*(ak*ak+N*N))
last = arb(fmpq(4*(terms-1)+1, 2))
mN = (mN+N*N/(2*last*last)).upper()
# Existing exact coefficient is digamma(1/4)-log pi; |cGamma|<8 suffices.
gamma_abs = arb(8)
M0 = (s_inf*((mN+gamma_abs)*a0+7*a1)+J+c*V0)/pi.sqrt()
M1 = (s_inf*((mN+gamma_abs)*X0+7*(a0+X1))+J+c*V1)/pi.sqrt()
H_norm = N.sqrt()*M0
epsilon_coefficient = N*N.sqrt()*M1/pi
e_coefficient = 2*(1+H_norm/delta)*epsilon_coefficient
# e_M < 1/16 is only a center-tail target, not a retained matrix sign.
rank_man, rank_exponent = map(int, (16*e_coefficient).upper().man_exp())
rank = ((rank_man << rank_exponent) if rank_exponent >= 0 else
        (rank_man+(1 << -rank_exponent)-1)//(1 << -rank_exponent))+1
if not e_coefficient/arb(rank) < alpha/2:
    raise RuntimeError('Declared center-tail margin not obtained')

# Full complex cosine columns on the [0,N] Bernstein ellipse of radius 3/2.
ellipse = arb(fmpq(3, 2))
imaginary_bound = N*(ellipse-1/ellipse)/4
eta_bound = N/2+N*(ellipse+1/ellipse)/4
weighted_factor = (imaginary_bound.gamma()/(2*b)**imaginary_bound).sqrt()
weighted_a0, weighted_a1 = K0*weighted_factor, K1*weighted_factor
power = imaginary_bound/2
prime_phase_factor = (imaginary_bound/b)**power*(-power).exp()
mean_power = (imaginary_bound+arb(fmpq(1, 2)))/2
weighted_V = 2*K0*mean_power.gamma()/b**mean_power
ellipse_column = (16*s_inf*((1+eta_bound)*weighted_a0+weighted_a1)
                  +gamma_abs*s_inf*weighted_a0+J*prime_phase_factor
                  +c*weighted_V)/pi.sqrt()
ellipse_tail_coefficient = (2*(1+H_norm/delta)*N.sqrt()
                            *2*ellipse_column/(ellipse-1))
degree = 0
while not ellipse_tail_coefficient*ellipse**(-degree) < alpha/2:
    degree += 1
    if degree > 256:
        raise RuntimeError('Declared polynomial search range exhausted')


def endpoint(v):
    bound = v.upper()
    return {'display': str(bound), 'dyadic': [str(t) for t in bound.man_exp()]}


result = {
    'scope': 'Complete sharp-center column upper majorants and a sufficient tail rank; no finite matrix sign, practicality, cofinal or RH certificate; no new Lean certification',
    'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__, 'precision_bits': ctx.prec},
    'supplier_data': 'derivative-bandwidth-result.json',
    'supplier_data_sha256': hashlib.sha256(supplier_bytes).hexdigest(),
    'bandwidth_N': 64, 'physical_radius_R': 3, 'symbol_terms': terms,
    'original_derivative_grid_rerun': False,
    'K0_upper': endpoint(K0), 'K1_upper': endpoint(K1),
    'a0_upper': endpoint(a0), 'a1_upper': endpoint(a1),
    'X0_upper': endpoint(X0), 'X1_upper': endpoint(X1),
    's_infinity_upper': endpoint(s_inf),
    'V0_upper': endpoint(V0), 'V1_upper': endpoint(V1),
    'prime_column_and_derivative_upper': endpoint(J),
    'm_N_upper': endpoint(mN), 'gamma_abs_upper_used': 8,
    'M0_upper': endpoint(M0), 'M1_upper': endpoint(M1),
    'H_center_input_norm_upper': endpoint(H_norm),
    'tail_e_coefficient_upper': endpoint(e_coefficient),
    'requested_center_tail_margin': '1/16',
    'sufficient_cell_rank': rank,
    'tail_e_at_rank_upper': endpoint(e_coefficient/arb(rank)),
    'ellipse_radius': '3/2',
    'ellipse_imaginary_eta_upper': endpoint(imaginary_bound),
    'ellipse_absolute_eta_upper': endpoint(eta_bound),
    'ellipse_column_norm_upper': endpoint(ellipse_column),
    'ellipse_tail_e_coefficient_upper': endpoint(ellipse_tail_coefficient),
    'sufficient_polynomial_degree': degree,
    'ground_augmented_rank_upper': degree+2,
    'ellipse_tail_e_at_degree_upper': endpoint(ellipse_tail_coefficient*ellipse**(-degree)),
    'retained_matrix_sign': 'not computed',
}
out = Path(__file__).with_name('sharp-center-result.json')
out.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2), flush=True)
