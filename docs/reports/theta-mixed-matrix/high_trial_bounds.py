"""Directed weighted derivative bounds on fixed whole-line high trials."""
import ast
import hashlib
import json
import math
import sys
from pathlib import Path

import flint
from flint import arb, ctx, fmpq

ctx.prec = 128
canonical = Path(__file__).resolve().parent
inputs = {}


def read_data(name):
    data = (canonical / name).read_bytes()
    inputs[name] = hashlib.sha256(data).hexdigest()
    return json.loads(data)


forward = read_data('forward-action-result.json')
trial = read_data('common-trials.json')
if (forward['bandwidth_N'] != 64 or forward['retained_gamma_terms'] != 1024
        or forward['retained_prime_cutoff'] != 64):
    raise RuntimeError('Action supplier parameter mismatch')
source = canonical / 'derivative_bandwidth.py'
source_bytes = source.read_bytes()
inputs[source.name] = hashlib.sha256(source_bytes).hexdigest()
tree = ast.parse(source_bytes)
prefix = []
for node in tree.body:
    if isinstance(node, ast.Assign) and any(
            isinstance(t, ast.Name) and t.id == 'bounds' for t in node.targets):
        break
    prefix.append(node)
else:
    raise RuntimeError('Original derivative coefficient boundary not found')
env = {'__file__': str(source)}
exec(compile(ast.Module(body=prefix, type_ignores=[]), str(source), 'exec'), env)
K = env['K'][:3]


def from_endpoint(item):
    man, exponent = item['dyadic']
    return arb(int(man)) * arb(2)**int(exponent)


def dyadic_frobenius(key, rows, columns):
    matrix = trial[key]
    if len(matrix) != rows or any(len(row) != columns for row in matrix):
        raise RuntimeError('Trial coefficient shape mismatch')
    integers = [[int(x) for x in row] for row in matrix]
    squared_sum = sum(x*x for row in integers for x in row)
    return arb(squared_sum).sqrt() * arb(2)**trial['coefficient_exponent']


FB = dyadic_frobenius('trial_coefficients_B', 95, 4)
FA = dyadic_frobenius('correction_map_A', 4, 95)
S = [from_endpoint(x) for x in forward['s_derivative_sup_upper']]
N, b, c = arb(64), arb(fmpq(3, 8)), arb(fmpq(3, 8))
A = [sum((math.comb(r,j)*S[j]*N**(r-j) for j in range(r+1)), arb(0))
     for r in range(3)]
D = [sum((math.comb(r,j)*S[j]*A[r-j] for j in range(r+1)), arb(0))
     for r in range(3)]
M = sum((arb(4)/arb(fmpq(4*k+1, 1)) for k in range(1024)), arb(0))
prime_terms = []
W = arb(0)
for p in range(2, 65):
    if any(p % d == 0 for d in range(2, math.isqrt(p)+1)):
        continue
    n = p
    while n <= 64:
        prime_terms.append(n)
        W += arb(p).log()/arb(n).sqrt()
        n *= p
V = [arb(1)]
for r in (1, 2):
    V.append(2*(arb.pi()/(2*b))**arb(fmpq(1, 4))
             *sum((math.comb(r,j)*arb(2)**(j-r)*K[j]
                   for j in range(r+1)), arb(0)))
Rj = [(M+8+2*W)*D[r]+c*V[r] for r in range(3)]
UZ = FB*(S[2]*Rj[0]+2*S[1]*Rj[1]+S[0]*Rj[2])
Ug = S[2]+2*S[1]*V[1]+S[0]*V[2]
weighted = (Ug*Ug+UZ*UZ).sqrt()
family_norm = (1+(FB*Rj[0])**2).sqrt()
prime_error = from_endpoint(forward['full_two_direction_prime_action_error_upper'])
prime_family_error = prime_error*family_norm
target = arb(fmpq(1, 1000))
terms = 1024
while True:
    last = arb(fmpq(4*terms-3, 2))
    gamma_error = S[0]*weighted/(2*last*last)
    total = gamma_error+prime_family_error
    if total < target:
        break
    terms *= 2
    if terms > 2**30:
        raise RuntimeError('Declared sufficient Gamma search range exhausted')


def endpoint(value):
    if not value.is_finite():
        raise RuntimeError('Nonfinite high-trial coefficient')
    upper = value.upper()
    return {'display': str(upper), 'dyadic': [str(v) for v in upper.man_exp()]}


result = {
    'scope': 'Paper-model derivative and action-tail supplier on fixed high trials; '
             'retained actions, Gram, residual matrix and sign remain unverified; no Lean or RH certificate',
    'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__,
                'precision_bits': ctx.prec},
    'input_sha256': inputs,
    'bandwidth_N': 64, 'trial_gamma_terms': 1024, 'trial_prime_cutoff': 64,
    'retained_prime_powers': sorted(prime_terms),
    'original_derivative_grid_rerun': False,
    'trial_B_frobenius_upper': endpoint(FB), 'map_A_frobenius_upper': endpoint(FA),
    'K_envelope_upper': [endpoint(x) for x in K],
    'finite_multiplier_sup_upper': endpoint(M),
    'retained_prime_weight_sum_upper': endpoint(W),
    'v0_derivative_norm_upper': [endpoint(x) for x in V],
    'retained_forward_derivative_norm_upper': [endpoint(x) for x in Rj],
    'weighted_second_Z_upper': endpoint(UZ),
    'weighted_second_ground_upper': endpoint(Ug),
    'weighted_second_common_family_upper': endpoint(weighted),
    'common_family_norm_upper': endpoint(family_norm),
    'sufficient_action_gamma_terms': terms,
    'action_target': '1/1000', 'gamma_action_error_upper': endpoint(gamma_error),
    'prime_action_error_upper': endpoint(prime_family_error),
    'full_common_family_action_error_upper': endpoint(total),
    'retained_actions_evaluated': False,
}
Path(__file__).with_name('high-trial-bounds-result.json').write_text(
    json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
