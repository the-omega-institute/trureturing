"""Ground normalization and action-tail transport using saved theta data."""
import ast
import hashlib
import json
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


derivative = read_data('derivative-bandwidth-result.json')
forward = read_data('forward-action-result.json')
high = read_data('high-trial-bounds-result.json')
if (forward['bandwidth_N'] != 64 or high['bandwidth_N'] != 64
        or high['sufficient_action_gamma_terms'] != 262144):
    raise RuntimeError('Action supplier parameter mismatch')
for name, expected in high['input_sha256'].items():
    if hashlib.sha256((canonical/name).read_bytes()).hexdigest() != expected:
        raise RuntimeError('High-trial input hash mismatch: '+name)
for name, expected in forward['input_data_sha256'].items():
    if hashlib.sha256((canonical/name).read_bytes()).hexdigest() != expected:
        raise RuntimeError('Low-band input hash mismatch: '+name)
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
    raise RuntimeError('Original coefficient boundary missing')
env = {'__file__': str(source)}
exec(compile(ast.Module(body=prefix, type_ignores=[]), str(source), 'exec'), env)
K = env['K']


def value(item):
    man, exponent = item['dyadic']
    return arb(int(man))*arb(2)**int(exponent)


a = [value(x).sqrt() for x in derivative['derivative_norm_squared_upper']]
b, N, R = arb(fmpq(3, 8)), arb(64), arb(3)
uR = (2*R).exp()
tau = (uR**arb(fmpq(-1, 2))*(-2*b*uR).exp()/(2*b)).sqrt()
ch, sh = (R/2).cosh(), (R/2).sinh()
interior = [2*ch*a[1]+sh*a[0], 2*ch*a[2]+2*sh*a[1]+ch*a[0]/2]
exterior = [2*(K[1]+K[0]/2)*tau, 2*(K[2]+K[1]+K[0]/4)*tau]
V = [(i*i+o*o).sqrt() for i, o in zip(interior, exterior)]
eta = V[1]/N**2
if not eta < 1:
    raise RuntimeError('Ground projection lower bound unavailable')
kappa = (1-eta*eta).sqrt()
normalization = 1/(1-eta*eta)
lift_norm = eta/kappa
residual_error = (value(forward['full_forward_action_error_upper'])
                  +value(high['map_A_frobenius_upper'])
                   *value(high['full_common_family_action_error_upper']))
if not residual_error < arb(fmpq(662, 10**6)):
    raise RuntimeError('Declared residual action-tail target not obtained')


def endpoint(x, lower=False):
    if not x.is_finite():
        raise RuntimeError('Nonfinite coefficient enclosure')
    bound = x.lower() if lower else x.upper()
    return {'display': str(bound), 'dyadic': [str(v) for v in bound.man_exp()]}


result = {
    'scope': 'Paper-model ground normalization and residual action-tail '
             'difference on the exact ground complement; no residual norm, '
             'retained Gram, matrix sign, Lean or RH certificate',
    'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__,
                'precision_bits': ctx.prec},
    'input_sha256': inputs, 'bandwidth_N': 64, 'physical_split_R': 3,
    'original_derivative_grid_rerun': False,
    'v0_derivative_norm_upper': [endpoint(x) for x in V],
    'Qv0_norm_upper': endpoint(eta), 'Pv0_norm_lower': endpoint(kappa, lower=True),
    'ground_inverse_squared_normalization_upper': endpoint(normalization),
    'ground_lift_operator_norm_upper': endpoint(lift_norm),
    'low_action_gamma_terms': 1024, 'high_action_gamma_terms': 262144,
    'residual_action_tail_difference_upper': endpoint(residual_error),
    'retained_actions_evaluated': False,
}
Path(__file__).with_name('ground-residual-result.json').write_text(
    json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
