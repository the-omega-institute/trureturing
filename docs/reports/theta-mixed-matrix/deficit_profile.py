"""Directed enclosure of the actual mixed theta scalar deficit."""
import ast
import hashlib
import json
import math
import sys
from pathlib import Path

import flint
from flint import arb, acb, ctx, fmpq

ctx.prec = 128
run = Path(__file__).parent
source = run/'scalar_pilot.py'
source_bytes = source.read_bytes()
tree = ast.parse(source_bytes)
body = [node for node in tree.body if isinstance(node, ast.FunctionDef)
        and node.name in ('phi', 'realphi')]
if len(body) != 2:
    raise RuntimeError('Approved theta callback selection is incomplete')
scope = {'arb': arb, 'acb': acb, 'P': 6, 'counter': {'theta': 0}}
exec(compile(ast.Module(body=body, type_ignores=[]), str(source), 'exec'), scope)
phi = scope['realphi']
EPS = arb(fmpq(1, 4))
R = arb(fmpq(3, 2))
NP = 64
GRID = 1536
CG = arb.const_euler() + arb.pi()/2 + 3*arb(2).log() + arb.pi().log()


def upper_s(x):
    value = phi(x)
    if not value.is_finite() or not value.upper() > 0:
        raise RuntimeError('Nonfinite or nonpositive theta upper enclosure')
    d = 2*(x/2).cosh()
    if not d.lower() > 0:
        raise RuntimeError('Uncertified denominator')
    return (value.upper()/d.lower()).sqrt().upper()


def density_s2(x):
    value = phi(x)/(2*(x/2).cosh())
    if not value.is_finite() or not value.lower() > 0:
        raise RuntimeError('Uncertified principal coefficient lower bound')
    return value


def prime_base(n):
    for p in range(2, math.isqrt(n)+1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return p if m == 1 else None
    return n


terms = [(n, prime_base(n)) for n in range(2, NP+1)]
terms = [(n, p, arb(p).log()/arb(n).sqrt(), arb(n).log())
         for n, p in terms if p is not None]
alpha = arb(fmpq(3, 4))*(-2*R).exp()
if not arb(NP).log() > R or not 2*alpha*NP**2 > 1:
    raise RuntimeError('Uncertified shifted and decreasing prime-tail range')
tail = (arb(fmpq(72, 5)).sqrt()*arb(fmpq(9, 5)).sqrt()
        *(-alpha*NP**2).exp()/alpha).upper()
exterior = 160*(-arb(fmpq(3, 8))*(2*R).exp()).exp()
if not exterior.upper() < EPS/2:
    raise RuntimeError('Exterior deficit-zero claim is not certified')


def point_lower(x):
    s2 = density_s2(x)
    sm = s2.sqrt()
    row = arb(0)
    for n, p, w, t in terms:
        for y in (x+t, x-t):
            val = density_s2(y)
            row += w*sm*val.sqrt()
    value = (CG*s2+row-EPS/2)/s2
    return max(arb(0), value.lower())


best_hi = arb(0)
best_lo = arb(0)
best_cell = None
zero_boxes = 0
rows = []
for j in range(GRID):
    a = fmpq(3*j, 2*GRID)
    b = fmpq(3*(j+1), 2*GRID)
    x = arb((a+b)/2, arb((b-a)/2).upper())
    s2 = density_s2(x)
    sm_up = s2.sqrt().upper()
    row_up = arb(0)
    for n, p, w, t in terms:
        row_up += w.upper()*sm_up*(upper_s(x+t)+upper_s(x-t))
    deficit_up = (CG.upper()*s2.upper()+row_up+tail-EPS/2).upper()
    if deficit_up > 0:
        value_up = (deficit_up/s2.lower()).upper()
    elif deficit_up <= 0:
        value_up = arb(0)
        zero_boxes += 1
    else:
        raise RuntimeError('Ambiguous deficit sign')
    if value_up > best_hi:
        best_hi = value_up
        best_cell = [str(a), str(b)]
    best_lo = max(best_lo, point_lower(arb((a+b)/2)))
    if j % 256 == 0:
        print(json.dumps({'cell': j, 'mu_lower': str(best_lo),
                          'mu_upper': str(best_hi)}), flush=True)


def endpoint(x):
    return {'display': str(x), 'dyadic': [str(z) for z in x.man_exp()]}


result = {
    'scope': 'Directed scalar deficit enclosure; no matrix or RH certificate; no new Lean certification',
    'runtime': {
        'python': sys.version.split()[0],
        'python_flint': flint.__version__,
        'precision_bits': ctx.prec,
    },
    'epsilon': '1/4', 'radius': '3/2', 'prime_cutoff': NP,
    'prime_powers': [[n, p] for n, p, _, _ in terms],
    'grid_boxes': GRID, 'certified_nonpositive_boxes': zero_boxes,
    'theta_callback_sha256': hashlib.sha256(source_bytes).hexdigest(),
    'mu_lower': endpoint(best_lo), 'mu_upper': endpoint(best_hi),
    'largest_upper_cell': best_cell, 'omitted_full_row_upper': endpoint(tail),
    'exterior_d_upper': endpoint(exterior.upper()),
    'declared_width_below_0_1': bool(best_hi-best_lo < arb('0.1')),
    'theta_calls': scope['counter']['theta'],
}
(run/'deficit-result.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result), flush=True)
