#!/usr/bin/env python3
"""Exact arithmetic for actual-law sparse extensions of certified heads.

Python 3.10+ standard library. --inherited is the Chapter 23 JSON certificate.
This checks new numerical inequalities, not the probability transport proof.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import prod
from pathlib import Path
import json
import sys

if not __debug__:
    raise RuntimeError('Run without -O; assertions are certificate checks')
if sys.version_info < (3, 10):
    raise SystemExit('Python 3.10 or newer is required')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--inherited', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
raw = args.inherited.read_bytes()
inherited = json.loads(raw)
assert inherited['kernel_rows'] == 160
assert len(inherited['rows']) == 160

def residuals(b, t):
    n = len(b)
    top = (1 << n)-1
    bs = [F(0)] + [prod(b[i] for i in range(n) if s >> i & 1)
                    for s in range(1, top+1)]
    v = [F(0)] + [(t + int(s.bit_count() > 1))*bs[s]
                   for s in range(1, top+1)]
    z = [F(1)]*(top+1)
    for a in range(1, top+1):
        low = a & -a
        z[a] = z[a ^ low] - sum(v[s]*z[a ^ s]
                                for s in range(1, top+1)
                                if s & a == s and s & low)
    # Distinct implementation: literal independent support sets.
    direct = [F(0)]*(top+1)
    for size in range(n+1):
        for family in combinations(range(1, top+1), size):
            used = 0
            for s in family:
                if used & s:
                    break
                used |= s
            else:
                term = (-1)**size * prod(v[s] for s in family)
                for a in range(top+1):
                    if used & a == used:
                        direct[a] += term
    assert direct == z and min(z) > 0
    return z[top], sum(bs[s]*z[top ^ s] for s in range(1, top+1))

def aggregate(R, t, delta):
    norm = 1-(t+1)*(1+R)*delta
    assert norm > 0
    return (R+(1+R)*delta)/norm

rstar = F(65157018363904, 65378462038225)
epsilon = 1-rstar
endpoint_gaps = [10**7*epsilon*x-(1+x)*(1+8*x)
                 for x in (F(3,8192), F(2200))]
assert min(endpoint_gaps) > 0
kernel_rows = []
for row in inherited['rows']:
    t, C = row['cutoff'], F(row['charge'])
    R = F(row['L'])/F(row['Z'])
    X = 2*3**t*C
    assert 1 <= t <= 7 and F(3,8192) <= X < 2200
    assert R/X <= rstar
    K = aggregate(R, t, F(1,10**7))/(2*3**t)
    assert K < C
    kernel_rows.append({'proxy_tuple': row['proxy_tuple'], 'cutoff': t,
                        'charge': str(C), 'extended_K3': str(K),
                        'margin': str(C-K)})

kr_rows = []
for row, orientation in zip(inherited['coupled_KR_inputs'],
                            inherited['exceptional_non3_orientations']):
    assert row['children'] == orientation['children']
    b = tuple(map(F, row['caps']))
    Z, L = residuals(b, 0)
    assert L == F(row['L0'])
    M, gap, delta = F(row['target_fee']), F(row['minimum_fee_gap']), F(1,400)
    margin = gap-(Z+L)*delta*(M+F(1,2))
    assert margin > 0
    Z1, L1 = residuals(b, 1)
    K3 = L1/(6*Z1)
    assert K3 == F(orientation['K3_t1']) and K3 < F(3,5)
    pmin = orientation['min_non3_parent']
    normalized = aggregate(L1/Z1, 1, delta)/(2*pmin)
    assert normalized < F(orientation['charge'])
    kr_rows.append({'head': row['children'], 'Delta': str(delta),
                    'Z0': str(Z), 'L0': str(L),
                    'remaining_KR_gap': str(margin),
                    'min_non3_parent': pmin,
                    'normalized_non3_bound': str(normalized)})

# Fixed rational input from the separately verified literal-5/15
# dense-core theorem; the conditional premise is not proved by this script.
core_K = F(328823862662848,743415381507325)
core_fee = F(371,768)
core_extended = aggregate(6*core_K, 1, F(1,128))/6
assert core_extended < core_fee
bcore = tuple(map(F, ('640/1917','128/639','128/1151','128/1407','128/1919')))
Zcore, Lcore = residuals(bcore, 1)
Rcore = Lcore/Zcore
assert Rcore < 7
core_non3 = aggregate(Rcore, 1, F(1,128))/(2*19)
assert core_non3 < core_fee

out = {'scope': 'Exact continuation inequalities; actual-law transport and '
                'recursive closure require the accompanying ordinary proof.',
       'inherited_sha256': sha256(raw).hexdigest(),
       'uniform_kernel_Delta': '1/10000000',
       'uniform_kernel_sigma': '1/10000001',
       'rstar': str(rstar), 'quadratic_endpoint_gaps': list(map(str, endpoint_gaps)),
       'kernel_rows_checked': len(kernel_rows), 'kernel_rows': kernel_rows,
       'KR_sigma': '1/401', 'KR_rows': kr_rows,
       'conditional_dense_core_sigma': '1/129',
       'conditional_dense_core_K3': str(core_extended),
       'conditional_dense_core_margin': str(core_fee-core_extended),
       'baseline_dense_core_R1': str(Rcore),
       'baseline_dense_core_non3_normalized_bound': str(core_non3),
       'baseline_dense_core_non3_margin': str(core_fee-core_non3)}
args.output.write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k != 'kernel_rows'}, indent=2))
