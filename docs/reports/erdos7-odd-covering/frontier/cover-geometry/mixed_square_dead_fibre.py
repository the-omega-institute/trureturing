#!/usr/bin/env python3
"""Exact regression for the Report591 first-root boundary and mixed squares.

Ordinary finite arithmetic; not a covering, an all-law obstruction, or Lean.
Run with Python standard library, optionally --output result.json.
"""
from fractions import Fraction as F
from itertools import product, combinations
from math import prod
import argparse
import json

P = (3, 5, 7, 11, 13, 17, 19)
V = P[2:]
FORCED = (3, 5, 7, 11)
G = F(566, 49)
PURE = tuple((p, 1) for p in P)
STARS = ((15, 0),) + tuple((c*p, 0) for p in V for c in (3, 5))
SPREAD = ((45, 2), (63, 23), (99, 35))
ALIGNED = ((45, 2), (63, 2), (99, 2))
checks = []

def check(name, condition):
    if not condition:
        raise RuntimeError(name)
    checks.append(name)

def crt(vals):
    x, n = 0, 1
    for m, a in zip((9,) + P[1:], vals):
        x += n * ((a-x)*pow(n, -1, m) % m)
        n *= m
    return x

def private_witnesses(squares):
    family = PURE + STARS + squares
    check('distinct-odd-labels-'+str(squares[1][1]),
          len(family) == len({m for m, _ in family}) == 21 and
          all(m > 1 and m % 2 for m, _ in family))
    result = []
    aligned = squares == ALIGNED
    for m, a in family:
        v = {p: 2 for p in P}
        if m in P:
            v[3] = 1 if m == 3 else 0
            v[m] = 1
        elif m == 15:
            v[3] = v[5] = 0
        elif m in {3*q for q in V}:
            v[3] = v[m//3] = 0
        elif m in {5*q for q in V}:
            v[3] = 5 if aligned else 2
            v[5] = v[m//5] = 0
        else:
            if aligned:
                for q in (5, 7, 11):
                    v[q] = 3
            v[3] = 2 if aligned else {45: 2, 63: 5, 99: 8}[m]
            v[m//9] = 2
        x = crt(tuple(v[p] for p in P))
        check('private-'+str((m, a)),
              [(n,b) for n,b in family if x % n == b] == [(m,a)])
        result.append((m,a,x))
    return result

# Exact weighted compression of rho. At each nonternary coordinate,
# category 3 denotes all retained roots except 0 and 2. Its multiplicity
# is p-3; all original tests used here are constant on that category.
base_mass = F(0)
e_mass = F(0)
single = [[F(0)]*3 for _ in range(2)]
unions = [F(0), F(0)]
surv_e = [F(0), F(0)]
for t in (0, 2, 3, 5, 6, 8):
    for qs in product((0, 2, 3), repeat=6):
        v = (t,) + qs
        weight = F(1,6) * prod(F(p-3 if a == 3 else 1, p-1)
                               for p,a in zip(P[1:], qs))
        x = crt(v)
        if any(x % m == a for m,a in STARS):
            continue
        base_mass += weight
        inside_e = all(v[P.index(p)] % p == 2 for p in FORCED)
        if inside_e:
            e_mass += weight
        for k,squares in enumerate((SPREAD, ALIGNED)):
            hits = tuple(x % m == a for m,a in squares)
            for j,hit in enumerate(hits):
                single[k][j] += weight*hit
            unions[k] += weight*any(hits)
            if inside_e and not any(hits):
                surv_e[k] += weight
check('base-mass', base_mass == F(2087,3072))
check('first-root-fibre-mass', e_mass == F(1,480))
check('equal-individual-square-masses', single[0] == single[1])
check('spread-kills-fibre', surv_e[0] == 0)
check('aligned-retains-two-thirds', surv_e[1] == F(2,3)*e_mass)
check('different-joint-loss', unions[0] == F(68753,829440) and
      unions[1] == F(23167,331776))

# Independently maximize every squarefree projected cylinder of eta_0.
# A queried root is either 0 or a specified nonzero retained root.
# Each unqueried nonzero category has p-2 members. These are all
# possible first-root query types because the star mask only reads zero.
maxima = {}
for size in range(1,8):
    for support in combinations(P,size):
        free = tuple(p for p in P if p not in support)
        best = F(0)
        for fixed in product((False,True), repeat=size):
            total = F(0)
            for other in product((False,True), repeat=len(free)):
                zero = dict(zip(support,fixed)) | dict(zip(free,other))
                if zero[3] and zero[5]:
                    continue
                if (zero[3] or zero[5]) and any(zero[q] for q in V):
                    continue
                w = prod(F(1,p-1) for p in support)
                w *= prod(F(1 if zero[p] else p-2,p-1) for p in free)
                total += w
            best = max(best,total)
        maxima[support] = best
base_query = sum((mass*prod(F(p,p-1) for p in support)
                  for support,mass in maxima.items()), F(0))
check('complete-base-query', base_query == F(145308365957,61152952320))
conditional_query = base_query/base_mass
check('base-law-crosses-gate', conditional_query < G)

# Conditional rho on E is a product: four fixed first roots with Haar
# tails, and three root-balanced coordinates with Haar tails.
restricted_query_ratio = prod(1 + (F(p,p-1) if p in FORCED
                                    else F(p,(p-1)**2)) for p in P)-1
check('complete-restricted-query',
      restricted_query_ratio == F(431784355,14155776))
check('restricted-query-exceeds-gate', restricted_query_ratio > G)
finite_query_ratio = 2**len(FORCED)-1
check('fifteen-label-witness', finite_query_ratio == 15 and F(15) > G)
# This bound uses only divisors >1 of 1155, all of whose phase-2
# cylinders contain E. It is independent of geometric-tail identities.

# The refill source conditions the centre product on avoiding 15, then
# each q on its active star exclusions. For the actual central cell
# (2,2), no q exclusions are active. Its beta is (1/8)/(7/8)=1/7.
refill_e = F(1,7)*F(1,6)*F(1,10)
check('refill-fibre-mass', refill_e == F(1,420))
private = private_witnesses(SPREAD)
private_aligned = private_witnesses(ALIGNED)
x_survivor = crt((0,2,2,2,2,2,2))
check('global-survivor', all(x_survivor % m != a for m,a in PURE+STARS+SPREAD))

def frac(v):
    return str(v)

out = {
    'scope': 'Actual regression for first-root-marginal preservation and mass-only weighted query bounds; no global cover or all-law obstruction.',
    'source': 'rho is the product Haar law conditioned on x_p mod p != 1; eta_0=rho|J^c; nu_0=eta_0/eta_0(1). eta_0 is NOT the full-survivor eta of TC7 after square additions.',
    'originals': PURE+STARS+SPREAD,
    'aligned_originals': PURE+STARS+ALIGNED,
    'private_witnesses': private,
    'aligned_private_witnesses': private_aligned,
    'eta_0_mass': frac(base_mass),
    'eta_0_E': frac(e_mass),
    'nu_0_E': frac(e_mass/base_mass),
    'refill_E': frac(refill_e),
    'single_square_masses_both_families': list(map(frac,single[0])),
    'square_union_masses_spread_aligned': list(map(frac,unions)),
    'E_survivor_masses_spread_aligned': list(map(frac,surv_e)),
    'R_eta_0': frac(base_query),
    'R_nu_0': frac(conditional_query),
    'restricted_R_per_mass': frac(restricted_query_ratio),
    'finite_query_lower_bound_per_mass': finite_query_ratio,
    'global_survivor': x_survivor,
    'checks': checks,
}
parser=argparse.ArgumentParser()
parser.add_argument('--output')
args=parser.parse_args()
text=json.dumps(out,indent=2)+'\n'
if args.output:
    with open(args.output,'w') as f:
        f.write(text)
else:
    print(text,end='')
