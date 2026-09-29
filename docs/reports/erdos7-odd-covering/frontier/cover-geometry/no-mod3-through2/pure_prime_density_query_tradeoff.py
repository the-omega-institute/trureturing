#!/usr/bin/env python3
"""Exact diagnostics for the finite-height pure-prime source tradeoff.

Universal source and minimax claims are proved in the companion text.
The existing six-coordinate hinge envelope is an explicit input.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json

ap = argparse.ArgumentParser()
ap.add_argument('--hinge-input', default=str(Path(__file__).with_name('height_three_clipping_envelope.json')))
ap.add_argument('--output', default=str(Path(__file__).with_suffix('.json')))
args = ap.parse_args()
checks = []


def need(name, condition):
    if not condition:
        raise ValueError(name)
    checks.append(name)


def cylinder_masses(weights, depth, p=3):
    masses = [F(0)] * p**depth
    for residue, mass in enumerate(weights):
        masses[residue % p**depth] += mass
    return masses


def response(weights, height, p=3):
    maxima = [max(cylinder_masses(weights, e, p)) for e in range(1, height + 1)]
    # The represented law is Haar within each depth-height cell.
    return maxima, sum(maxima, F(0)) + maxima[-1] / (p-1)


def pure_survivors(height, phases, p=3):
    return [r for r in range(p**height)
            if all(a is None or r % p**e != a for e, a in enumerate(phases, 1))]


def binary_source(height, phases):
    live = [0]
    for e, forbidden in enumerate(phases, 1):
        following = []
        for residue in live:
            children = [residue + digit * 3**(e-1) for digit in range(3)
                        if residue + digit * 3**(e-1) != forbidden]
            if len(children) < 2:
                raise ValueError('fewer than two legal children')
            following.extend(children[:2])
        live = following
    weights = [F(0)] * 3**height
    for r in live:
        weights[r] = F(1, 2**height)
    return weights


comb_rows = []
for p,H in [(3,h) for h in range(1,9)]+[(p,h) for p in (5,7) for h in range(1,5)]:
    modulus = p**H
    forbidden = [p**(e-1) for e in range(1, H+1)]
    survivor = set(pure_survivors(H, forbidden,p))
    exits = [{r for r in range(modulus) if r % p**e == digit*p**(e-1)}
             for e in range(1,H+1) for digit in range(2,p)]
    tag=f'comb p{p} H{H}'
    need(f'{tag} partition', {0}.union(*exits) == survivor
         and 1 + sum(map(len, exits)) == len(survivor))
    need(f'{tag} private original witnesses',
         all(sum(r % p**e == forbidden[e-1] for e in range(1, H+1)) == 1
             for r in forbidden))
    Dmin = F((p-1)*modulus, (p-2)*modulus+1)
    Dstar = F(p,p-1)**H
    Astar = (1-F(1,(p-1)**(H+1)))/(p-2)
    u0 = [F(1, len(survivor)) if r in survivor else F(0) for r in range(modulus)]
    us = [F(0)] * modulus
    us[0] = F(1,(p-1)**H)
    for i,cells in enumerate(exits):
        e=i//(p-2)+1
        for r in cells:
            us[r] = F(1,(p-1)**e * p**(H-e))
    need(f'{tag} normalized sources', sum(u0) == sum(us) == 1)
    m0, r0 = response(u0,H,p)
    ms, rs = response(us,H,p)
    need(f'{tag} Haar maxima', m0 == [Dmin/F(p**e) for e in range(1,H+1)])
    need(f'{tag} balanced maxima', ms == [F(1,(p-1)**e) for e in range(1,H+1)])
    need(f'{tag} endpoint response and density',
         r0 == Dmin/(p-1) and rs == Astar
         and max(u0)*modulus == Dmin and max(us)*modulus == Dstar)
    mixtures = []
    for lam in (F(0),F(1,3),F(1,2),F(2,3),F(1)):
        u = [(1-lam)*v+lam*w for v,w in zip(u0,us)]
        maxima, R = response(u,H,p)
        D = (1-lam)*Dmin+lam*Dstar
        need(f'{tag} exact mixture {lam}', max(u)*modulus == D
             and R == F(1,p-2)-D/F((p-2)*(p-1)*modulus)
             and maxima == [(1-lam)*a+lam*b for a,b in zip(m0,ms)])
        mixtures.append({'lambda':lam,'D':D,'R':R})
    comb_rows.append({'p':p,'H':H,'surviving_cells':len(survivor),
                      'D_min':Dmin,'D_star':Dstar,'A_star':Astar,'mixtures':mixtures})

# Verify the rational coefficients of the universal telescoping dual.
for p,H in product((3,5,7,11),range(1,65)):
    c = [(1-F(1,(p-1)**(H-e+2)))/(p-2) for e in range(1,H+2)]
    need(f'dual coefficients p{p} H{H}', c[-1] == F(1,p-1)
         and all(0 <= (p-2)*x <= 1 for x in c)
         and all((p-1)*c[e]-1 == c[e+1] for e in range(H)))

# All optional pure originals through height three, including redundancies.
H = 3
family_count = 0
Dmin = F(2*3**H,3**H+1)
Dstar = F(3,2)**H
for phases in product(*[(None,*range(3**e)) for e in range(1,H+1)]):
    live = set(pure_survivors(H,phases))
    us = binary_source(H,phases)
    ms, rs = response(us,H)
    u0 = [F(1,len(live)) if r in live else F(0) for r in range(3**H)]
    mixture = [(v+w)/2 for v,w in zip(u0,us)]
    _, rm = response(mixture,H)
    ok = (sum(us) == 1 and all(not mass or r in live for r,mass in enumerate(us))
          and ms == [F(1,2**e) for e in range(1,H+1)]
          and max(us)*3**H == Dstar and rs == 1-F(1,2**(H+1))
          and max(mixture)*3**H <= (Dmin+Dstar)/2
          and rm <= 1-(Dmin+Dstar)/F(4*3**H))
    if not ok:
        raise ValueError(('arbitrary-family source failure',phases))
    family_count += 1
need('all optional height3 families',family_count == 1120)

# Exact attainable height-two query/tail frontier.
frontier = []
for m in (F(1,5),F(5,24),F(9,40),F(6,25),F(1,4)):
    u = [F(0)]*9
    for r in (0,6): u[r] = m
    for r in (2,5,8): u[r] = (1-2*m)/3
    maxima,A = response(u,2)
    theta=maxima[-1]/6
    need(f'height2 cap frontier {m}',sum(u)==1 and maxima==[1-2*m,m]
         and A==1-m/2 and theta==m/6 and max(u)*9==9*m)
    frontier.append({'m':m,'A':A,'theta':theta,'density':9*m})

input_bytes = Path(args.hinge_input).read_bytes()
prior = json.loads(input_bytes)
B = F(prior['B'])
target = F(prior['target'])
need('expected same-source B',B==F(432040125182653876501,86355045355449035400))
need('expected continuation target',target==F(566,49))
corners = [[F(x) for x in c['K_integer'][:8]] for c in prior['corners']]
need('four complete corner input sequences',len(corners)==4 and all(len(c)==8 for c in corners))
need('corner0 dominates every endpoint0 through7',
     all(corners[0][n]>=corners[i][n] for n in range(8) for i in range(1,4)))
K = corners[0]
need('positive monotone first three intervals',all(K[n]>=K[n+1]>=0 for n in range(3)))
need('known exact threshold3 moment',K[3]==F(12019840537595758779003,5715264751774801992890))
derivative_guard=(1+2*B)*K[3]-3*(1+B)
need('source derivative positive for every0 through3 threshold',derivative_guard>0)
theta=F(1,30)
A=F(9,10)
clip_rows=[]
for t,k in enumerate(K):
    kappa=1-theta*t
    den=kappa-theta*k
    need(f'positive clip denominator at{t}',den>0)
    R=(kappa*B+A*(1+B))/den
    clip_rows.append({'t':t,'K':k,'kappa':kappa,'denominator':den,'R':R})
best=min(clip_rows,key=lambda row:row['R'])
tail_lower=B+F(27,23)*(1+B)
need('all remaining real thresholds excluded by nonnegative hinge',tail_lower>best['R'])
need('exact real optimum threshold3',best['t']==3 and
     best['R']==F(5661267838960687810116513,474307692534412983430090))
need('scalar source repair still fails target',best['R']>target)

result={
 'scope':'Exact finite diagnostics for general ordinary proofs. No new Lean verification. The scalar result optimizes only complete tail caps, fixed B/K and one scalar clip.',
 'comb':comb_rows,'all_optional_height3_families':family_count,
 'height2_cap_frontier':frontier,
 'hinge_input_sha256':hashlib.sha256(input_bytes).hexdigest(),
 'B':B,'target':target,'source_derivative_guard':derivative_guard,
 'clip_breakpoints':clip_rows,'clip_best':best,
 'clip_gap':best['R']-target,'clip_t_ge7_lower':tail_lower,
 'check_count':len(checks),'checks':checks}
Path(args.output).write_text(json.dumps(result,default=str,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'height3_families':family_count,
                  'best_t':best['t'],'best_R':str(best['R']),
                  'best_R_decimal':float(best['R']),
                  'gap':str(best['R']-target)}))
