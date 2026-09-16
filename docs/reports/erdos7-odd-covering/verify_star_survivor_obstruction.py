#!/usr/bin/env python3
"""Exact star-family Gamma certificate for the Erdős #7 problem dossier.
Python 3.8+ standard library. No solver output, repository state, or floating
arithmetic is used to decide a comparison. The full-height argument is in
Problems/erdos-7-odd-covering-systems.md.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
import json
from pathlib import Path
import sys

PRIMES = (3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73)
PINNED_M = (44425,25593,17916,13925,13125,12215,11932,11539,11178,11092,
            10897,10801,10761,10691,10607,10541,10522,10473,10445,10432)
SCALE = 10000

def require(ok, message):
    if not ok:
        raise ValueError(message)

def tree_recurrence(p,k,h):
    u=v=F(0)
    ui=vi=0
    records=[]
    for r in range(h-1,-1,-1):
        w=2*r+3
        a,b=w+u,w+v
        u,v=a/p,a*b/(a+k*b)
        ai,bi=SCALE*w+ui,SCALE*w+vi
        ui,vi=ai//p,ai*bi//(ai+k*bi)
        require(F(ui,SCALE)<=u and F(vi,SCALE)<=v, 'floor approximation')
        records.append({'depth':r,'u_floor':ui,'v_floor':vi})
    return 1+v, SCALE+vi, records

def allowed(x,p,k,h):
    for _ in range(h):
        digit=x%p
        x//=p
        if digit!=p-1:
            return p-k-1<=digit<=p-2
    return True

def tree_law(p,k,h):
    """Explicit leaf probabilities, for small exhaustive checks only."""
    u=[F(0)]*(h+1)
    v=[F(0)]*(h+1)
    for r in range(h-1,-1,-1):
        w=2*r+3
        u[r]=(w+u[r+1])/p
        v[r]=1/(F(k)/(w+u[r+1])+1/(w+v[r+1]))
    weights={}
    for t in range(p**h):
        if not allowed(t,p,k,h):
            continue
        mass=F(1)
        digits=t
        for r in range(h):
            digit=digits%p
            digits//=p
            w=2*r+3
            if digit==p-1:
                mass*=v[r]/(w+v[r+1])
            else:
                mass*=v[r]/(w+u[r+1])
                mass/=p**(h-r-1)
                break
        weights[t]=mass
    require(sum(weights.values(),F(0))==1,'tree law normalization')
    for x in range(p**h):
        if not allowed(x,p,k,h):
            continue
        potential=F(0)
        for t,mass in weights.items():
            ell=sum(x%(p**e)==t%(p**e) for e in range(1,h+1))
            potential+=mass*(1+ell)**2
        require(potential==1+v[0], 'pointwise equal potential')
    return len(weights)

def star_family(primes,heights):
    out=[]
    for exponents in product(*(range(h+1) for h in heights)):
        active=[i for i,e in enumerate(exponents) if e]
        if not active:
            continue
        modulus=prod(p**e for p,e in zip(primes,exponents))
        if len(active)==1:
            i=active[0]
            p,e=primes[i],exponents[i]
            residue=p**(e-1)-1
        elif len(active)==2 and active[0]==0 and primes[0]==3:
            moduli=[primes[i]**exponents[i] for i in active]
            values=[2*primes[i]**(exponents[i]-1)-1 for i in active]
            residue=sum(a*(modulus//d)*pow(modulus//d,-1,d)
                        for a,d in zip(values,moduli))%modulus
        else:
            residue=0
        out.append((modulus,residue))
    require(len(out)==prod(h+1 for h in heights)-1,'complete divisor list')
    require(len({d for d,a in out})==len(out),'distinct moduli')
    return out

def in_s(x,p,h):
    return all(x%(p**e)!=p**(e-1)-1 for e in range(1,h+1))

def in_c(x,p,h):
    return any(x%(p**e)==2*p**(e-1)-1 for e in range(1,h+1))

def check_small_family(primes,heights):
    family=star_family(primes,heights)
    Q=prod(p**h for p,h in zip(primes,heights))
    survivors=0
    for x in range(Q):
        actual=all(x%d!=a for d,a in family)
        all_s=all(in_s(x,p,h) for p,h in zip(primes,heights))
        ternary_exception=x%(3**heights[0])==3**heights[0]-1
        branch_b=in_c(x,3,heights[0]) and all(
            not in_c(x,p,h) for p,h in zip(primes[1:],heights[1:]))
        decomposition=all_s and (ternary_exception or branch_b)
        require(actual==decomposition,'actual survivor decomposition')
        survivors+=actual
    require(survivors>0,'nonempty survivor family')
    return {'primes':list(primes),'heights':list(heights),
            'period':Q,'divisors':len(family)+1,'survivors':survivors}

def check_large_witness():
    """Check the actual height-31/8 assignment at one full CRT witness."""
    require(PRIMES == tuple(n for n in range(3,74,2)
                           if all(n%d for d in range(2,n))), 'complete prime set')
    heights=(31,)+(8,)*(len(PRIMES)-1)
    powers=tuple(p**h for p,h in zip(PRIMES,heights))
    Q=prod(powers)
    coordinates=(1,)+(2,)*(len(PRIMES)-1)
    witness=sum(a*(Q//d)*pow(Q//d,-1,d)
                for a,d in zip(coordinates,powers))%Q
    require(all(witness%d==a for d,a in zip(powers,coordinates)), 'full CRT witness')
    for p,h in zip(PRIMES,heights):
        require(in_s(witness,p,h), 'full witness hits a pure class')
    for p,h in zip(PRIMES[1:],heights[1:]):
        for i in range(1,heights[0]+1):
            for j in range(1,h+1):
                require(not (witness%(3**i)==2*3**(i-1)-1
                             and witness%(p**j)==2*p**(j-1)-1),
                        'full witness hits a star class')
    # Every remaining assigned class is zero modulo some prime factor.
    require(all(witness%p for p in PRIMES), 'full witness hits a mixed zero class')
    require(Q%2==1 and prod(h+1 for h in heights)>1, 'odd nontrivial period')

def main():
    require(len(sys.argv)<=2, 'usage: verify_star_survivor_obstruction.py [certificate]')
    check_large_witness()
    rows=[]
    values=[]
    for p,m in zip(PRIMES,PINNED_M):
        k=1 if p==3 else p-3
        exact,observed,steps=tree_recurrence(p,k,8)
        require(observed==m,'pinned integer table')
        require(exact>=F(m,SCALE),'exact rational dominates integer table')
        rows.append({'prime':p,'side_children':k,'m':m,'steps':steps})
        values.append(exact)
    B=prod(values)
    lower_B=F(prod(PINNED_M),SCALE**len(PRIMES))
    A_factor=prod(F(p+2,p-1) for p in PRIMES[1:])
    require(lower_B>141,'depth-eight branch potential > 141')
    require(A_factor>14,'exceptional-branch product > 14')
    a_mix=F(32**2,100)*A_factor
    b_mix=F(99,100)*lower_B
    uniform_lower=min(a_mix,b_mix)
    require(uniform_lower>F(13959,100)>F(138877,1000),'Gamma threshold')
    tiny_trees=[]
    for p,k,h in [(3,1,1),(3,1,2),(3,1,3),(5,2,2),(7,4,2)]:
        tiny_trees.append({'prime':p,'side_children':k,'height':h,
                           'support':tree_law(p,k,h)})
    tiny_families=[check_small_family((3,5),(3,2)),
                   check_small_family((3,5,7),(2,2,2))]
    cert={'primes':list(PRIMES),'height_3':31,'height_other':8,
          'tree_depth':8,'scale':SCALE,'rows':rows,
          'branch_a_factor':str(A_factor),'branch_b_lower':str(lower_B),
          'mixture_weight_a':'1/100','mixture_weight_b':'99/100',
          'uniform_gamma_lower':str(uniform_lower),
          'comparison':'138877/1000','simple_strict_lower':'13959/100',
          'small_tree_checks':tiny_trees,'small_actual_families':tiny_families}
    target=(Path(sys.argv[1]) if len(sys.argv)>1 else
            Path(__file__).with_name('star_survivor_obstruction_certificate.json'))
    require(json.loads(target.read_text())==cert,'fixed certificate equality')
    print(json.dumps({'result':'PASS','branch_b_floor':str(lower_B),
                      'branch_b_floor_decimal':float(lower_B),
                      'branch_b_exact_decimal':float(B),
                      'uniform_gamma_lower_decimal':float(uniform_lower),
                      'strict_simple_gamma_lower':'13959/100',
                      'actual_family_points_checked':sum(r['period'] for r in tiny_families),
                      'scope':'Exact rational certificate plus small exhaustive regressions; full lifting is ordinary proof.'}))

if __name__=='__main__':
    main()
