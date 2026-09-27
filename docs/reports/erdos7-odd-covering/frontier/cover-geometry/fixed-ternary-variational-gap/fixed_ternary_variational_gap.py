#!/usr/bin/env python3
"""Exact primal and dual checks for the fixed-ternary variational gap.

The parameter-uniform proof and complete-height reduction are in Report571.
These finite cases check the certificates; they do not prove that theorem
by bounded enumeration. No solver or Lean is used.
"""
from fractions import Fraction as F
from pathlib import Path
from math import isqrt, prod
import json

checks={}
def need(name,value):
    if name in checks or not value: raise ValueError(name)
    checks[name]=True

def crt(t,x,p):
    return (t+3*((x-t)*pow(3,-1,p)%p))%(3*p)

def maxima(law,p):
    out={}
    for m in [3,p,3*p]:
        mass={}
        for x,v in law.items():mass[x%m]=mass.get(x%m,F(0))+v
        out[m]=max(mass.values(),default=F(0))
    return out

results=[]
for p in [5,7,11,13,17,19,23,29,101,1009]:
    tag=str(p)+':'
    need(tag+'prime',all(p%d for d in range(2,isqrt(p)+1)))
    n=p-1
    cells=[(t,x) for t in [0,1] for x in range(p) if (t,x)!=(1,1)]
    U={crt(t,x,p) for t,x in cells}
    need(tag+'actual_survivor',U=={z for z in range(3*p) if z%3!=2 and z%(3*p)!=1})
    all_law={crt(t,x,p):(F(1,2*n) if x==1 or t==1 else F(n-1,2*n*n)) for t,x in cells}
    fixed_law={crt(t,x,p):(F(0) if x==1 else F(1,2*n)) for t,x in cells}
    need(tag+'witness_probabilities',sum(all_law.values())==sum(fixed_law.values())==1)
    need(tag+'global_full_support',all(all_law[z]>0 for z in U))
    amax=maxima(all_law,p);fmax=maxima(fixed_law,p)
    need(tag+'global_maxima',amax=={3:F(1,2),p:F(2*n-1,2*n*n),3*p:F(1,2*n)})
    need(tag+'fixed_maxima',fmax=={3:F(1,2),p:F(1,n),3*p:F(1,2*n)})
    all_R=F(3,2)*amax[3]+F(p,n)*amax[p]+F(3*p,2*n)*amax[3*p]
    fixed_R=F(3,2)*fmax[3]+F(p,n)*fmax[p]+F(3*p,2*n)*fmax[3*p]
    target_fixed=F(3,4)+F(7*p,4*n*n)
    target_all=target_fixed-F(p,2*n**3)
    need(tag+'primal_values',all_R==target_all and fixed_R==target_fixed)
    need(tag+'strict_gap',fixed_R-all_R==F(p,2*n**3)>0)
    c2=F(p,n*n); c1=F(3*p,2*n)-c2
    alpha=(F(3,2)+c1/n)/2;beta=F(3,2)-alpha
    lam3={0:alpha,1:beta,2:F(0)}
    lamp={x:(F(0) if x==1 else F(p,n*n)) for x in range(p)}
    lamjoint={(t,x):(c2 if x==1 else c1/n if t==1 else F(0)) for t,x in cells}
    need(tag+'dual_nonnegative',min(list(lam3.values())+list(lamp.values())+list(lamjoint.values()))>=0)
    need(tag+'dual_budgets',sum(lam3.values())==F(3,2) and sum(lamp.values())==F(p,n) and sum(lamjoint.values())==F(3*p,2*n))
    need(tag+'dual_every_surviving_cell',all(lam3[t]+lamp[x]+lamjoint[t,x]==target_all for t,x in cells))
    slope=F(3,4)-F(7*p,4*n*n)
    need(tag+'fixed_slope_positive',slope>0 and 4*n*n*slope==(n-4)*(3*n+5)+13)
    need(tag+'fixed_good_fibre_dual',F(3,4)+F(p,n*n)+F(3*p,4*n*n)==target_fixed)
    need(tag+'fixed_bad_fibre_dual',F(3,2)==target_fixed+slope)
    # The global witness is also a product/delete posterior when ternary weights may vary.
    u={0:F(n-1,2*n-1),1:F(n,2*n-1)}
    w={x:(F(1,n) if x==1 else F(n-1,n*n)) for x in range(p)}
    raw={crt(t,x,p):u[t]*w[x] for t,x in cells}
    s=sum(raw.values())
    need(tag+'free_ternary_prior',sum(u.values())==sum(w.values())==1 and s==F(2*(n-1),2*n-1))
    need(tag+'free_ternary_attains_global',{z:v/s for z,v in raw.items()}==all_law)
    results.append(dict(p=p,n=n,min_all=all_R,min_fixed= fixed_R,gap=fixed_R-all_R,
                        global_maxima=amax,fixed_maxima=fmax,dual=dict(alpha=alpha,beta=beta,c1=c1,c2=c2),
                        fixed_slope=slope,free_ternary_survival=s))

p5=results[0]
need('p5_regression',p5['min_all']==F(161,128) and p5['min_fixed']==F(83,64) and p5['gap']==F(5,128))
unused=[7,11,13,17,19]
euler=prod((F(p,p-1) for p in unused),start=F(1))
lifted_all=(1+p5['min_all'])*euler-1
lifted_fixed=(1+p5['min_fixed'])*euler-1
need('unused_tensor_gap',(lifted_fixed-lifted_all)==F(5,128)*euler)
need('original_privatization',2%3==2 and 1%3!=2)
output=dict(scope='Finite rational primal/dual certificates for the general ordinary proof; all-height and arbitrary-prime statements are proved separately, not inferred from these diagnostics.',
            results=results,unused_prime_lift=dict(primes=unused,euler=euler,min_all=lifted_all,min_fixed=lifted_fixed,gap=lifted_fixed-lifted_all),
            checks=checks,check_count=len(checks))
Path(__file__).with_suffix('.json').write_text(json.dumps(output,default=str,indent=2)+'\n')
print('PASS',len(checks),'exact checks for',len(results),'prime instances')
print('p5',p5['min_all'],p5['min_fixed'],p5['gap'])
print('seven-prime lift',lifted_all,lifted_fixed,lifted_fixed-lifted_all)
