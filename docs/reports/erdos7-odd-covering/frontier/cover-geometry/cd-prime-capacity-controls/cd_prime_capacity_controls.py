#!/usr/bin/env python3
"""Exact local-capacity cyclic CRT controls.

Python 3 standard library only; writes deterministic JSON to stdout.
Run from any working directory. No sampling or floating-point comparisons
are used in the certificates; decimal fields are display values only.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import gcd, isqrt, lcm, prod
import json


def primes_upto(n):
    return [p for p in range(2,n+1)
            if all(p%d for d in range(2, isqrt(p)+1))]


def factor(n):
    out={}
    p=2
    while p*p<=n:
        while n%p==0:
            out[p]=out.get(p,0)+1
            n//=p
        p+=1
    if n>1: out[n]=out.get(n,0)+1
    return out


def crt(spec):
    x,m=0,1
    for a,n in spec:
        x += ((a-x)*pow(m,-1,n)%n)*m
        m *= n
        x %= m
    return x


def data(D):
    fs={d:factor(d) for d in D}
    P=sorted(set().union(*(set(v) for v in fs.values())))
    h={p:max(v.get(p,0) for v in fs.values()) for p in P}
    N={p:set() for p in P}
    for v in fs.values():
        for p,q in combinations(v,2):
            N[p].add(q); N[q].add(p)
    return fs,P,h,N


def canonical(D):
    fs,P,h,N=data(D)
    assert all(len(N[p])+(h[p]>=2)<=p-1 for p in P)
    colors={p:{q:1+(h[p]>=2)+j for j,q in enumerate(sorted(N[p]))} for p in P}
    B={}
    for d,f in fs.items():
        T=sorted(f)
        if len(T)==1:
            p=T[0]; a=f[p]
            B[d]=0 if h[p]==1 else p**(a-1)
        else:
            nxt={p:T[(j+1)%len(T)] for j,p in enumerate(T)}
            B[d]=crt([(colors[p][nxt[p]]*p**(a-1),p**a) for p,a in f.items()])
    M={}
    safe={}
    for p in P:
        low={colors[p][q] for q in N[p] if q<p}
        if h[p]==1:
            safe[p]=[y for y in range(p) if y and y not in low]
            M[p]=p-1-len(low)
        else:
            allowed=set(range(2,p))-low
            def good(y):
                if y==0: return True
                while y%p==0: y//=p
                return y%p in allowed
            safe[p]=[y for y in range(p**h[p]) if good(y)]
            M[p]=1+(p-2-len(low))*(p**h[p]-1)//(p-1)
        assert len(safe[p])==M[p]>0
    Q=lcm(*D)
    xstar=crt([(0 if h[p]>=2 else p-1,p**h[p]) for p in P])
    assert all(xstar%d!=B[d] for d in D)
    assert all((B[d]-B[e])%gcd(d,e)!=0
               for d,e in combinations(D,2) if gcd(d,e)>1)
    assert all(any(all(y%p**a != B[d]%p**a for y in safe[p])
                       for p,a in fs[d].items()) for d in D)
    return B,Q,xstar,prod(M.values()),M


def psi(D):
    D=tuple(D); n=len(D)
    closed=[(1<<i)|sum(1<<j for j in range(n) if j!=i and gcd(D[i],D[j])>1)
            for i in range(n)]
    @lru_cache(None)
    def go(mask):
        if not mask: return Fraction(1)
        i=(mask&-mask).bit_length()-1
        return go(mask&~(1<<i))-Fraction(1,D[i])*go(mask&~closed[i])
    return go((1<<n)-1)


def all_divisors_nonunit(Q):
    return [d for d in range(2,Q+1) if Q%d==0]


small=[]
palettes=[
    ("prime_two_height_one",all_divisors_nonunit(54)),
    ("prime_two_high_isolated",[2,4,8,3,5,15,25,75]),
    ("mixed_heights_and_support_cycles",all_divisors_nonunit(25725)),
    ("nonclosed_but_capacity_passes",[3,9,5,25,45]),
]
for name,D in palettes:
    B,Q,xstar,safe_count,M=canonical(D)
    count=sum(all(x%d!=B[d] for d in D) for x in range(Q))
    val=psi(D)
    assert val==Fraction(count,Q)>=Fraction(safe_count,Q)>0
    small.append({"name":name,"moduli":D,"residues":[B[d] for d in D],
                  "Q":Q,"xstar":xstar,"avoidance_count":count,"psi":str(val),
                  "product_survivor_count":safe_count,"Mp":M})

# All intersecting support pairs on five labels: the cycle lemma regression.
base=[2,3,5,7,11]
supports=[T for k in range(2,6) for T in combinations(base,k)]
cycle_checks=0
for T,U in combinations(supports,2):
    intersection=set(T)&set(U)
    if not intersection: continue
    st={p:T[(i+1)%len(T)] for i,p in enumerate(T)}
    su={p:U[(i+1)%len(U)] for i,p in enumerate(U)}
    assert any(st[p]!=su[p] for p in intersection)
    cycle_checks+=1

# Exhaust every residue assignment on a small capacity palette.
D=[2,3,6]
floor=psi(D)
avoid_counts=[sum(all(x%d!=a for d,a in zip(D,assignment)) for x in range(6))
              for assignment in product(*(range(d) for d in D))]
assert min(avoid_counts)==6*floor==1

# The nonclosed necessity counterexample, kept as literal integers.
bad={3:0,5:0,7:0,9:1,45:11,63:50}
assert all((bad[d]-bad[e])%gcd(d,e)!=0
           for d,e in combinations(bad,2) if gcd(d,e)>1)
bad_avoid=sum(all(x%d!=a for d,a in bad.items()) for x in range(315))
assert bad_avoid==110
_,_,bh,bN=data(bad)
assert len(bN[3])+(bh[3]>=2)==3>2

# Connected 100-prime degree-bounded graph and exact scalar certificates.
P=[p for p in primes_upto(547) if p>=3]
assert len(P)==100
degree={p:0 for p in P}
edges=[]
N={p:set() for p in P}
for p,q in combinations(P,2):
    if degree[p]<p-2 and degree[q]<q-2:
        edges.append((p,q))
        degree[p]+=1; degree[q]+=1
        N[p].add(q); N[q].add(p)
seen={P[0]}
while True:
    new=seen|set().union(*(N[p] for p in seen))
    if new==seen: break
    seen=new
assert len(edges)==3673 and len(seen)==100
A={p:sum((Fraction(1,p**(a-1)*(p-1)) for a in range(1,4)),Fraction()) for p in P}
S=sum((A[p]-Fraction(1,p-1) for p in P),Fraction())+sum((A[p]*A[q] for p,q in edges),Fraction())
prime_reciprocal=sum((Fraction(1,p) for p in P),Fraction())
assert S>Fraction(1002858,1000000)>1
assert prime_reciprocal>1
assert 3*len(P)+9*len(edges)==33357
assert 7*len(P)+49*len(edges)==180677
assert 1+7*sum(p-1 for p in P)==172047
# At each p, normalized pq-child colors are 1..degree[p]; p^2 is p-1.
assert all(len(set(range(1,degree[p]+1))|{p-1})==degree[p]+1 for p in P)

print(json.dumps({
    "small_canonical_controls":small,
    "distinct_intersecting_support_pair_checks":cycle_checks,
    "all_assignments_on_2_3_6":{"assignments":len(avoid_counts),"minimum_avoidance":str(floor)},
    "nonclosed_necessity_counterexample":{"residues_by_modulus":bad,"period":315,"avoidance_count":bad_avoid,"psi":str(psi(bad))},
    "hundred_prime_scalar_control":{
        "primes":P,"edges":len(edges),"connected":len(seen)==100,
        "height_three_modulus_count":33357,"S_exact":str(S),"S_decimal":float(S),
        "S_lower_bound":"1002858/1000000","prime_reciprocal_exact":str(prime_reciprocal),
        "prime_reciprocal_decimal":float(prime_reciprocal),
        "all_star_costs_zero":True,"full_palette_niceness_omega_Q_over_3":100,
        "height_seven_modulus_count":180677,"height_seven_Tarsi_rhs":172047,
        "degrees":degree}
},indent=2))
