#!/usr/bin/env python3
"""Exact certificates for free-prior product/deletion separation on {3,5}.
The ordinary proof is Report573. Finite checks do not replace it.
No numerical optimizer is used by these checks.
"""
from fractions import Fraction as F
import json
from pathlib import Path
from math import gcd, prod

family=[(3,2),(5,4),(15,0),(45,1)]
# (t mod9,x mod5); pure3 removes t=2 mod3 and pure5 removes x=4.
U=[(t,x) for t in range(9) for x in range(5)
   if t%3!=2 and x!=4 and not(t%3==0 and x==0) and not(t==1 and x==1)]
queries=[3,5,9,15,45]
gamma={3:F(1),5:F(5,4),9:F(3,2),15:F(5,4),45:F(15,8)}

def phase(d,t,x):
 return next(a for a in range(d) if a%gcd(d,9)==t%gcd(d,9) and a%gcd(d,5)==x%gcd(d,5))

def maxima(mu):
 return {d:max(sum((mu.get((t,x),F(0)) for t,x in U if phase(d,t,x)==a),F(0)) for a in range(d)) for d in queries}

def norm(mu):
 return sum((gamma[d]*v for d,v in maxima(mu).items()),F(0))

checks=0
def check(p):
 global checks
 if not p: raise ValueError('failed exact check '+str(checks+1))
 checks+=1

check(len(U)==20)
# Check literal arithmetic originals against the CRT support.
for n in range(45):
 check(((n%9,n%5) in U)==all(n%m!=r for m,r in family))

# Balanced unrestricted attainer: A and row1 each 1/18; Bgood cols0,1
# each 1/18 and cols2,3 each1/36.
mu={(t,x):(F(1,36) if t in (4,7) and x in (2,3) else F(1,18)) for t,x in U}
check(sum(mu.values())==1)
check(maxima(mu)=={3:F(1,2),5:F(5,18),9:F(1,6),15:F(1,6),45:F(1,18)})
check(norm(mu)==F(203,144))

# Nonnegative query dual, keyed by (d, CRT phase).
def ph(d,t,x):return phase(d,t,x)
dual={
 (3,ph(3,0,0)):F(73,144),
 (3,ph(3,1,0)):F(71,144),
 **{(5,ph(5,0,x)):F(5,12) for x in (1,2,3)},
 (15,ph(15,0,1)):F(35,72),
 (15,ph(15,0,2)):F(25,144),
 (15,ph(15,0,3)):F(25,144),
 (15,ph(15,1,0)):F(5,12),
 **{(9,ph(9,t,0)):F(1,2) for t in (1,4,7)},
 **{(45,ph(45,t,x)):F(5,16) for t in (0,3,6) for x in (2,3)},
}
for v in dual.values():check(v>0)
for d in queries:check(sum((v for (dd,a),v in dual.items() if dd==d),F(0))==gamma[d])
for t,x in U:
 check(sum((v for (d,a),v in dual.items() if ph(d,t,x)==a),F(0))==F(203,144))

# Explicit normalized product/deletion source, providing an upper bound.
u={t:(F(2,11) if t in (0,1,3,6) else F(3,22)) for t in (0,1,3,4,6,7)}
w={x:F(1,4) for x in range(4)}
raw={(t,x):u[t]*w[x] for t,x in U}
s=sum(raw.values());prod_law={c:v/s for c,v in raw.items()}
check(sum(u.values())==sum(w.values())==1)
check(s==F(9,11))
check(norm(prod_law)==F(13,9))

# Optimal-face row4 has p41=1/18 and p42+p43=1/18. Every A-row
# has p01=p02=p03=1/18. Two product cycles would force both p42,p43
# to1/18, contradicting that row sum. The balanced attainer exhibits
# the exact defect in each such cycle.
for x in (2,3):
 check(mu[0,1]*mu[4,x]-mu[0,x]*mu[4,1]==-F(1,648))
check(F(1,18)+F(1,18)!=F(1,18))

# The product upper witness obeys both cycles, while no point on the
# optimum face can obey both (the ordinary equality-case proof).
for x in (2,3):
 check(prod_law[0,1]*prod_law[4,x]==prod_law[0,x]*prod_law[4,1])
check(maxima(prod_law)=={3:F(1,2),5:F(11,36),9:F(1,6),15:F(1,6),45:F(1,18)})
unused=[7,11,13,17,19]
euler=prod((F(p,p-1) for p in unused),start=F(1))
lifted_all=(1+F(203,144))*euler-1
lifted_upper=(1+F(13,9))*euler-1
check(lifted_all<lifted_upper<F(566,49))

result={'family':family,'K':45,'survivor_cells':len(U),'all_joint_optimum':str(F(203,144)),
 'product_candidate_upper':str(F(13,9)),
 'strict_infimum_separation':'proved in ordinary proof via optimal-face exclusion and compact closed cycle superset',
 'unused_prime_lift':{'primes':unused,'euler':str(euler),'joint_optimum':str(lifted_all),'product_upper':str(lifted_upper)},
 'checks':checks,'dual':{f'{d}:{a}':str(v) for (d,a),v in sorted(dual.items())},
 'primal':{f'{t}:{x}':str(v) for (t,x),v in mu.items()}}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',checks,'exact checks; joint optimum',F(203,144),'product upper',F(13,9))
