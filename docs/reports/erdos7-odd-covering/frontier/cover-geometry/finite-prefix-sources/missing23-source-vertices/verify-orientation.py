"""An exact restricted G16 paired-orientation counterexample.

One zero-extra5 quinary column (column2), source leaves13,22,7,16,25;
all six current losses and H16 use one physical tuple. All prime-multiplier
and extra3-depth tails are summed exactly. Final values include the source
column's common4/5 factor. This is not the full44-cell source comparison.

One preselected physical pattern and its swap test the paired-envelope criterion;
no geometry/source-node search or scan over the64 physical patterns occurs.
"""
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
from math import lcm
import json


def need(c, s):
    if not c:
        raise ValueError(s)


ROWS=(13,22,7,16,25)
BR=(4,4,7,7,7)
LAY=tuple(product((4,7),ROWS,(4,7),ROWS))
OLD=(F(1,6),F(2,3),F(2,3),F(2,3),F(2,3))
ONE=(F(1),)*5
PRIMES=(7,11,13,17,19,29)
THRESHOLDS=(2,4,4,8,8,16)
ZERO={7:tuple(F(x,14) for x in (11,11,9,6,3)),11:tuple(F(x,33) for x in (28,28,28,28,25)),13:tuple(F(x,26) for x in (23,23,23,23,21))}


def law(p,t,positive=False):
    c=F(p-1,p-1-t)
    z=1-c/p
    return ({1:F(0) if positive else z,**{m:c*(p-1)/p**m for m in (2,3,4)}}, c/p if positive else F(1), 1+c/(p-1)-z if positive else 1+c/(p-1))


def mul(a,b):
    low={i:sum((x*y for j,x in a[0].items() for k,y in b[0].items() if j*k==i),F(0)) for i in (1,2,3,4)}
    return low,a[1]*b[1],a[2]*b[2]


def norm(w):
    den=lcm(*(a.denominator for a in w))
    return tuple(int(a*den) for a in w),den


@lru_cache(None)
def vectors(p,t,m,b0,sel,u):
    result=[]
    for a9,a27,a45,a135 in LAY:
        if p==7:
            v=tuple(max(0,-4+6*b0+6*(b==sel)+(b==a9)+7*(1+u)*(r==a27)+7*(b==a45)+7*(1+u)*(r==a135)) for r,b in zip(ROWS,BR))
        else:
            c=p-1 if p else 0
            den=p or 1
            base=den*(4*m-t)-3*c+c*b0
            v=tuple(max(0,base+c*(b==sel)+(den*m-c)*(b==a9)+den*m*(1+u)*(r==a27)+den*m*(b==a45)+den*m*(1+u)*(r==a135)) for r,b in zip(ROWS,BR))
        result.append(v)
    return tuple(result)


GEOMETRY_KEYS=set()


@lru_cache(None)
def geom_int(w,p,t,m,b0,sel,u):
    GEOMETRY_KEYS.add((w,p,t,m,b0,sel))
    return max(sum(a*b for a,b in zip(w,v)) for v in vectors(p,t,m,b0,sel,u))


def geo(w,p,t,m,b0,sel,u):
    iw,den=norm(w)
    return F(geom_int(iw,p,t,m,b0,sel,u),den*(p or 1))


def affine_value(w,p,t,m,b0,sel,u):
    c=F(p-1,p) if p else F(0)
    mass=sum(w)
    bm=max(sum(a for a,b in zip(w,BR) if b==r) for r in (4,7))
    hit=sum(a for a,b in zip(w,BR) if b==sel)
    return m*(4*mass+2*bm+2*(1+u)*max(w))+c*((b0-3)*mass+hit-bm)-t*mass


def expectation(w,p,t,b0,sel,u,dist):
    low,mass,first=dist
    tm=mass-sum(low.values())
    tf=first-sum(m*v for m,v in low.items())
    need(tm>=0 and tf>=5*tm,"full multiplier tail")
    slope=affine_value(w,p,t,6,b0,sel,u)-affine_value(w,p,t,5,b0,sel,u)
    intercept=affine_value(w,p,t,5,b0,sel,u)-5*slope
    return sum(v*geo(w,p,t,m,b0,sel,u) for m,v in low.items() if v)+tf*slope+tm*intercept


@lru_cache(None)
def full_g(source,u,b0,bits):
    # Same six physical labels throughout; zero7/11/13 branches stay joint.
    parts=[((F(1),F(1)),({1:F(1),2:F(0),3:F(0),4:F(0)},F(1),F(1)))]
    total=14*geo(source,7,1,1,b0,bits[0],u)/4
    for index,(p,t) in enumerate(zip(PRIMES,THRESHOLDS)):
        if index:
            cur=F(0)
            for fields,dist in parts:
                w=tuple(a*fields[b==7] for a,b in zip(source,BR))
                cur+=expectation(w,p,t,b0,bits[index],u,dist)/(p-1-t)
            total+=14*cur
        if p in ZERO:
            z=tuple(ZERO[p][b0+(r==bits[index])] for r in (4,7))
            expanded=[]
            for fields,dist in parts:
                expanded.append((tuple(a*b for a,b in zip(fields,z)),dist))
                expanded.append((fields,mul(dist,law(p,t,True))))
            parts=expanded
        else:
            parts=[(fields,mul(dist,law(p,t))) for fields,dist in parts]
    for fields,dist in parts:
        w=tuple(a*fields[b==7] for a,b in zip(source,BR))
        total+=expectation(w,0,16,0,0,u,dist)
    return total


def ceil(x):
    return -(-x.numerator//x.denominator)


def tail_start(key):
    w,p,t,m,b0,sel=key
    a=vectors(p,t,m,b0,sel,16)
    b=vectors(p,t,m,b0,sel,17)
    lines=[]
    for va,vb in zip(a,b):
        v16=sum(x*y for x,y in zip(w,va))
        v17=sum(x*y for x,y in zip(w,vb))
        slope=v17-v16
        lines.append((slope,v16-16*slope))
    best=max(lines)
    bound=16
    for slope,intercept in lines:
        if slope<best[0]:
            bound=max(bound,ceil(F(intercept-best[1],best[0]-slope)))
    # Every cell with a leaf increment has positive hinge for u>=16; all
    # remaining cells have an u-independent hinge. Thus each line is exact.
    return bound


NEW=(F(2,3),F(2,3),F(1,6),F(2,3),F(2,3))
COLUMN=F(4,5)
CASES=((1,(4,7,7,4,7,4)),)

for b0,bits in CASES:
    for bs in (bits,tuple(11-x for x in bits)):
        for weights,u in ((OLD,0),(NEW,0),(ONE,1)):
            full_g(weights,u,b0,bs)
# For u>=16 each leaf-hit hinge is nonnegative and affine, and unhit
# hinges are constant. The100 layout lines give an exact tail crossover.
U=max(tail_start(key) for key in GEOMETRY_KEYS)

@lru_cache(None)
def positive(b0,bs):
    finite=sum((F(2,3**(u+1))*full_g(ONE,u,b0,bs)
                for u in range(1,U)),F(0))
    at=full_g(ONE,U,b0,bs)
    slope=full_g(ONE,U+1,b0,bs)-at
    intercept=at-U*slope
    return finite+F(1,3**U)*(slope*(U+F(1,2))+intercept)

rows=[]
for b0,bits in CASES:
    swapped=tuple(11-x for x in bits)
    old0=[COLUMN*full_g(OLD,0,b0,bs) for bs in (bits,swapped)]
    new0=[COLUMN*full_g(NEW,0,b0,bs) for bs in (bits,swapped)]
    plus=[COLUMN*positive(b0,bs) for bs in (bits,swapped)]
    old=[x+y for x,y in zip(old0,plus)]
    new=[x+y for x,y in zip(new0,plus)]
    mixed=[F(4,7)*old0[i]+F(3,7)*old0[1-i]+plus[i] for i in (0,1)]
    d0,dp=old0[0]-old0[1],plus[0]-plus[1]
    best=max(old)
    need(d0*(4*d0+7*dp)<0,'preselected paired-envelope failure')
    need(all(new[i]<=mixed[i] for i in (0,1)),'exchange inequality')
    need(mixed[0]>best and all(x<best for x in new),
         'failure is in the mixed bound, not actual restricted domination')
    def physical(c):
        return (2,2,c,1) if b0==1 else (1,2,c,1)
    # On root1/column2, fixed3,5,15 hits are sigma3=1,
    # sigma5=2, sigma15=7. This checks the stated physical realization.
    for c in bits:
        x=physical(c)
        need((x[0]==1)+(x[1]==2)+(x[3]==7)==b0,'physical base')
    rows.append(dict(base=b0,physical=tuple(physical(c) for c in bits),
        mod9=bits,mod9_swapped=swapped,source_column_factor=str(COLUMN),
        extra3_affine_from=U,
        G0_A=list(map(str,old0)),G0_B=list(map(str,new0)),
        Gplus=list(map(str,plus)),G_A=list(map(str,old)),G_B=list(map(str,new)),
        mixed_bounds=list(map(str,mixed)),old_pair_max=str(best),
        d0=str(d0),dplus=str(dp),weak_product=str(d0*(4*d0+7*dp)),
        mix_minus_old_max=[str(x-best) for x in mixed],
        actual_new_minus_old_max=[str(x-best) for x in new],
        actual_new_dominated=all(x<=best for x in new)))
print(json.dumps(dict(scope=__doc__,prime_order=PRIMES,cases=rows),indent=2))
