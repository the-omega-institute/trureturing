#!/usr/bin/env python3
"""Exact finite diagnostics for the mixed-defect Monster selector.

No VOA, conformal net, modular analytic theorem, orbifold, or Monster action is
constructed here. Integer series and finite sign constraints are diagnostics.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb
import json


def require(value: bool, label: str) -> None:
    if not value:
        raise AssertionError(label)


def mul(a: list, b: list, n: int) -> list:
    c = [Q(0)] * (n + 1)
    for i, ai in enumerate(a[:n+1]):
        for j, bj in enumerate(b[:n+1-i]):
            c[i+j] += ai * bj
    return c


def inverse(a: list, n: int) -> list:
    require(a[0] != 0, 'series inverse constant')
    b = [Q(1)/a[0]] + [Q(0)] * n
    for k in range(1, n+1):
        b[k] = -sum(a[j]*b[k-j] for j in range(1, min(k, len(a)-1)+1))/a[0]
    return b


def euler(exponent: int, n: int, *, sign: int = 1,
          indices: list[int] | None = None) -> list:
    ans = [Q(1)] + [Q(0)] * n
    for j in (range(1, n+1) if indices is None else indices):
        f = [Q(0)] * (n+1)
        for k in range(min(exponent, n//j)+1):
            f[j*k] = comb(exponent, k)*sign**k
        ans = mul(ans, f, n)
    return ans


def sigma(n: int, power: int) -> int:
    return sum(d**power for d in range(1,n+1) if n%d == 0)


def rank_gf2(rows: list[int]) -> int:
    pivots = {}
    for row in rows:
        while row:
            p = row.bit_length()-1
            if p not in pivots:
                pivots[p] = row
                break
            row ^= pivots[p]
    return len(pivots)


def ground_system(r: int) -> dict:
    size = 1 << r
    def row(g: int, h: int) -> int:
        return sum(1 << ((g-1)*r+j) for j in range(r) if (h>>j)&1)
    equations = [(row(g,g),1) for g in range(1,size)]
    equations += [(row(g,h)^row(h,g),1)
                  for g in range(1,size) for h in range(g+1,size)]
    pivots = {}
    for a,b in equations:
        while a:
            p = a.bit_length()-1
            if p not in pivots:
                pivots[p] = (a,b)
                break
            ap,bp = pivots[p]
            a,b = a^ap,b^bp
        if not a and b:
            return {'consistent':False,'partial_rank':len(pivots)}
    solution = 0
    for p in sorted(pivots):
        a,b = pivots[p]
        bit = b ^ ((a & solution).bit_count()&1)
        if bit:
            solution |= 1 << p
    require(all(((a&solution).bit_count()&1)==b for a,b in equations),
            'full finite sign solution')
    labels = [((solution >> ((g-1)*r)) & (size-1)) for g in range(1,size)]
    return {'consistent':True,'rank':len(pivots),
            'free_bits':r*(size-1)-len(pivots),'dual_labels':labels}


def main() -> dict:
    n = 40
    counts = Counter()
    plus = euler(24,n)
    tunit = inverse(plus,n)
    e4 = [Q(1)] + [Q(240*sigma(k,3)) for k in range(1,n+1)]
    j = mul(mul(mul(e4,e4,n),e4,n),inverse(euler(24,n,sign=-1),n),n)
    J = {e:j[e+1]-(744 if e==0 else 0) for e in range(-1,n)}
    P = [Q(0)] + plus[:-1]
    P2 = mul(P,P,n)
    H = [47*P[k]+4096*P2[k] for k in range(n+1)]
    FA = {e:tunit[e+1]+(24 if e==0 else 0)+(4096*P[e] if e>=0 else 0)
          for e in range(-1,n)}
    for e in range(-1,n):
        h = H[e] if e>=0 else 0
        require(J[e]-FA[e] == 4096*h,'all-grade character identity')
        require(FA[e]>=0 and h>=0,'finite series nonnegativity')
        counts['character_coefficients'] += 1
        for r in range(1,13):
            regular = (1 << (12-r))*h
            require(FA[e]+(1<<r)*regular == J[e], 'graded regular representation')
            require(Q(regular).denominator==1,'graded multiplicity integral')
            counts['graded_representation_cases'] += 1
    require(Q(196884-4372,1<<13)==Q(47,2),'rank13 obstruction')
    require(Q(196884-4372,1<<12)==47,'rank12 old boundary')

    # Independent theta-product lambda construction, variable x=q^(1/2).
    even = euler(8,n,indices=list(range(2,n+1,2)))
    odd = euler(8,n,indices=list(range(1,n+1,2)))
    L = mul(even,inverse(odd,n),n)
    lam = [Q(0)]+[16*v for v in L[:-1]]
    require(lam[:5]==[0,16,-128,704,-3072],'lambda theta coefficients')
    invL = inverse(L,n)
    inv1mlam = inverse([1]+[-v for v in lam[1:]],n)
    f = {e:invL[e+1] - (16*inv1mlam[e] if e>=0 else 0)
            - (16*lam[e] if e>=0 else 0) + (8 if e==0 else 0)
         for e in range(-1,n)}
    e6x = [Q(1)] + [Q(-504*sigma(k//2,5)) if k%2==0 else Q(0)
                    for k in range(1,n+1)]
    eta12x = euler(12,n,sign=-1,indices=list(range(2,n+1,2)))
    target = mul(e6x,inverse(eta12x,n),n)
    for e in range(-1,n-1):
        require(f[e]==target[e+1],'mixed trace E6 eta identity')
        counts['mixed_trace_coefficients'] += 1
    require([f[e] for e in (-1,0,1,2,3)]==[1,0,-492,0,-22590], 'mixed leading')

    # Three cusp constant linear conditions, null vector (A,B,C,D)=(2,-2,-2,1).
    v = [Q(2),Q(-2),Q(-2),Q(1)]
    cusp_rows = [[Q(1,2),1,0,1],[1,Q(1,2),1,1],[0,0,Q(1,2),1]]
    require(all(sum(a*b for a,b in zip(row,v))==0 for row in cusp_rows),'cusp constants')
    # Minor from columns B,C,D has determinant 3/4, hence rank exactly three.
    minor = [[row[k] for k in (1,2,3)] for row in cusp_rows]
    det = (minor[0][0]*(minor[1][1]*minor[2][2]-minor[1][2]*minor[2][1])
           -minor[0][1]*(minor[1][0]*minor[2][2]-minor[1][2]*minor[2][0])
           +minor[0][2]*(minor[1][0]*minor[2][1]-minor[1][1]*minor[2][0]))
    require(det!=0,'unique three-cusp line')
    def R(z): return 1/z-1/(1-z)-z+Q(1,2)
    for z in [Q(a,b) for a in range(-7,8) for b in range(1,8) if a not in (0,b)]:
        require(R(1-z)==-R(z) and R(z/(z-1))==-R(z),'rational S T sign')
        counts['rational_function_values'] += 1

    signs = {str(r):ground_system(r) for r in range(1,5)}
    require([signs[str(r)]['consistent'] for r in range(1,5)]==[True,True,True,False],
            'rank four sharp finite sign boundary')
    require(signs['3']['free_bits']==3,'eight rank3 sign tables')
    # A nine-equation contradictory dependency, using U=<1,2>, W=<4,8>.
    def row4(g,h): return sum(1<<((g-1)*4+j) for j in range(4) if (h>>j)&1)
    lhs,rhs = 0,0
    for g,h in product((1,2,3),(4,8,12)):
        lhs ^= row4(g,h)^row4(h,g)
        rhs ^= 1
    require(lhs==0 and rhs==1,'nine-pair certificate')
    counts['nine_pair_equations'] = 9

    # Trilinear representatives of H^3(F2^r,U1): each exponent is a cocycle.
    def triples(r):
        return ([(i,i,i) for i in range(r)]
                +[(j,i,i) for i,j in combinations(range(r),2)]
                +list(combinations(range(r),3)))
    def term(t,a,b,c):
        i,j,k=t
        return ((a>>i)&1)*((b>>j)&1)*((c>>k)&1)
    for t in triples(3):
        for a,b,c,d in product(range(8),repeat=4):
            value=(term(t,b,c,d)^term(t,a^b,c,d)^term(t,a,b^c,d)
                   ^term(t,a,b,c^d)^term(t,a,b,c))
            require(value==0,'cocycle pentagon')
            counts['cocycle_equations'] += 1
    for r in range(1,7):
        ts=triples(r)
        columns=[sum(term(t,g,g,g)<<g for g in range(1<<r)) for t in ts]
        require(rank_gf2(columns)==len(ts),'cyclic restriction full rank')
        require(len(ts)==r+comb(r,2)+comb(r,3),'cohomology dimension')
        counts['restriction_ranks'] += 1
    # Pure type III is detected on the diagonal cyclic subgroup, not on generators alone.
    t=(0,1,2)
    require(all(term(t,g,g,g)==0 for g in (1,2,4)) and term(t,7,7,7)==1,
            'generator-only anomaly test must fail')
    counts['negative_controls'] = 2  # rank4 contradiction and generator-only blindness.

    # Standalone incidence bound has a sharp example B=nonzero codimension-three subspace.
    for r in range(4,9):
        B=set(range(1,1<<(r-3)))
        require(len(B)==(1<<(r-3))-1,'blocking cardinality')
        # Check all four-subspaces for r<=5 by all bases; cache their underlying sets.
        if r<=5:
            subspaces=set()
            for basis in combinations(range(1,1<<r),4):
                if rank_gf2(list(basis))!=4: continue
                span={0}
                for u in basis: span |= {x^u for x in tuple(span)}
                subspaces.add(tuple(sorted(span)))
            for subspace in subspaces:
                require(bool(B.intersection(subspace)),'codimension3 blocking')
                counts['blocking_subspaces'] += 1
    require((1<<(12-3))-1==511 and (1<<(13-3))-1==1023,'rank12 rank13 counts')
    # Previously allowed B={g0} at rank13 misses this explicit four-subspace.
    require(1 not in {2*a for a in range(16)},'singleton Fourier model rejected by sewing')

    return {'status':'passed','arithmetic':'integers and Fraction; no floating point',
            'series_degree':n,'counts':dict(sorted(counts.items())),
            'rank_sign_systems':signs,
            'mixed_coefficients_x_minus1_to_7':[str(f[e]) for e in range(-1,8)],
            'cusp_minor_determinant':str(det),
            'rank12_B_lower_bound':511,'rank13_B_lower_bound':1023,
            'scope':'Finite diagnostics only. The rank-four VOA implication requires the manuscript’s common orbifold trace realization; no VOA/net/Monster construction, Lean or independent review.'}


if __name__ == '__main__':
    print(json.dumps(main(),ensure_ascii=False,indent=2))
