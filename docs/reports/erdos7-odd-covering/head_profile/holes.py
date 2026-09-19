#!/usr/bin/env python3
"""Verify the complete 315 marked-head convex profile using exact arithmetic.

The adjacent fixed certificate contains finite results, not executable input.
Every old-head layout histogram, ordered histogram pair, integer survivor
count and integer threshold is checked.  Only the Python standard library is
used.  The universal pruning and convex-rearrangement argument is stated in
marked_head_profile.md; this program verifies its finite calculation.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path


MODULI = (3, 5, 9, 15, 45)
CATEGORIES = ("same_other_column", "other_same_column", "other_other_column")
THRESHOLDS = range(13)


from head_profile.base import *

def matching_hole_common_lambda():
    """Check symbolic identities and PSD proof patterns, without grid instances."""
    class Polynomial(dict):
        # Sparse integer polynomials in m,n,k,epsilon,j, used only below.
        def __init__(self, value=0):
            super().__init__(value if isinstance(value, dict) else
                             ({(0,)*5: value} if value else {}))

        def __add__(self, other):
            out = dict(self)
            for powers, value in Polynomial(other).items():
                out[powers] = out.get(powers, 0)+value
            return Polynomial({powers: value for powers, value in out.items() if value})

        __radd__ = __add__

        def __mul__(self, other):
            out = {}
            for a, x in self.items():
                for b, y in Polynomial(other).items():
                    powers = tuple(i+j for i, j in zip(a, b))
                    out[powers] = out.get(powers, 0)+x*y
            return Polynomial({powers: value for powers, value in out.items() if value})

        __rmul__ = __mul__

        def __sub__(self, other):
            return self + Polynomial(other)*(-1)

        def __rsub__(self, other):
            return Polynomial(other) + self*(-1)

    m,n,k,e,j = [Polynomial({tuple(int(i==q) for i in range(5)): 1}) for q in range(5)]
    identities = []

    def identity(name, left, right):
        require(not Polynomial(left)-Polynomial(right), name)
        identities.append(name)

    S,V,H = m+n,m*n-k,k*(m+n-k-1)
    A = 3*(S+3)
    B = m*m+n*n+(2-k)*S-k-3
    identity('probability normalization', H*(1+e)+(m-k)*(n-k), V+H*e)
    identity('coefficient sum numerator',
             S+1+2*k*e+2*(n+1+k*e)+2*(m+1+k*e)+4, A+6*k*e)
    identity('strict multiplier gain numerator', A*H-6*k*V, 3*k*B)
    mx,ny = k+1+m,k+1+n
    identity('positive gain polynomial after translation',
             mx*mx+ny*ny+(2-k)*(mx+ny)-k-3,
             5*k+3+(k+4)*(m+n)+m*m+n*n)
    identity('row perturbation bound first slack', 2*n-(2*k+2), 2*(n-k-1))
    identity('row perturbation bound second slack', 2*n-(2*n-2*k), 2*k)
    D = lambda index: m*n-index+e*index*(S-index-1)
    N = lambda index: A+6*e*index
    delta = lambda index: 1-e*(S-2*index-2)
    T = lambda index: 6*e*D(index)+N(index)*delta(index)
    identity('varying-count denominator difference', D(j)-D(j+1), delta(j))
    identity('varying-count factor difference numerator', N(j+1)*D(j)-N(j)*D(j+1), T(j))
    identity('increasing difference numerator', T(j+1)-T(j), 2*e*N(j+1))
    identity('mean-count saving numerator', N(1)*D(0)-N(0)*D(1),
             6*e*m*n+A*(1-e*(S-2)))

    patterns = 0
    for hi,hj,u,v,t in product((0,1), repeat=5):
        r,q = n-hi,m-hj
        matrix = [[V,r,q,1],[r,r,u,v],[q,u,q,t],[1,v,t,1]]
        diagonal = [V+S+1,2*(n+1),2*(m+1),4]
        slacks = [hi+hj,2+2*hi-u-v,2+2*hj-u-t,2-v-t]
        require(all(not diagonal[a]-sum(matrix[a])-Polynomial(slacks[a]) for a in range(4)),
                'symbolic uniform Gram row-sum slack formula')
        require(min(slacks)>=0, 'all abstract row-sum slacks nonnegative')
        require((max(slacks)==0)==(hi==hj==0 and u==v==t==1),
                'only untouched aligned configurations have zero slack')
        patterns += 1

    norms = []
    for ell in range(4):
        transform = []
        for i in range(4):
            row = [1,0,0,0]
            if ell:
                row[ell] += 1
            if i:
                row[i] -= 1
            transform.append(row)
        recover = [[int(i==ell) for i in range(4)], [1,-1,0,0], [1,0,-1,0], [1,0,0,-1]]
        require(all(sum(transform[a][q]*recover[q][b] for q in range(4))==int(a==b)
                    for a in range(4) for b in range(4)), 'exact anchored-star coordinate inverse')
        norms.append(sum(value*value for row in transform for value in row))
    require(norms==[7,9,9,9], 'anchored-star squared Frobenius norms')
    return {
        'scope': 'symbolic identities and abstract PSD proof patterns; ordinary proof, not Lean verification',
        'parameter_domain': 'm,n>=3; 0<=k<min(m,n)',
        'epsilon_interval': '0<=epsilon<=1/(9*max(m+n+2*k-1,2*m,2*n))',
        'symbolic_identities': identities,
        'abstract_incidence_slack_patterns': patterns,
        'anchor_squared_Frobenius_norms': norms,
        'concrete_grid_instances': 0,
    }


def matching_height_lift():
    """Exact constants and regressions for the ordinary all-height theorem."""
    def tail(p, height):
        u = sum((Fraction(1, p**t) for t in range(1, height)), Fraction(0))
        v = sum((Fraction(2*t-1, p**t) for t in range(1, height)), Fraction(0))
        return u, 4*u+v


    def bound(m, n, k, epsilon, uq, ur, wq, wr, G, M):
        V, H = m*n-k, k*(m+n-k-1)
        D = V+H*epsilon
        c = 1/D
        atom = c*(1+epsilon) if k else c
        row, col = c*(n+k*epsilon), c*(m+k*epsilon)
        F = 1+c*(3*(m+n+3)+6*k*epsilon)
        E = (row+3*atom)*wq+(col+3*atom)*wr+atom*wq*wr
        lam = M*((row+atom)*uq+(col+atom)*ur+atom*uq*ur)
        require(lam < 1, "positive supported mass")
        return {"F": F, "E": E, "lambda": lam,
                "square": (F+E)*G, "conditioned": ((F+E)*G-lam)/(1-lam)}


    q, r, m, n, k = 11, 13, 10, 12, 1
    epsilon = Fraction(1, 216)
    G, M = Fraction(1131, 86), Fraction(271, 86)
    uq, ur = Fraction(1, 10), Fraction(1, 12)
    wq, wr = Fraction(13, 25), Fraction(31, 72)
    require(wq == 4*uq+Fraction(12, 100), "q infinite pair sum")
    require(wr == 4*ur+Fraction(14, 144), "r infinite pair sum")
    uniform = bound(m,n,k,Fraction(0),uq,ur,wq,wr,G,M)
    perturbed = bound(m,n,k,epsilon,uq,ur,wq,wr,G,M)
    require(perturbed["conditioned"] < uniform["conditioned"], "infinite-tail gain")

    V, H = Fraction(119), Fraction(20)
    Lmax = 13*uq+11*ur+uq*ur
    Nmax = V+75+15*wq+13*wr+wq*wr
    drop_min = 786-176*wq-216*wr-99*wq*wr
    charge_slope_max = Fraction(3,2)
    corners = [-22*x+18*y+99*x*y for x in (Fraction(0), uq) for y in (Fraction(0),ur)]
    require(max(corners) == charge_slope_max, "bilinear maximum")
    require(Lmax == Fraction(89,40), "largest unscaled high charge")
    margin40 = drop_min*(V-40*Lmax)-Nmax*40*charge_slope_max
    require(margin40 > 0, "uniform derivative margin for all M <= 40")
    denominator40 = V+H*epsilon-40*(Lmax+epsilon*(2*(uq+ur)+uq*ur))
    require(denominator40 > 0, "all-height positive denominator for M <= 40")

    checked = 0
    for hq in range(1, 9):
        for hr in range(1, 9):
            au, aw = tail(q,hq)
            bu, bw = tail(r,hr)
            require(0 <= au <= uq and 0 <= bu <= ur, "tail mass range")
            require(0 <= aw <= wq and 0 <= bw <= wr, "pair sum range")
            pair_q = sum((Fraction(1, q**(max(i,j)-1))
                          for i in range(hq+1) for j in range(hq+1)
                          if max(i,j) >= 1), Fraction(0))
            require(pair_q == 3+aw, "ordered exponent-pair count")
            a = bound(m,n,k,Fraction(0),au,bu,aw,bw,G,M)
            b = bound(m,n,k,epsilon,au,bu,aw,bw,G,M)
            require(b["conditioned"] < a["conditioned"], "finite-height gain")
            N0=V+75+15*aw+13*bw+aw*bw
            N1=H+6+4*(aw+bw)+aw*bw
            L0=13*au+11*bu+au*bu
            L1=2*(au+bu)+au*bu
            delta=(G*N0-M*L0)*(H-M*L1)-(G*N1-M*L1)*(V-M*L0)
            exact_gain=epsilon*delta/((V-M*L0)*(V+epsilon*H-M*(L0+epsilon*L1)))
            require(exact_gain == a["conditioned"]-b["conditioned"], "gain identity")
            require(delta > 0, "derivative certificate")
            checked += 1

    certificate = {
        "scope": "ordinary symbolic transfer with exact rational regressions; not Lean",
        "parameters": {"q":q,"r":r,"m":m,"n":n,"k":k,"epsilon":str(epsilon),"G":str(G),"M":str(M)},
        "infinite_tail_uniform": {x:str(y) for x,y in uniform.items()},
        "infinite_tail_perturbed": {x:str(y) for x,y in perturbed.items()},
        "strict_gain": str(uniform["conditioned"]-perturbed["conditioned"]),
        "all_height_proof_constants": {"Lmax":str(Lmax),"Nmax":str(Nmax),"drop_min":str(drop_min),"charge_slope_max":str(charge_slope_max),"derivative_margin_at_M40":str(margin40),"denominator_at_M40":str(denominator40)},
        "finite_height_pairs_checked": checked,
    }
    return certificate


def matching_height_tail17(old_result, lift_result):
    """Fixed tail17 schedule, using the verified comparator and actual square."""
    import hashlib
    from runpy import run_path
    arithmetic=run_path(str((Path(__file__).resolve().parents[1] / 'verify_star_block_obstruction.py')))
    continuation=run_path(str((Path(__file__).resolve().parents[1] / 'verify_finite_continuation.py')))
    SCALE=10**18
    runs=((17,4),(23,6),(31,8),(47,12),(61,16),(67,18),(89,24),(127,32),
          (131,36),(137,40),(191,48),(251,64),(271,72),(397,96),(523,128),
          (577,144),(587,160),(857,192),(859,216),(863,240),(1129,256),
          (1289,288),(1297,320),(1693,384))
    ps=list(continuation['segmented_primes'](0,runs[-1][0]))
    choices=[]
    previous=16
    for end,t in runs:
        require(end in ps and previous<end,'schedule endpoints are increasing primes')
        choices.extend((q,t) for q in ps if previous<q<=end)
        previous=end
    def up_fraction(x):
        return arithmetic['stoploss_ceiling'](SCALE*x.numerator,x.denominator)
    ceil_ratio=arithmetic['stoploss_ceiling']
    require([q for q,t in choices]==[q for q in ps if q>=17], 'consecutive full tail primes')
    require(all(isinstance(t,int) and 1<t<=q-2 for q,t in choices), 'normalized kernel domains')
    cap=max(t for q,t in choices)
    atoms={1:Fraction(581,6966),2:Fraction(3031,6966),3:Fraction(146,1053),4:Fraction(425,2106),5:Fraction(10,1443),6:Fraction(45,481),8:Fraction(1,37),12:Fraction(1,74)}
    require(atoms=={int(k):Fraction(v) for k,v in old_result['auxiliary_atoms'].items()},
            'directly reuse the verified old315 comparator')
    require(sum(atoms.values())==1,'old315 comparator probability')
    mean=sum(d*v for d,v in atoms.items())
    require(mean==Fraction(271,86),'old315 comparator mean')
    exact=[Fraction(0)]*(cap+1)
    for d,v in atoms.items():exact[d]=v
    for p,c in ((11,Fraction(11,10)),(13,Fraction(13,12))):
        law=[Fraction(0),1-c/p]+[c*(p-1)/p**f for f in range(2,cap+1)]
        new=[Fraction(0)]*(cap+1)
        for f in range(1,cap+1):
            for d in range(1,cap//f+1):
                new[f*d]+=law[f]*exact[d]
        exact=new
        mean*=1+c/(p-1)
    bad=Fraction(lift_result['infinite_tail_perturbed']['lambda'])
    head_second=Fraction(lift_result['infinite_tail_perturbed']['conditioned'])
    amax=(1+Fraction(1,216))/(119+20*Fraction(1,216))
    require((bad,amax,head_second)==(Fraction(5213769,88490560),Fraction(217,25724),Fraction(6074954672,249830373)),
            'same actual law supplies reference density and separate square bound')
    ell=(1-bad)/(120*amax)
    require(ell==Fraction(83276791,89577600), 'reference density fraction')
    require(1-exact[1]-exact[2]<=ell<=1-exact[1], 'upper quantile threshold two')
    mass2=(ell-1+exact[1]+exact[2])/ell
    mean=2+(mean-2+exact[1])/ell
    w=[up_fraction(v/ell if d>2 else mass2 if d==2 else Fraction(0)) for d,v in enumerate(exact)]
    mean_scaled=up_fraction(mean);second=up_fraction(head_second)
    charge=0;rows=[]
    for q,t in choices:
        s=q-1-t;c=Fraction(q-1,s)
        require(0<c<=q,'conditional geometric law probability')
        numerator=mean_scaled-t*SCALE+sum((t-d)*w[d] for d in range(1,t))
        require(numerator>=0,'nonnegative hinge upper')
        step=ceil_ratio(numerator,s);charge+=step
        require(charge<SCALE,'survival at every prefix')
        w=arithmetic['stoploss_product_update'](w,arithmetic['stoploss_atom_bounds'](q,c,cap,SCALE),SCALE)
        a=1+c/(q-1);b=1+c*Fraction(3*q-1,(q-1)**2)
        mean_scaled=ceil_ratio(mean_scaled*a.numerator,a.denominator)
        second=ceil_ratio(second*b.numerator,b.denominator)
        rows.append({'prime':q,'threshold':t,'s':s,'delta':str(Fraction(t-1,q-2)),
                     'charge_scaled_upper':step,'cumulative_scaled_upper':charge})
    gamma=1+Fraction(second-SCALE,SCALE-charge)
    stop=continuation['stopping_threshold'](len(ps))
    require(gamma<4856<4868<stop,'strict rational stopping chain')
    result={'scope':'Exact directed arithmetic; comparator proof and BBMST continuation are separate ordinary mathematical inputs.',
            'scale':SCALE,'retained_product_states':cap,'first_tail_prime':17,
            'last_prime':choices[-1][0],'global_prime_index':len(ps),'head_density_fraction':str(ell),
            'reference_mass_at_one':str(exact[1]),'reference_mass_at_two':str(exact[2]),
            'reference_mean':str(Fraction(271,86)*Fraction(111,100)*Fraction(157,144)),
            'head_quantile_mass_at_two':str(mass2),'head_comparator_mean':str(mean),
            'head_actual_second_upper':str(head_second),
            'mean_upper':str(Fraction(mean_scaled,SCALE)), 'second_moment_upper':str(Fraction(second,SCALE)),
            'total_charge_upper':str(Fraction(charge,SCALE)), 'survival_lower':str(Fraction(SCALE-charge,SCALE)),
            'Gamma_upper':str(gamma),'stopping_lower':str(stop),'stopping_margin':str(stop-gamma),
            'steps':rows,'final_low_state_digest':hashlib.sha256(json.dumps(w,separators=(',',':')).encode()).hexdigest()}
    result['threshold_runs']=[{'last_prime':q,'threshold':t} for q,t in runs]
    return result


def arbitrary_hole_degree_symbolic():
    """Symbolic algebra for the ordinary arbitrary-hole Gram proof."""
    class P(dict):
        def __init__(self,x=0):
            super().__init__(x if isinstance(x,dict) else ({():x} if x else {}))
        def __add__(self,other):
            answer=P(self)
            for term,value in P(other).items():
                answer[term]=answer.get(term,0)+value
                if not answer[term]: del answer[term]
            return answer
        __radd__=__add__
        def __neg__(self): return P({term:-value for term,value in self.items()})
        def __sub__(self,other): return self+-P(other)
        def __rsub__(self,other): return P(other)+-self
        def __mul__(self,other):
            answer=P()
            for term,value in self.items():
                for term2,value2 in P(other).items():
                    product=tuple(sorted(term+term2))
                    answer[product]=answer.get(product,0)+value*value2
            return P({term:value for term,value in answer.items() if value})
        __rmul__=__mul__
        def __pow__(self,n):
            answer=P(1)
            for _ in range(n): answer=answer*self
            return answer


    def variable(name): return P({(name,):1})


    m,n,k,e,t,d,u,x,y,a,b,s=[variable(v) for v in 'm n k epsilon t d u x y a b s'.split()]
    identities=[]
    certificates=[]
    def identity(name,left,right):
        if left-right: raise RuntimeError(name)
        identities.append(name)
    def nonnegative(name,poly):
        if not poly or any(value<0 for value in poly.values()):
            raise RuntimeError(name)
        certificates.append({'name':name,'terms':[
            {'monomial':'*'.join(term) or '1','coefficient':value}
            for term,value in sorted(poly.items())]})

    S=m+n
    V=m*n-k
    D=V+e*k*(S-k-1)
    H=k*S-(k*k+k-2*t)
    identity('degree-square disjoint-pair normalization',H,k*(S-k-1)+2*t)
    identity('common diagonal sum numerator',
             S+1+2*k*e+2*(n+1+k*e)+2*(m+1+k*e)+4,
             3*(S+3+2*k*e))
    B=m*m+n*n+(2-k)*S-k-3
    identity('strict gain numerator',
             3*(S+3)*D-3*(S+3+2*k*e)*V,
             3*k*e*B)
    Dnext=m*n-(k+1)+e*(k+1)*(S-(k+1)-1)
    identity('hole-count denominator difference',D-Dnext,1-e*(S-2*k-2))
    identity('perturbation row zero bound',
             2*k+k*(n-1)+k*(m-1)+k,k*(S+1))
    identity('row derivative with excess neighboring degree',
             d*(n-d)+k-(d+u),k+d*(n-d-1)-u)
    identity('row-cap residual',
             n+k*e-(n-d+e*(k+d*(n-d-1)-u)),
             d*(1-e*(n-d-1))+e*u)
    identity('filled-row and filled-column center remainder',
             (3+x)*a+(3+y)*b-2*(a+b),
             (1+x)*a+(1+y)*b)
    identity('large-row-derivative norm remainder',
             2*k*(n-1)-2*(k*(n-1)-s),2*s)
    nonnegative('small-row-derivative norm remainder, n=3+x',
                2*k*((3+x)-1)-4*k)
    nonnegative('restored-edge anchor surplus',x*a+y*b)
    nonnegative('large-row-derivative norm remainder',2*s)
    identity('10x12 gain polynomial',
             10*10+12*12+(2-k)*(10+12)-k-3,285-23*k)
    identity('10x12 gain at k=12-x',285-23*(12-x),9+23*x)
    nonnegative('10x12 gain for k<=12',9+23*x)
    result={'status':'PASS','scope':'symbolic algebra; semantic proof remains in note',
            'identities':identities,'nonnegative_coefficient_certificates':certificates}
    return result


def varying_hole_head(old_result, square_result):
    """Correlated hole-count input bounds for the same actual law."""
    X={1:Fraction(581,6966),2:Fraction(3031,6966),3:Fraction(146,1053),4:Fraction(425,2106),
       5:Fraction(10,1443),6:Fraction(45,481),8:Fraction(1,37),12:Fraction(1,74)}
    M,G=Fraction(271,86),Fraction(1131,86)
    require(X=={int(k):Fraction(v) for k,v in old_result['auxiliary_atoms'].items()},'verified old315 comparator')
    require(G==Fraction(square_result['actual_second_moment_upper']),'same old law square bound')
    require(sum(X.values())==1,'X normalization')
    require(sum(x*p for x,p in X.items())==M,'X mean')
    uq,ur,wq,wr=Fraction(1,10),Fraction(1,12),Fraction(13,25),Fraction(31,72)
    Nmean=Fraction(111,100)*Fraction(157,144)


    def top(alpha):
        out={x:Fraction(0) for x in X}
        rest=alpha
        for x in sorted(X,reverse=True):
            out[x]=min(rest,X[x])
            rest-=out[x]
        require(rest==0,'upper quantile mass')
        return out


    def parameters(j,eps):
        D=120-j+eps*j*(21-j)
        R=(12+j*eps)/D
        C=(10+j*eps)/D
        a=(1+j*eps)/D
        F=1+(75+6*j*eps)/D
        T=(R+a)*uq+(C+a)*ur+a*uq*ur
        E=(R+3*a)*wq+(C+3*a)*wr+a*wq*wr
        return {'D':D,'R':R,'C':C,'a':a,'F':F,'T':T,'chi':F+E,'d':120*a,
                'lambda0':1+(23+2*j*eps)/D,
                'lambda1':2*(13+j*eps)/D,
                'lambda2':2*(11+j*eps)/D,'lambda3':4/D}


    def reference_low(raw_old,cap=24):
        weights=[Fraction(0)]*(cap+1)
        for x,v in raw_old.items():
            weights[x]=v
        for p in (11,13):
            new=[v*Fraction(p-2,p-1) for v in weights]
            for f in range(2,cap+1):
                prob=Fraction(1,p**(f-1))
                for x in range(1,cap//f+1):
                    new[f*x]+=weights[x]*prob
            weights=new
        return weights


    def quantify(raw_old,survival):
        mass=sum(raw_old.values())
        mean=Nmean*sum(x*v for x,v in raw_old.items())
        low=reference_low(raw_old)
        remove=mass-survival
        below=Fraction(0)
        cut=None
        for j in range(1,len(low)):
            if below+low[j]>=remove:
                cut=j
                break
            below+=low[j]
        require(cut is not None,'quantile located in retained range')
        correction=sum((cut-j)*low[j] for j in range(1,cut))
        final_mean=cut+(mean-cut*mass+correction)/survival
        cut_mass=(survival-mass+sum(low[:cut+1]))/survival
        def hinge(t):
            if t<cut:
                return final_mean-t
            return (mean-t*mass+sum((t-j)*low[j] for j in range(1,t+1)))/survival
        return {'mass':mass,'ell':survival/mass,'raw_mean':mean,'cut':cut,
                'cut_mass':cut_mass,'mean':final_mean,'raw_mass1':low[1],
                'raw_mass2':low[2]},[hinge(t) for t in range(25)]


    rows=[]
    for K in range(1,13):
        eps=Fraction(1,207*K)
        vals=[parameters(j,eps) for j in range(K+1)]
        zero,last=vals[0],vals[-1]
        for field in ('R','C','a','F','T','chi','d','lambda0','lambda1','lambda2','lambda3'):
            seq=[v[field] for v in vals]
            require(all(seq[j]<=seq[j+1] for j in range(K)),field+' monotonic')
            require(all(seq[j+2]-seq[j+1]>=seq[j+1]-seq[j] for j in range(K-1)),field+' convex')
            require(all(seq[j]<=seq[0]+Fraction(j,K)*(seq[K]-seq[0]) for j in range(K+1)),field+' chord')
        alpha=min(Fraction(1),M/K)
        upper=top(alpha)
        Talpha=sum(x*v for x,v in upper.items())
        lam=zero['T']*M+(last['T']-zero['T'])*Talpha
        square=last['chi']*G-(last['chi']-zero['chi'])*(1-alpha)
        final=(square-lam)/(1-lam)
        old_lam=last['T']*M
        old_square=last['chi']*G
        old_final=(old_square-old_lam)/(1-old_lam)
        raw={x:X[x]+(last['d']-1)*upper[x] for x in X}
        profile,hinges=quantify(raw,1-lam)
        old_profile,old_hinges=quantify({x:last['d']*X[x] for x in X},1-old_lam)
        require(lam<1 and final>=1,'positive conditioned law')
        if alpha<1:
            require(lam<old_lam and square<old_square and final<old_final,'strict square and mass improvement')
            require(all(a<b for a,b in zip(hinges,old_hinges)),'strict profile improvement')
        else:
            require(lam==old_lam and square==old_square and profile==old_profile,'unchanged vacuous mean bound')
        rows.append({'K':K,'epsilon':str(eps),'alpha':str(alpha),
           'old_upper_quantile_cut':min(x for x,v in upper.items() if v),
           'old_upper_quantile_raw_mean':str(Talpha),
           'lambda':str(lam),'square_before_conditioning':str(square),'J':str(final),
           'worstK_lambda':str(old_lam),'worstK_J':str(old_final),
           'density_max':str(last['d']),
           'survival_lower':str(1-lam),
           'raw_old_mixture_atoms':{str(x):str(v) for x,v in raw.items()},
           'upper_old_subprobability_atoms':{str(x):str(v) for x,v in upper.items()},
           'profile':{k:str(v) if isinstance(v,Fraction) else v for k,v in profile.items()},
           'worstK_profile_mean':str(old_profile['mean'])})

    result={'scope':'Exact rational head inputs only; no tail schedule; symbolic proof separate',
            'old_mean':str(M),'old_square':str(G),'rows':rows,'hinge_regressions':12*25}
    return result


def arbitrary_holes12_tail17(head):
    """Fixed 414-step schedule for the verified K12 finite comparison measure."""
    import hashlib
    from runpy import run_path
    arithmetic=run_path(str((Path(__file__).resolve().parents[1] / 'verify_star_block_obstruction.py')))
    continuation=run_path(str((Path(__file__).resolve().parents[1] / 'verify_finite_continuation.py')))
    SCALE=10**18
    runs=((17, 4), (23, 6), (31, 8), (43, 12), (61, 16), (89, 24), (113, 32), (127, 36), (179, 48), (233, 64), (251, 72), (257, 80), (359, 96), (367, 108), (467, 128), (523, 144), (761, 192), (769, 216), (997, 256), (1117, 288), (1129, 320), (1669, 384), (1697, 432), (1699, 480), (2239, 512), (2551, 576), (2579, 640), (2903, 768))
    ps=list(continuation['segmented_primes'](0,runs[-1][0]))
    choices=[]
    previous=16
    for end,t in runs:
        require(end in ps and previous<end,'schedule endpoints are increasing primes')
        choices.extend((q,t) for q in ps if previous<q<=end)
        previous=end
    def up_fraction(x):
        return arithmetic['stoploss_ceiling'](SCALE*x.numerator,x.denominator)
    ceil_ratio=arithmetic['stoploss_ceiling']
    require([q for q,t in choices]==[q for q in ps if q>=17], 'consecutive full tail primes')
    require(all(isinstance(t,int) and 1<t<=q-2 for q,t in choices), 'normalized kernel domains')
    cap=max(t for q,t in choices)
    require(head['K']==12,'all twelve old cross-cofactor labels')
    atoms={int(a):Fraction(v) for a,v in head['raw_old_mixture_atoms'].items()}
    rawmass=sum(atoms.values())
    require(rawmass==Fraction(head['profile']['mass']),'raw old measure total mass')
    mean=sum(d*v for d,v in atoms.items())
    exact=[Fraction(0)]*(cap+1)
    for d,v in atoms.items():exact[d]=v
    for p,c in ((11,Fraction(11,10)),(13,Fraction(13,12))):
        law=[Fraction(0),1-c/p]+[c*(p-1)/p**f for f in range(2,cap+1)]
        new=[Fraction(0)]*(cap+1)
        for f in range(1,cap+1):
            for d in range(1,cap//f+1):
                new[f*d]+=law[f]*exact[d]
        exact=new
        mean*=1+c/(p-1)
    ell=Fraction(head['survival_lower'])
    head_second=Fraction(head['J'])
    require(rawmass-exact[1]-exact[2]<=ell<=rawmass-exact[1], 'upper surviving-mass quantile threshold two')
    mass2=(ell-rawmass+exact[1]+exact[2])/ell
    refmean=mean
    mean=2+(mean-2*rawmass+exact[1])/ell
    require(mean==Fraction(head['profile']['mean']),'verified full comparator mean')
    w=[up_fraction(v/ell if d>2 else mass2 if d==2 else Fraction(0)) for d,v in enumerate(exact)]
    mean_scaled=up_fraction(mean);second=up_fraction(head_second)
    charge=0;rows=[]
    for q,t in choices:
        s=q-1-t;c=Fraction(q-1,s)
        require(0<c<=q,'conditional geometric law probability')
        numerator=mean_scaled-t*SCALE+sum((t-d)*w[d] for d in range(1,t))
        require(numerator>=0,'nonnegative hinge upper')
        step=ceil_ratio(numerator,s);charge+=step
        require(charge<SCALE,'survival at every prefix')
        w=arithmetic['stoploss_product_update'](w,arithmetic['stoploss_atom_bounds'](q,c,cap,SCALE),SCALE)
        a=1+c/(q-1);b=1+c*Fraction(3*q-1,(q-1)**2)
        mean_scaled=ceil_ratio(mean_scaled*a.numerator,a.denominator)
        second=ceil_ratio(second*b.numerator,b.denominator)
        rows.append({'prime':q,'threshold':t,'s':s,'delta':str(Fraction(t-1,q-2)),
                     'charge_scaled_upper':step,'cumulative_scaled_upper':charge})
    gamma=1+Fraction(second-SCALE,SCALE-charge)
    stop=continuation['stopping_threshold'](len(ps))
    require(gamma<9826<9833<stop,'strict rational stopping chain')
    result={'scope':'Exact directed arithmetic; comparator proof and BBMST continuation are separate ordinary mathematical inputs.',
            'scale':SCALE,'retained_product_states':cap,'first_tail_prime':17,
            'last_prime':choices[-1][0],'global_prime_index':len(ps),'head_survival_lower':str(ell),'head_raw_comparator_mass':str(rawmass),
            'reference_mass_at_one':str(exact[1]),'reference_mass_at_two':str(exact[2]),
            'reference_mean':str(refmean),
            'head_quantile_mass_at_two':str(mass2),'head_comparator_mean':str(mean),
            'head_actual_second_upper':str(head_second),
            'mean_upper':str(Fraction(mean_scaled,SCALE)), 'second_moment_upper':str(Fraction(second,SCALE)),
            'total_charge_upper':str(Fraction(charge,SCALE)), 'survival_lower':str(Fraction(SCALE-charge,SCALE)),
            'Gamma_upper':str(gamma),'stopping_lower':str(stop),'stopping_margin':str(stop-gamma),
            'steps':rows,'final_low_state_digest':hashlib.sha256(json.dumps(w,separators=(',',':')).encode()).hexdigest()}
    result['threshold_runs']=[{'last_prime':q,'threshold':t} for q,t in runs]
    return result
