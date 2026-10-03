#!/usr/bin/env python3
"""Exact finite diagnostics for the Monster completion / cubic-response note.

Only integer/Fraction calculations. This does not construct the Monster, a VOA,
a conformal net, or its anomaly class. Small permutation models are explicitly
labelled as toys; published coefficients are checked for internal consistency.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
from math import comb, factorial
import json


def require(test, label):
    if not test:
        raise AssertionError(label)


def mul(a, b, degree):
    out = [0] * (degree + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j <= degree:
                out[i+j] += x*y
    return out


def power(a, k, degree):
    out = [1] + [0]*degree
    for _ in range(k):
        out = mul(out, a, degree)
    return out


def oscillators(d, degree, odd=False, insertion=False):
    out = [1]+[0]*degree
    for n in range(1, degree+1):
        if odd and n % 2 == 0:
            continue
        term = [0]*(degree+1)
        for k in range(degree//n+1):
            term[k*n] = comb(d+k-1, k) * ((-1)**k if insertion else 1)
        out = mul(out, term, degree)
    return out


def delta(degree):
    out = [1]+[0]*degree
    for n in range(1, degree+1):
        term = [0]*(degree+1)
        for k in range(min(24, degree//n)+1):
            term[k*n] = (-1)**k*comb(24,k)
        out = mul(out, term, degree)
    return [0]+out[:-1]


def dot(x,y):
    return sum(a*b for a,b in zip(x,y))


def matmul(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]


def transpose(a):
    return [list(x) for x in zip(*a)]


def add(a,b):
    return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]


def scale(q,a):
    return [[q*x for x in row] for row in a]


def polyadd(a,b,scale_b=1):
    n=max(len(a),len(b))
    return [(a[i] if i<len(a) else 0)+scale_b*(b[i] if i<len(b) else 0) for i in range(n)]


def evaluate(a,x):
    return sum(v*x**i for i,v in enumerate(a))


def run():
    counts=Counter()
    degree=8
    e4=[1]+[240*sum(d**3 for d in range(1,n+1) if n%d==0) for n in range(1,degree+1)]
    jshift=mul(power(e4,3,degree),oscillators(24,degree),degree)
    J={i-1:x for i,x in enumerate(jshift)}
    J[0]-=744
    theta=polyadd(power(e4,3,degree),delta(degree),-720)
    require(theta[:3]==[1,0,196560],"rootless theta initial coefficients")
    leech=mul(theta,oscillators(24,degree),degree)
    inserted=oscillators(24,degree,insertion=True)
    untwisted={i-1:F(leech[i]+inserted[i],2) for i in range(degree+1)}
    half=oscillators(24,2*degree,odd=True)
    twisted={n:4096*half[2*n-1] for n in range(1,degree)}
    for n in range(-1,degree):
        require(untwisted.get(n,0)+twisted.get(n,0)==J[n],("orbifold character",n))
        counts['orbifold_character_coefficients']+=1
    for d,k,expected in [(8,1,248),(16,2,496)]:
        coeff=mul(power(e4,k,degree),oscillators(d,degree),degree)[1]
        require(coeff==expected,("low-central-charge current count",d))
        counts['low_c_current_coefficients']+=1
    require(300+196560//2==98580,"untwisted weight two")
    require(24*2**12==98304,"twisted weight two")
    require(98580+98304==196884,"total weight two")
    counts['orbifold_sector_counts']+=3

    # Direct polynomial elimination of displayed Matsuo v1 equations (3.2),(3.4).
    A=[0,2388,955,70]
    B=[1496,-110,2]
    C=[0,1497768,3507098,1369715,155250,5250]
    D=[1032240,1561868,-23382,-4770,125]
    lhs=polyadd(mul(A,D,7),mul(B,C,7),-1)
    rhs=[-1]+[0]*7
    for factor in ([0,1],[-24,1],[-1,2],[-142,5],[22,5],[44,5],[68,7]):
        rhs=mul(rhs,factor,7)
    require(lhs==rhs,"Matsuo elimination factorization")
    counts['selection_polynomial_identities']+=1
    candidates={}
    for c in (F(1,2),F(24),F(142,5)):
        val=evaluate(A,c)/evaluate(B,c)
        candidates[str(c)]=str(val)
        require(evaluate(A,c)*evaluate(D,c)==evaluate(B,c)*evaluate(C,c),c)
        counts['selection_positive_root_cases']+=1
    require(candidates=={'1/2':'1','24':'196884','142/5':'-164081'},"positive branches")

    # Griess scalar trace and compressed cubic constants, not full tensor tests.
    n=196884; d=n-1
    require(F(-2*(5*24**2-88*n+2*24*n),24*(5*24+22))==4620,"Norton trace constant")
    sigma=F(4620)-F(2,3)
    cubic_norm_squared=d*sigma
    require(cubic_norm_squared==F(2728404614,3),"cubic norm")
    require(F(3,2)*4620**2/900==35574,"finite pulse bias coefficient")
    require(F(8*n,900)==F(43752,25),"normalized trace noise coefficient")
    require(F(4620**2,720)==29645,'even pulse bias prefactor')
    require(F(3*43752,25*2*29645)==F(65628,741125),'even balanced step prefactor')
    counts['response_constant_identities']+=6

    # Eight ordered pulse subwords. Formal real matrix series are evaluated at i*t.
    # Below-cubic terms cancel; the normalized first correction is purely imaginary.
    # Independent exact coefficient convolution, no finite-difference float threshold.
    def trace(a): return sum(a[i][i] for i in range(len(a)))
    for dim in (2,3):
        eye=[[F(i==j) for j in range(dim)] for i in range(dim)]
        for seed in range(1,7):
            matrices=[]
            for offset in range(3):
                matrices.append([[F(((i+j+offset+seed)%5)-2,seed)
                                  + (F(offset+1) if i==j else 0)
                                  for j in range(dim)] for i in range(dim)])
            deg=7
            expansions=[]
            for a in matrices:
                powers=[eye]
                for n0 in range(1,deg+1):
                    powers.append(matmul(powers[-1],a))
                expansions.append([scale(F(1,factorial(n0)),powers[n0])
                                   for n0 in range(deg+1)])
            summed=[F(0)]*(deg+1)
            for mask in range(8):
                series=[eye]+[[[F(0)]*dim for _ in range(dim)] for _ in range(deg)]
                for k0 in range(3):
                    if not (mask>>k0)&1: continue
                    new=[]
                    for n0 in range(deg+1):
                        val=[[F(0)]*dim for _ in range(dim)]
                        for r0 in range(n0+1):
                            val=add(val,matmul(series[r0],expansions[k0][n0-r0]))
                        new.append(val)
                    series=new
                sign=(-1)**(3-mask.bit_count())
                for n0 in range(deg+1): summed[n0]+=sign*trace(series[n0])
            require(summed[:3]==[0,0,0],('pulse cancellation',dim,seed))
            abc=trace(matmul(matmul(matrices[0],matrices[1]),matrices[2]))
            require(summed[3]==abc,('ordered cubic coefficient',dim,seed))
            correction=F(0)
            for k0 in range(3):
                changed=list(matrices)
                changed[k0]=matmul(changed[k0],changed[k0])
                correction+=trace(matmul(matmul(changed[0],changed[1]),changed[2]))/2
            require(summed[4]==correction,('pure-imaginary normalized correction',dim,seed))
            # i^(4-3) is imaginary; i^(5-3) is real. This parity is exact.
            counts['ordered_pulse_series_cases']+=1

    # Derivative Gram for T(x,y,z)=sum x_i y_i z_i on R^d: kappa^2=3.
    for d0 in range(2,6):
        keys=list(product(range(d0), repeat=3))
        deriv=[]
        for i in range(d0):
            for j in range(i+1,d0):
                a=[[F(0)]*d0 for _ in range(d0)]
                a[i][j]=F(1); a[j][i]=F(-1)
                vals=[]
                for p,q,r in keys:
                    vals.append((a[q][p] if q==r else 0)+(a[p][q] if p==r else 0)+(a[p][r] if p==q else 0))
                deriv.append(vals)
        for i,x in enumerate(deriv):
            for j,y in enumerate(deriv):
                require(dot(x,y)==(6 if i==j else 0),("toy cubic Jacobian",d0,i,j))
                counts['toy_cubic_jacobian_entries']+=1

    # Ancestry marker in the standard S_m representation (not a Monster representation).
    toys=[]
    for m in (3,4,5):
        identity=[[F(i==j) for j in range(m)] for i in range(m)]
        p0=[[identity[i][j]-F(1,m) for j in range(m)] for i in range(m)]
        v=[F(0)]*m; v[0]=F(1); v[1]=F(-1)
        marker=[[v[i]*v[j]/2 for j in range(m)] for i in range(m)]
        z=add(identity,scale(-2,marker))
        total=[[F(0)]*m for _ in range(m)]
        stab=0; count=0
        for p in permutations(range(m)):
            g=[[F(i==p[j]) for j in range(m)] for i in range(m)]
            moved=matmul(matmul(g,marker),transpose(g))
            fixed=(moved==marker)
            commuting=matmul(g,z)==matmul(z,g)
            require(fixed==commuting,("marked centralizer",m,p))
            counts['toy_marker_centralizer_cases']+=1
            total=add(total,moved); stab+=fixed; count+=1
        average=scale(F(1,count),total)
        require(average==scale(F(1,m-1),p0),("toy twirl",m))
        counts['toy_marker_twirl_identities']+=1
        x=[F(1),F(1),F(-2)]+[F(0)]*(m-3)
        minus=[-a for a in x]
        require(dot(x,x)==dot(minus,minus) and sum(a**3 for a in x)==-sum(a**3 for a in minus)!=0,"odd data detects sign")
        counts['deliberate_quadratic_blindness_controls']+=1
        toys.append({'permutation_degree':m,'group_order':count,'marked_stabilizer':stab})

    # Actual finite Frobenius-algebra reconstruction from a metric and symmetric cubic.
    for d0 in (2,3,4):
        def prodB(a,b):
            return [a[0]*b[0]+dot(a[1:],b[1:])/3]+[a[0]*b[i]+b[0]*a[i]+a[i]*b[i] for i in range(1,d0+1)]
        def metric(a,b): return 3*a[0]*b[0]+dot(a[1:],b[1:])
        basis=[[F(i==j) for j in range(d0+1)] for i in range(d0+1)]
        for a,b,c in product(basis,repeat=3):
            require(metric(prodB(a,b),c)==metric(a,prodB(b,c)),"Frobenius identity")
            counts['toy_product_reconstruction_entries']+=1

    # Group-junction pentagon using a rational representative of a cyclic 3-cocycle.
    # This verifies the cocycle equation, not nontriviality in group cohomology.
    for m in range(2,7):
        for a in range(m):
            def phase(x,y,z): return F(a*x*((y+z)//m),m) % 1
            for x,y,z,w in product(range(m),repeat=4):
                defect=phase(y,z,w)+phase(x,(y+z)%m,w)+phase(x,y,z)-phase((x+y)%m,z,w)-phase(x,y,(z+w)%m)
                require(defect%1==0,("cyclic pentagon",m,a,x,y,z,w))
                counts['toy_defect_pentagons']+=1
    return {
        'status':'passed','arithmetic':'integers and fractions.Fraction only',
        'case_counts':dict(sorted(counts.items())),
        'orbifold_weight_two':{'untwisted':98580,'twisted':98304,'total':196884,'primary':196883},
        'moonshine_character_q_minus1_to_q5':[int(J[k]) for k in range(-1,6)],
        'Matsuo_positive_branches':candidates,
        'Matsuo_v1_note':'The displayed elimination polynomial has negative root -44/5; the prose list differs. Only the positive branches are used.',
        'cubic_norm_squared':str(cubic_norm_squared),
        'unit_label_pulse_linear_bound':'35574*t',
        'unit_label_pulse_even_bound':'29645*sqrt(4620)*t^2',
        'normalized_trace_noise_constant':'43752/25',
        'balanced_step_fifth_power_coefficient':'65628/(741125*sqrt(4620))',
        'balanced_error_exponent':'2/5',
        'Monster_twisted_fraction':str(F(98304,196883)),
        'toy_ancestry_groups':toys,
        'scope':'Finite diagnostics only. No Monster matrices, full Griess multiplication table, VOA, conformal net, anomaly cohomology computation, physical experiment, or Lean verification.'
    }

if __name__=='__main__':
    print(json.dumps(run(),ensure_ascii=False,indent=2))
