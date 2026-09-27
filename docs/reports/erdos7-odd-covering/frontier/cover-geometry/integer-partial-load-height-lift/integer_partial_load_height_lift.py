#!/usr/bin/env python3
"""Exact controls for integer mixed-load height lifting with a fixed cofactor.

The companion report proves the unbounded integer inequalities. These controls
check their arithmetic and the quantitative certificates, without Lean claims.
"""

from fractions import Fraction as F
from itertools import product
import json

def require(ok,msg):
    if not ok: raise ValueError(msg)

def g(d,z): return max(1,d*d*z*z)

def quantities(C,u5,v5,u7,v7):
    q=C-1
    M=((C,3*q/8,C/2,6*q/35),
       (3*q/8,q/8,17*q/96,2*q/35),
       (C/2,17*q/96,C/4,3*q/35),
       (6*q/35,2*q/35,3*q/35,q/35))
    W=((F(1),u5,u7,u5*u7),
       (u5,v5,u5*u7,v5*u7),
       (u7,u5*u7,v7,u5*v7),
       (u5*u7,v5*u7,u5*v7,v5*v7))
    A=sum(W[i][j]*M[i][j] for i in range(4) for j in range(4))
    lam=u5*q/8+u7*(C+8)/12+u5*u7*q/35
    return A,lam

def check_pointwise():
    n=0
    for b in range(33):
        require(b<=F(g(3,b)-1,8),'first moment type5')
        require(b<=F(g(2,b)+8,12),'integer face type7')
        require(b<=F(g(6,b)-1,35),'first moment type57 without indicator assumption')
    for a,b in product(range(1,33),range(33)):
        require(24*a*b<=4*a*a+5*g(3,b)-9,'cross full/5')
        n+=1
    for a,b in product(range(33),repeat=2):
        require(16*a*b<=g(3,a)+g(3,b)-2,'two independent type5 loads')
        n+=1
    for a,b in product(range(33),repeat=2):
        delta=9*g(3,a)+8*g(2,b)-17-96*a*b
        require(delta>=0,'joint cross-axis dual')
        if a and b:
            require(delta==32*(F(b)-F(3*a,2))**2+9*a*a-17,'universal cross-axis square identity')
        n+=1
    for d,D in product(range(1,9),range(2,9)):
        for a,b in product(range(25),repeat=2):
            delta=(D*D-1)*g(d,a)+(D*D+1)*g(D,b)-2*D*D-2*d*D*(D*D-1)*a*b
            require(delta>=0,'general integer joint-moment dual')
            if a and b:
                require(delta==(D*D-1)*(d*a-D*b)**2+2*D*D*(b*b-1),'general nonnegative-square identity')
            elif a==0:
                require(delta==(D*D+1)*(g(D,b)-1),'zero first argument')
            else:
                require(delta==(D*D-1)*(g(d,a)-1),'zero second argument')
            n+=1
    return n

def check_sharp_relaxation(C):
    q=C-1
    law={(0,0):1-q/8,(1,1):7*q/96,(1,2):5*q/96}
    require(all(w>=0 for w in law.values()) and sum(law.values())==1,'one joint law')
    require(sum(w*g(3,a) for (a,b),w in law.items())==C,'type5 moment')
    require(sum(w*g(2,b) for (a,b),w in law.items())==C,'type7 moment')
    require(sum(w*a*b for (a,b),w in law.items())==17*q/96,'joint price equality')

def joint_four_moment_boundary_controls():
    C = F(46, 9)
    states = ((1, 0, 1, 0), (3, 1, 1, 0), (3, 1, 1, 1), (3, 1, 2, 1))
    masses = (F(35, 72), F(111, 280), F(47, 1890), F(5, 54))
    law = tuple(zip(states, masses))
    require(sum(masses) == 1 and all(w > 0 for w in masses), "one joint four-atom probability")
    require(all(x[0] >= 1 and all(type(z) is int and z >= 0 for z in x) for x in states),
            "unbounded-integer model: witness uses admissible integer values")
    moments = tuple(sum(w*g(d, x[i]) for x, w in law) for i, d in enumerate((1, 3, 2, 6)))
    require(moments == (C, C, C, C), "all four moment budgets on the same law")
    first = tuple(sum(w*x[i] for x, w in law) for i in (1, 2, 3))
    require(first == ((C-1)/8, (C+8)/12, (C-1)/35), "all first-moment faces attained together")
    q = C-1
    caps = ((C, 3*q/8, C/2, 6*q/35),
            (3*q/8, q/8, 17*q/96, 2*q/35),
            (C/2, 17*q/96, C/4, 3*q/35),
            (6*q/35, 2*q/35, 3*q/35, q/35))
    gram = tuple(tuple(sum(w*x[i]*x[j] for x, w in law) for j in range(4)) for i in range(4))
    require(all(gram[i][j] <= caps[i][j] for i in range(4) for j in range(4)),
            "the same joint law meets the complete retained matrix")

    def evaluate(joint_law, sums):
        u5, v5, u7, v7 = sums
        W = ((F(1), u5, u7, u5*u7),
             (u5, v5, u5*u7, v5*u7),
             (u7, u5*u7, v7, u5*v7),
             (u5*u7, v5*u7, u5*v7, v5*v7))
        phi = sum(w*sum(W[i][j]*x[i]*x[j] for i in range(4) for j in range(4))
                  for x, w in joint_law)
        deletion = sum(w*(u5*x[1]+u7*x[2]+u5*u7*x[3]) for x, w in joint_law)
        return phi, deletion

    infinity = (F(1, 4), F(3, 8), F(1, 6), F(2, 9))
    phi, deletion = evaluate(law, infinity)
    require(phi == F(3948953, 544320) and deletion == F(28619, 90720), "exact joint all-height values")
    require(phi+8*deletion == F(1064533, 108864)
            and phi+8*deletion-9 == F(84757, 108864) > 0, "joint target obstruction")
    statewise_d = tuple(infinity[0]*x[1]+infinity[2]*x[2]+infinity[0]*infinity[2]*x[3]
                        for x in states)
    require(max(statewise_d) == F(5, 8) and 0 <= deletion < 1,
            "no truncation or denominator defect")
    finite = (sum((F(1, 5**t) for t in (1, 2)), F()),
              sum((F(2*t-1, 5**t) for t in (1, 2)), F()),
              sum((F(1, 7**t) for t in (1, 2)), F()),
              sum((F(2*t-1, 7**t) for t in (1, 2)), F()))
    finite_phi, finite_d = evaluate(law, finite)
    require(finite_phi+8*finite_d == F(4443137, 463050)
            and finite_phi+8*finite_d-9 == F(275687, 463050) > 0,
            "finite n5=n7=2, heights K5=4,K7=3")
    # The following parameter formulas are affine; identities at 0 and1 fix their coefficients.
    for c in (F(0), F(1), F(4), F(128, 23), C):
        ws = ((9-c)/8, 27*(c-1)/280, (128-23*c)/420, (c-4)/12)
        ll = tuple(zip(states, ws))
        require(sum(ws) == 1, "parametric normalization identity")
        mm = tuple(sum(w*g(d, x[i]) for x, w in ll) for i, d in enumerate((1, 3, 2, 6)))
        require(mm == (c, c, c, c), "parametric moment identities")
        pp, dd = evaluate(ll, infinity)
        require(pp+8*dd == (113105*c+13315)/60480, "parametric joint objective identity")
        if 4 <= c <= F(128, 23): require(all(w >= 0 for w in ws), "feasible parameter interval")
    threshold = F(106201, 22621)
    require((113105*threshold+13315)/60480 == 9 and 4 < threshold < C,
            "necessary moment-model seed threshold")
    return {"scope": "Four-budget joint-moment relaxation only; no arithmetic or excluded-union realization asserted",
            "C": str(C), "atoms": [{"loads": x, "mass": str(w)} for x, w in law],
            "four_g_moments": list(map(str, moments)),
            "joint_gram": [[str(z) for z in row] for row in gram],
            "all_height": {"E_Phi": str(phi), "E_D": str(deletion),
                           "target": str(phi+8*deletion), "target_minus_nine": str(phi+8*deletion-9)},
            "finite": {"n5": 2, "n7": 2, "K5": 4, "K7": 3,
                       "carrier": "5^4*7^3*M", "E_Phi": str(finite_phi), "E_D": str(finite_d),
                       "target": str(finite_phi+8*finite_d), "target_minus_nine": str(finite_phi+8*finite_d-9)},
            "statewise_D": list(map(str, statewise_d)),
            "parametric_C_interval": ["4", "128/23"], "necessary_moment_threshold": str(threshold)}


def main():
    count=check_pointwise()
    finite=(F(1,5),F(1,5),F(1,7),F(1,7))
    infinite=(F(1,4),F(3,8),F(1,6),F(2,9))
    # Every expression is affine in C; values at 0 and 1 check coefficient identities.
    for C in (F(0),F(1)):
        A,l=quantities(C,*finite)
        require(A==(81289*C-11989)/58800 and l==(1109*C+2041)/29400,'finite affine identity')
        A,l=quantities(C,*infinite)
        require(A==(8667*C-1627)/5760 and l==(467*C+793)/10080,'all-height affine identity')
    out=[]
    for C in map(F,('4','68/15','149/30','5','46/9','167/33','9')):
        check_sharp_relaxation(C)
        for name,sums in (('175M_to_6125M',finite),('all_finite_5_7_heights_fixed_M',infinite)):
            A,lam=quantities(C,*sums)
            require(A>=1 and 0<=lam<1,'positive denominator and monotonicity')
            J=(A-lam)/(1-lam)
            out.append({'C':C,'scope':name,'A':A,'lambda':lam,'bound':J,'nine_minus_bound':9-J})
            if C==F(46,9) and name=='175M_to_6125M':
                require(J==F(3492627,390434) and 9-J==F(21279,390434)>0,'finite improvement')
            if C==F(68,15) and name=='all_finite_5_7_heights_fixed_M':
                require(J==F(3780053,430196) and 9-J==F(91711,430196)>0,'all-height improvement')
    for sums,threshold in ((finite,F(169511,33011)),(infinite,F(348893,75613))):
        A,l=quantities(threshold,*sums)
        require(A+8*l==9,'exact affine threshold')
    C=F(68,15)
    _,newlam=quantities(C,*infinite)
    require(F(319,216)*C+8*newlam-9==F(263,56700)>0,'first-moment-only correction remains insufficient')
    # Verify the aggregate coefficient identity against all excess pairs for two finite sizes.
    for n5,n7 in ((1,1),(3,2)):
        u5=sum((F(1,5**t) for t in range(1,n5+1)),F())
        v5=sum((F(2*t-1,5**t) for t in range(1,n5+1)),F())
        u7=sum((F(1,7**t) for t in range(1,n7+1)),F())
        v7=sum((F(2*t-1,7**t) for t in range(1,n7+1)),F())
        W=((F(1),u5,u7,u5*u7),(u5,v5,u5*u7,v5*u7),
           (u7,u5*u7,v7,u5*v7),(u5*u7,v5*u7,u5*v7,v5*v7))
        actual=[[F() for j in range(4)] for i in range(4)]
        vectors=list(product(range(n5+1),range(n7+1)))
        for t,s in product(vectors,repeat=2):
            i=int(t[0]>0)+2*int(t[1]>0);j=int(s[0]>0)+2*int(s[1]>0)
            actual[i][j]+=F(1,5**max(t[0],s[0])*7**max(t[1],s[1]))
        require(tuple(map(tuple,actual))==W,'excess pair aggregation')
    print(json.dumps({'scope':'ordinary proof for arbitrary fixed cofactor M coprime to 35; exact integer controls; not Lean; actual-family full Gamma_175M seed remains a hypothesis',
        'pointwise_cases':count,'results':out,
        'joint_four_moment_boundary':joint_four_moment_boundary_controls(),
        'finite_C_threshold':F(169511,33011),'all_height_C_threshold':F(348893,75613)},default=str,indent=2))

if __name__=='__main__': main()
