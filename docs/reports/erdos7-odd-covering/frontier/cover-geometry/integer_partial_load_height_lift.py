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
        'finite_C_threshold':F(169511,33011),'all_height_C_threshold':F(348893,75613)},default=str,indent=2))

if __name__=='__main__': main()
