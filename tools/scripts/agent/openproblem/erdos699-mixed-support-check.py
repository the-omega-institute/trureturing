#!/usr/bin/env python3
"""Exact self-audit: original-parameter mixed-support exclusion, Erdos 699.

WRITTEN THEOREM. Under an i=3 counterexample, EACH of j,n-j has an odd prime
factor of n-1 and an odd prime factor outside n(n-1). Consequently each
endpoint has at least two distinct odd prime factors not dividing n. If j
has at most two odd prime factors, exceptions can only have n=2^N or3*2^N;
if also3|j, only2^N remains. No initial n/prime/exponent bound is assumed.

Proof uses the normalized integral cubic F, Delta>=49, and the preceding
prime-summand proof. Put n=Ad,A=c*2^a,B=j/d,C=A-B,c in{1,3},n>=32.
Let eta=3 only if v3(n-1)=1, R1=(n-1)/eta,q=gcd(R1,B),v=B/q.
The prior block-value argument gives q,v>1 for both endpoints. With
H=(n-1)/q,J=j/q,s=c*d,
 T=J(H-J)(2H-J)/(s(n-2)) is a positive integer,
 theta=(n-j)(n-j-1)/((n-2)(n-1)) is in(0,1), and
 Delta*T=108*J^3*theta^2*(1-theta)/s^5.
Assume rad(B)|n(n-1). At every p|v, the valuations of Delta and T are at
least2v_p(v),v_p(v). For p|n, p|d but p does not divide A*c, and the exact
values are2v_p(v)+v_p(108),v_p(v). For a retained p^h||n-1, beta=v_p(B)>h
and the exact values are2(beta-h)+v_p(108),beta-h. The omitted single3 is
separate: v3(n-1)=1 implies v3(Delta)>=2beta+1,v3(T)>=beta+2.
Thus M=(Delta/v^2)*(T/v) is a positive integer, and
 c^5*d^2*M=108*theta^2*(1-theta).
For reduced theta=x/y, y^3|108; hence theta=1/3 or2/3, with right side8
or16. This forces c=1,d in{1,2,4},n=2^N. Every odd prime of v now divides
n-1. Theta is3-integral if3|v (also for the omitted single3), impossible.
At p>=5 dividing v, cancelling the complete p^h from theta's numerator
and denominator gives theta=-1 mod p. Thus theta=2/3 and v=5^t,4|N.

Theta=2/3 gives(n-1)(n+4)=3j(2n-1-j). Valuation at5 yields
 t=v5(n+4)=1+v5(N-2), so v<=5(N-2), by elementary binomial lifting.
It also forces j>n/6 and n-j>n/2. For n>=32, j-1>n/8 and
 Delta=72j^2(n-j)(j-1)/(d^4(n-2)(n-1)^2)>n/(8d^4).
Since T/v>=1 and M=16/d^2, Delta<=16v^2/d^2. Therefore
 2^N=n<128d^2v^2<=51200(N-2)^2.
The ratio2^N/(N-2)^2 increases for N>=5, and2^25>51200*23^2, so N<=24.
For the COMPLETE relaxed list N=4,8,12,16,20,24 the required integer
square (8*2^(2N)-24*2^N+19)/3 lies strictly between consecutive squares.
Contradiction. The complementary polynomial -F(1-X) proves the other side.

The prime from q divides n-1; the new prime divides neither n nor n-1.
If j has at most two odd prime factors neither can divide n, so d is a
power of2; n=c*2^a*d has oddpart(n) in{1,3}. If3|j, c=3 is impossible.
The remaining dyadic two/multi-prime rows and i=4..324 are NOT solved.
These are self-checks, not independent review, Lean, CI or priority claims.

PRIMARY NEW COLUMN THEOREM. For p>=5 prime, if gcd(ord_p(2),6)>1 then
EVERY j=2^b*3^s*p^t (b>=0,s,t>=1) satisfies the i=3 statement for all n>=2j.
This has a direct proof using the partial cancellation lemma above, not the
six-terminal mixed-support computation. The previous prime-power endpoint
theorem forces B to retain both3,p and hence c=1. If an odd prime divides
d, q>1 forces the other prime into n-1; all of v is then cancellable, so
theta=1/3 or2/3 forces d in{1,2,4}, contradiction. Thus n=2^N,d=2^b.

For N even, theta is3-integral: j contains the full3-power of n-1 (including
the omitted single3). If p|n-1 all of v cancels, contrary to3-integrality.
Otherwise q is a retained3-power (thus3|N), and cancellation of v's3-part
forces theta's denominator to divide3*p^t. Its3-integrality then forces p
into n-2. Hence ord_p(2)|N-1. For N odd, q>1 forces p|n-1, hence
ord_p(2)|N. This already excludes every even order.

Let o=ord_p(2) be odd and divisible by3. N even is impossible: q is a
retained3-power, requiring3|N, whereas o|N-1. Hence N is odd,o|N,3|N.
Then n=-1 mod9 and v3(n-2)=1. Cancelling v's p-part shows theta has only
3 in its denominator; the raw formula shows the exact denominator is3.
Thus theta=1/3 or2/3 and d<=4. If t>h=v_p(n-1), then theta=-1 mod p,
forcing p=5, whose order4 is inapplicable. So t=h. Theta=2/3 is impossible
at3: (n-1)(n+4)=3j(2n-1-j) has valuations1 and at least2. Theta=1/3 gives
 2(n-1)(n+1)=3j(2n-1-j), s<=v3(N)-1.
Write lambda=v_p(2^o-1). Elementary lifting gives t=lambda+v_p(N).
Thus j=d*3^s*p^t<=4*p^lambda*N/3. Theta=1/3 forces j>n/3, so
 2^(N-o)<4N, using p^lambda<=2^o-1.
Since N/o is odd, N>=3o would contradict4^o>12o for o>=3 and monotonicity
in N. Thus N=o, and s>=1 forces9|o. The factor2^(o/3)-1 of2^o-1 is prime
to p, so it divides qC=(n-1)/p^lambda. But j>n/3 gives
 2^(o/3)-1<=qC<3*d*3^s<=4*3^v3(o)<=4o.
For odd multiples of9 with o>=27 this is impossible by monotonicity
(starting2^9-1=511>108). Thus o=9. Factoring2^9-1=7*73 gives p=73,
lambda=t=1,N=9,s=1,d in{1,2,4}. The original j<=n/2 leaves d=1,j=219;
3*(512-219)*(511-219)-(511*510)=-3942, not zero. Contradiction.
Every cutoff here follows from an unbounded proof; no prime search cutoff.
Primes whose order is coprime to6 (e.g.23,31) are NOT covered by this theorem.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from math import comb, gcd, isqrt, lcm
from functools import lru_cache

@lru_cache(None)
def factors(x: int) -> dict[int,int]:
    if x<=0: raise ValueError('positive integer required')
    out={};p=2
    while p*p<=x:
        while x%p==0:out[p]=out.get(p,0)+1;x//=p
        p=3 if p==2 else p+2
    if x>1:out[x]=out.get(x,0)+1
    return out

def oddpart(x:int)->int:
    if x<=0:raise ValueError('positive integer required')
    return x//(x&-x)

def vp(x:int|Q,p:int)->int:
    x=Q(x)
    if x==0:raise ValueError('zero has no finite valuation')
    a,b=abs(x.numerator),x.denominator;t=0
    while a%p==0:a//=p;t+=1
    while b%p==0:b//=p;t-=1
    return t

def support_part(x:int,modulus:int)->int:
    rem=x
    while (g:=gcd(rem,modulus))>1:rem//=g
    return x//rem

def vpbinom(n:int,j:int,p:int)->int:
    ans=0;power=p
    while power<=n:
        ans+=n//power-j//power-(n-j)//power;power*=p
    return ans

def carries(n:int,j:int,p:int)->int:
    a,b,carry,ans=j,n-j,0,0
    while a or b or carry:
        carry=(a%p+b%p+carry)//p;ans+=carry;a//=p;b//=p
    return ans

def normalized(n:int,j:int):
    d=gcd(n,j);A,B=n//d,j//d;c=3 if A%3==0 else 1;h=A//c
    if h<4 or h&(h-1):return None
    eta=3 if vp(n-1,3)==1 else 1
    q=gcd((n-1)//eta,B);v=B//q;H,J=(n-1)//q,j//q
    T=Q(J*(H-J)*(2*H-J),c*d*(n-2))
    D=Q(108*B*B*(A-B)**2*(j-1)*(n-j-1),c**4*(n-2)**2*(n-1)**3)
    theta=Q((n-j)*(n-j-1),(n-2)*(n-1))
    return d,A,B,c,v,D,T,theta

def local_audit(nmax:int)->dict:
    count=tests=0
    cases=dict.fromkeys(('p_divides_n','retained_3','omitted_single_3','retained_p_ge_5'),0)
    for n in range(8,nmax+1):
        for j in range(4,n-3):
            data=normalized(n,j)
            if data is None:continue
            d,A,B,c,v,D,T,theta=data
            assert 0<theta<1 and D>0 and T>0
            assert D*T==Q(108*v**3,c**5*d*d)*theta**2*(1-theta)
            w=support_part(v,n*(n-1))
            for p,b in factors(w).items():
                if n%p==0:
                    cases['p_divides_n']+=1
                    assert d%p==0 and (A*c)%p!=0
                    assert vp(T,p)==b and vp(D,p)==2*b+vp(108,p)
                elif p==3 and vp(n-1,3)==1:
                    cases['omitted_single_3']+=1
                    assert vp(T,p)>=b+2 and vp(D,p)>=2*b+1 and vp(theta,p)>=0
                else:
                    cases['retained_3' if p==3 else 'retained_p_ge_5']+=1
                    assert vp(T,p)==b and vp(D,p)==2*b+vp(108,p)
                    assert vp(theta,p)>=0 and vp(theta+1,p)>=1
                assert vp(D/w**2,p)>=0 and vp(T/w,p)>=0
                tests+=1
            # Integral SCALED controls, explicitly not hypothetical counterexamples.
            F=(Q(A,c),Q(-3*B,c),Q(3*B*(j-1),c*(n-1)),
               Q(-B*(j-1)*(j-2),c*(n-1)*(n-2)))
            scale=lcm(*(z.denominator for z in F))
            dd,tt=scale**4*D/w**2,scale*T/w
            assert dd.denominator==tt.denominator==1 and dd>0 and tt>0
            assert c**5*d*d*dd*tt==108*scale**5*(v//w)**3*theta**2*(1-theta)
            count+=1
    assert all(cases.values())
    d,A,B,c,v,D,T,theta=normalized(32,5)
    assert v==5 and 32*31%5!=0 and vp(T/v,5)<0 and vp(D/v**2,5)<0
    return {'rational_normalized_pairs_both_halves':count,'supported_local_valuations':tests,
            'local_cases':cases,'integral_scaled_controls':count,'negative_control':True}

def terminal_audit()->dict:
    rats=[]
    for y in range(2,121):
        for x in range(1,y):
            if gcd(x,y)==1 and (108*Q(x,y)**2*(1-Q(x,y))).denominator==1:rats.append([x,y])
    assert rats==[[1,3],[2,3]]
    choices=[]
    for c in (1,3):
        for d in range(1,20):
            for val in (8,16):
                if val%(c**5*d*d)==0:
                    assert c==1 and d in (1,2,4);choices.append([c,d,val])
    for N in range(4,2001,4):
        assert vp((1<<N)+4,5)==1+vp(N-2,5)
        assert 5**vp((1<<N)+4,5)<=5*(N-2)
    assert (1<<25)>51200*23**2
    terminal=[]
    for N in (4,8,12,16,20,24):
        n=1<<N;raw=8*n*n-24*n+19
        assert raw%3==0
        R=raw//3;z=isqrt(R)
        assert z*z<R<(z+1)**2
        terminal.append({'N':N,'R':R,'floor_sqrt':z,'above_square':R-z*z,'below_next':(z+1)**2-R})
    controls=0
    for n in range(32,20001):
        raw=8*n*n-24*n+19
        if raw%3:continue
        y=isqrt(raw//3)
        if y*y!=raw//3 or y%2!=1:continue
        m=(y+1)//2;j=n-m
        if j<4:continue
        assert Q(m*(m-1),(n-2)*(n-1))==Q(2,3)
        assert 6*j>n and 2*m>n and 8*(j-1)>n
        for d in (1,2,4):
            D=Q(108*j*j*m*m*(j-1)*(m-1),d**4*(n-2)**2*(n-1)**3)
            assert D==Q(72*j*j*m*(j-1),d**4*(n-2)*(n-1)**2)>Q(n,8*d**4)
        controls+=1
    assert controls>0
    return {'rational_regressions':rats,'integer_choices':choices,'lifting_regressions':500,
            'complete_terminal_six':terminal,'exact_theta_controls':controls}

def predicates(n:int,j:int):
    fj=set(factors(j))-{2};fm=set(factors(n-j))-{2}
    fn=set(factors(n));fn1=set(factors(n-1))
    mixed=not(fj-(fn|fn1)) or not(fm-(fn|fn1))
    outside=len(fj-fn)<=1 or len(fm-fn)<=1
    row=oddpart(n)
    two=len(fj)<=2 and (row not in (1,3) or (3 in fj and row!=1))
    d=gcd(n,j)
    old=len(set(factors(j//d))-{2})<=1 or len(set(factors((n-j)//d))-{2})<=1
    old=old or len(set(factors(j-1))-{2})<=1 or len(set(factors(comb(n,3)))-{2})<=3
    return mixed,outside,two,old

def witness(n:int,j:int)->int:
    g=gcd(comb(n,3),comb(n,j))
    p=next((p for p in sorted(set(factors(comb(n,3)))-{2}) if g%p==0),None)
    assert p is not None and vpbinom(n,3,p)>0
    assert vpbinom(n,j,p)==carries(n,j,p)>0
    return p

def original_audit(nmax:int)->dict:
    pairs=mixed=outside=two=covered=new=0;example=None
    for n in range(8,nmax+1):
        for j in range(4,n//2+1):
            pairs+=1;a,b,c,old=predicates(n,j)
            mixed+=a;outside+=b;two+=c
            if a or b or c:
                p=witness(n,j);covered+=1
                if not old:
                    new+=1
                    if example is None:example=[n,j,p]
    examples=[]
    for n,j in ((4096,351),(24576,3375),(10752,2205)):
        a,b,c,old=predicates(n,j)
        assert (a or b or c) and not old
        examples.append({'n':n,'j':j,'d':gcd(n,j),'shared_prime':witness(n,j),
                         'mixed':a,'outside_count':b,'two_prime_row':c})
    return {'original_pairs':pairs,'mixed_predicate_pairs':mixed,'outside_count_pairs':outside,
            'two_prime_nondyadic_pairs':two,'covered_union':covered,
            'beyond_three_named_old_criteria':new,'first_new_named':example,
            'larger_named_examples':examples,'categories_overlap':True}

@lru_cache(None)
def order_two(p:int)->int:
    if p<3 or factors(p)!={p:1}:raise ValueError('odd prime required')
    x=1
    for o in range(1,p):
        x=2*x%p
        if x==1:return o
    raise AssertionError('order not found')

def three_p_column(j:int)->bool:
    fs=set(factors(oddpart(j)))
    if len(fs)!=2 or 3 not in fs:return False
    p=next(iter(fs-{3}))
    return gcd(order_two(p),6)>1

def three_p_audit(nmax:int)->dict:
    covered=new=0;columns=set();orders={};first=None
    for n in range(8,nmax+1):
        for j in range(4,n//2+1):
            if not three_p_column(j):continue
            shared=witness(n,j);covered+=1;columns.add(j)
            p=next(iter(set(factors(oddpart(j)))-{3}));orders[p]=order_two(p)
            old=predicates(n,j)[3]
            if not old:
                new+=1
                if first is None:first=[n,j,shared]
    parity=0;odd_three=0
    for p in range(5,501,2):
        if factors(p)!={p:1}:continue
        o=order_two(p)
        if o%2==0:
            assert not any((N%2==1 and N%o==0) or (N%2==0 and (N-1)%o==0)
                           for N in range(lcm(2,o)))
            parity+=1
        elif o%3==0:
            assert not any(N%2==0 and N%3==0 and (N-1)%o==0
                           for N in range(lcm(6,o)))
            odd_three+=1
    # Exact all-degree inequalities used for the odd order proof.
    assert 4**3>12*3 and 2**9-1>4*27
    assert factors((1<<9)-1)=={7:1,73:1}
    assert order_two(7)==3 and order_two(73)==9
    n=512;legal=[]
    for d in (1,2,4):
        j=3*73*d
        if j<=n//2:
            difference=3*(n-j)*(n-j-1)-(n-1)*(n-2)
            assert difference==-3942;legal.append([d,j,difference])
    assert legal==[[1,219,-3942]]
    # Congruence-compatible control outside the proved order condition.
    assert order_two(23)==11 and order_two(31)==5
    assert not three_p_column(3*23) and not three_p_column(3*31)
    assert 11%2==1 and 11%order_two(23)==0
    assert 12%2==0 and 12%3==0 and (12-1)%order_two(23)==0
    # Explicit whole-column examples, evaluated at dyadic rows too.
    named=[]
    for j in (111,3375,1971):
        assert three_p_column(j)
        N=(2*j-1).bit_length();n=1<<N
        named.append([n,j,witness(n,j)])
    return {'new_three_p_whole_column_pairs':covered,'new_three_p_columns':len(columns),
            'new_three_p_beyond_three_named_old_criteria':new,
            'first_three_p_new_named':first,'sample_orders':orders,
            'even_order_full_period_regressions':parity,
            'odd_order_multiple_three_regressions':odd_three,
            'odd_order_terminal':legal,'whole_column_named_dyadic_samples':named,
            'order_coprime_six_controls_retained':True}

def symbolic()->dict:
    import sympy as S
    n,j,d,t,X=S.symbols('n j d t X');m=n-j;D0=(n-2)*(n-1)
    Delta=108*j*j*m*m*(j-1)*(m-1)/(d**4*(n-2)**2*(n-1)**3)
    reduced=72*j*j*m*(j-1)/(d**4*(n-2)*(n-1)**2)
    target=36*j*j*m*(j-1)*(3*m*(m-1)-2*D0)/(d**4*(n-2)**2*(n-1)**3)
    assert S.factor(Delta-reduced-target)==0
    assert S.expand((n-1)*(n+4)-3*j*(2*n-1-j))==S.expand(3*m*(m-1)-2*D0)
    assert S.factor(S.Rational(4,27)-t*t*(1-t)-(t-S.Rational(2,3))**2*(t+S.Rational(1,3)))==0
    assert S.expand(2*(X-2)**2-(X-1)**2)==S.expand((X-3)**2-2)
    assert S.expand(3*(5*n/6)*(5*n/6-1)-2*D0)==S.expand(n*n/12+7*n/2-4)
    assert S.expand(3*(2*n/3)*(2*n/3-1)-D0)==S.expand(n*n/3+n-2)
    assert S.expand(2*(n-1)*(n+1)-3*j*(2*n-1-j))==S.expand(3*m*(m-1)-D0)
    return {'symbolic_exact_identities':True}

def main()->None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--nmax',type=int,default=500)
    p.add_argument('--local-nmax',type=int,default=320)
    p.add_argument('--symbolic',action='store_true');a=p.parse_args()
    if a.nmax<8 or a.local_nmax<256:p.error('requires nmax>=8 and local-nmax>=256')
    out={'status':'passed','all_parameter_proof_by_sampling':False,'whole_problem_solved':False,
         'independent_review':False}
    out.update(local_audit(a.local_nmax));out.update(terminal_audit());out.update(original_audit(a.nmax));out.update(three_p_audit(a.nmax))
    if a.symbolic:out.update(symbolic())
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
