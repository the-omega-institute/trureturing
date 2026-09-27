#!/usr/bin/env python3
"""# Erdos 699: common cyclic quotients and removal of common odd powers

Continuation of issue #9670 / PR #9769, read at
`f8af4869e9addd95d2fe1591960f61f336443c76`.
These are written partial theorems with exact self-audits. They do not solve
unrestricted i=3 or all Erdos 699. No independent review, new Lean
certification, or worldwide priority is claimed.

## Statements directly about the original problem

Write o(p)=ord_p(2), h(p)=v2(o(p)), and H_p=<2 mod p>.
When 3 belongs to H_p, let a_p be its discrete logarithm to the DISTINGUISHED
base 2, taken modulo o(p). The existence and every residue used below are
finite exact predicates; their use does not bound the prime or any exponent.

**A. Whole two-prime columns.** Let p,q>=5 be distinct primes. Put
 g=gcd(o(p),o(q)). Suppose h(p)=h(q), g>1, and either
 (i) 3 is absent from at least one of H_p,H_q; or
 (ii) both a_p,a_q exist and a_q-a_p is neither 1 nor -1 modulo g.
Then for ALL b>=0,s,t>=1 and ALL n>=2j, j=2^b*p^s*q^t has an odd prime
common to binomial(n,3) and binomial(n,j).
Zero binary-order layers ARE included when g>1. Positive-layer equal-sign
results in the previous file are subsumed, but opposite signs can now also
be excluded by an odd part of the common quotient.

Examples: p11,q211 have orders10,210 and logs8,43; the difference is5 mod10,
not +/-1. Their earlier chi signs are opposite, so the old criterion did
not cover these columns. p7,q73 have orders3,9, and 3 is absent from H_7.
Thus all 2^b*11^s*211^t and all 2^b*7^s*73^t columns are covered.

**B. Arbitrarily many primes and genuinely odd gcds.** Suppose all odd prime
divisors of j belong to ONE residue class r modulo24, r in{5,11,13,19}.
Let d=gcd(n,j). For r11 or19 assume oddpart(d) is an integer square; for
r5 or13 assume it is an integer fourth power. Then every3<j<=n/2 has a
common odd prime in the two binomials. There is no bound on the number of
prime divisors, on their powers, or on the common odd power. The gcd is
not required to be a power of2. This is a theorem for the stated original
pairs; it is not an unconditional all-gcd column theorem for3+ primes.

**C. An explicit unbounded supply for A.** For k>=2 put
 M_k=2^(2*3^(k-1))+2^(3^(k-1))+1.
Every prime q dividing M_k has o(q)=3^k. Therefore every pair(7,q) supplies
all columns2^b*7^s*q^t. Distinct k use disjoint prime supports, so there
really are infinitely many eligible q. No primality of M_k, unproved
prime-producing formula, Zsigmondy theorem, or density assertion is used.

## Inherited number-theoretic premises and exact scope

Under a putative i=3 counterexample, the deposited normalization and
mixed-support proofs give
 n=c*2^a*d, c in{1,3}, a>=2, d=gcd(n,j), j<n/2.
Each of j and n-j has an odd prime dividing n-1 and an odd prime outside
n(n-1). For theta=(n-j)(n-j-1)/((n-1)(n-2))=x/y in lowest terms,
 0<theta<1, y>1, y divides3z,
where every prime of z divides j and divides neither n nor n-1.
Thus any prime other than3 in y divides both j and n-2.
The proofs of these facts use the normalized integral cubic and its
integer discriminant; this new group computation does not re-certify them.
Their source is erdos699-mixed-support-check.py, with the prime-summand
and prime-power files and main-theory sections2-5 it explicitly uses.
For exactly two odd endpoint primes, the two required distinct primes
are both outside n. Thus d is a power of2 and n=2^N or3*2^N.
We also inherit the positive-equal-layer dyadic-row theorem from
`erdos699-order-layer-check.py`: if n=2^N and all odd endpoint primes have
one common h>0, the original i=3 pair is excluded. Its exceptional h2
branch is closed there by the exact mod4/mod16 argument.

No claim about the uniform3-p theorem is needed for A or B; its new
p-adic logarithm input is NOT a premise of this continuation.

## 1. Exact common-quotient lemma: the common exponent is the coupling

Let m,n be positive integers, g=gcd(m,n). On C_m x C_n define
 pi(a,b)=a-b modg.
This is well-defined, a surjective group homomorphism, with kernel
 K={(t modm,t modn):t in Z}.
Indeed the forward inclusion is immediate. Conversely a=b modg is exactly
the solvability condition for t=a modm,t=b modn: write t=a+mk and solve
 (m/g)k=(b-a)/g mod(n/g), using Bezout because gcd(m/g,n/g)=1.
Thus
 (C_m x C_n)/K is isomorphic to C_g.
In multiplicative notation, (H_p x H_q)/<(2,2)> is C_g via
 (2^a,2^b) -> a-b modg.
This is the classical cyclic special case of generalized CRT/Goursat's
subdirect-product description. The elementary proof above is supplied;
it is not claimed as a new abstract group theorem.

If 3 lies in both H_p,H_q, the simultaneous original-row conditions
 p | 3*2^N-1, q | 3*2^N-2
are equivalent to N=-a_p modo(p), N=1-a_q modo(q), hence to
 a_q-a_p=1 modg.
When compatible they yield a full residue class modulo lcm(o(p),o(q)),
so positive exponents exist as well. If either subgroup lacks3, neither
orientation is possible. Swapping the two prime roles replaces1 by-1.

This is stronger than testing the two primes separately. It is also
stronger than a parity character: the full common quotient retains ALL
its Sylow components. For11,211 the C2 signs permit a role assignment,
but the C5 component would require0=+/-1. Concretely the two orientations
force respectively N=2 and8 mod10, or N=3 and7 mod10.
There is no arbitrary identification of residue fields: the distinguished
base2 fixes the maps, and the position of3 is explicitly retained.

## 2. Proof of A, including zero layers

Consider a putative counterexample in the stated two-prime column.
The inherited reduction leaves n=2^N or3*2^N.
If h(p)=h(q)>0, the dyadic row is excluded by the preceding equal-layer
written theorem, with its original assumptions and review status.
If instead both h values are0, the orders are odd. If theta's denominator
has a prime other than3, the two distinct endpoint primes must occupy
n-1 and n-2, so their orders divide N and N-1. This contradicts g>1.
Otherwise y divides3 (3 does not divide z), so theta=1/3 or2/3.
The exact equations are respectively
 2(n-1)(n+1)=3j(2n-1-j),
 (n-1)(n+4)=3j(2n-1-j).
The inherited external endpoint prime R>=5 then divides n+1 or n+4.
Hence2^N=-1 modR or2^(N-2)=-1 modR. An odd-order subgroup contains no
nontrivial element of order2; -1 is not in it. Contradiction.
This proves the needed dyadic statement also at zero layer.

For n=3*2^N the raw denominator(n-1)(n-2) is prime to3. Its reduced
nontrivial denominator must therefore have an external endpoint prime,
which divides n-2. The other endpoint prime divides n-1. Both possible
orientations contradict the common-quotient condition in section1.
All original n and all exponents are excluded, proving A.

The boundary g>1 at zero layer is necessary for this local argument:
orders of7 and31 are3 and5; N6 gives7|2^6-1,31|2^6-2.
The opposite-sign case11,19 also cannot be claimed as excluded: their
orders10,18 and logs8,13 have g2 and difference1. At N42 the two triple-
dyadic role conditions hold. These are local controls, not original
binomial counterexamples.

## 3. Proof of C without a prime-producing conjecture

Let T=2^(3^(k-1)). M_k=T^2+T+1 is odd and1 mod3, so a prime q|M_k is
neither2 nor3. It divides2^(3^k)-1. If its order divided3^(k-1), T=1 modq
would imply q|3, impossible. As every divisor of3^k is a3-power, its
order is exactly3^k. In particular q!=7 for k>=2. The orders of7 andq
have gcd3 and both are odd. Also H_7={1,2,4} does not contain3, so A applies.
Every M_k>1 has a prime divisor. The order computation makes the prime
supports for distinct k disjoint. This proves the stated infinite supply.

## 4. Power quotients eliminate the common odd factor in B

Set h=1 for r11,19 and h=2 for r5,13. Every prime p in that class has
 v2(p-1)=h and Legendre(2,p)=-1.
Consequently Gamma_p=F_p^*/(F_p^*)^(2^h) is cyclic of order2^h and the
class of2 is a generator. With2 mapped to1 in additive notation,
 [-1]=2^(h-1), [4]=2, and every2^h-th power maps to0.
This is a concrete use of the existing power-character kernel theorem,
not the definition of an unrelated group. Only primes outside d are
used for these unit-group operations.

Assume H. Write d=2^b*v^(2^h), N=a+b, n=c*2^N*v^(2^h).
The inherited prime P|j,n-1 is outside d, so in the case c1 the quotient
at P implies N=0 mod2^h. There cannot be ANY endpoint prime dividing
n-2: its quotient would instead imply N=1 mod2^h.
The denominator restriction therefore yields theta=1/3 or2/3.
For the external endpoint prime R the above two equations force
 0=2^(h-1) mod2^h, or 0=2^(h-1)+2 mod2^h.
The first is impossible; the second only permits h2.
If h2, every odd prime of j is1 mod4, hence oddpart(j)=1 mod4.
Also4|N and N>=2 imply N>=4, so16|n. For odd j the equation
 3(n-j)(n-j-1)=2(n-1)(n-2)
reads2=0 mod4. For even j, N>v2(j) follows from a>=2 and the definition
of d; valuation at2 forces v2(j)=2. Then j=4 mod16 and the same equality
reads12=4 mod16. This closes the entire c1 branch.

For c3 it suffices to project to the square quotient. Since v^(2^h) is
a square, at EVERY endpoint prime p outside n,
 Legendre(n,p)=Legendre(3,p)*(-1)^N.
For a fixed allowed mod24 class the3-symbol is one common sign sigma:
 r5,11,13,19 give respectively -1,+1,+1,-1.
The required prime of n-1 gives sigma*(-1)^N=1. No endpoint prime can
then divide n-2, since that requires Legendre(n,p)=Legendre(2,p)=-1.
But for3|n the raw theta denominator is prime to3; the inherited reduced
denominator restriction must supply precisely such an endpoint prime.
Contradiction. This proves B for arbitrary numbers of primes and for
arbitrarily large common odd squares/fourth powers.

For completeness the elementary symbol table follows by Gauss counting:
for multiplication by2 the number of negative least residues is
(p-1)/2-floor(p/4), and for multiplication by3 it is
floor(p/3)-floor(p/6). Multiplying the signed representatives proves the
sign formula; evaluating p mod24 yields the table above. No analytic
prime-density or reciprocity theorem is required as a new input.

## Remote formalization correspondence

Read dev `D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.lean`, blob
`79c32483be14a2333e043f151744877c4ea30fb8`. It already proves
 power_character_joint_kernel_eq_power_subgroup,
 power_quotient_has_exponent_dividing,
 power_subgroup_le_iff_quotient_pow_eq_one.
In particular G^k equals the intersection of all mu_k-character kernels;
G/G^k is the maximal exponent-dividing-k quotient. Apply this at k2,k4
for section4. The residue-field character calculations, cofactor links,
role existence, and final original-column theorems remain new proof
obligations. This source was read, not recompiled in this session.
The common-diagonal kernel in section1 is a separate quotient; it is NOT
silently identified with a power subgroup. Their roles are complementary:
section1 compares the SAME exponent across primes; section4 removes common
powers within each prime while retaining the distinguished images of2.

Formalization handoff: (a) generalized CRT/kernel equality for C_m x C_n;
(b) labelled target membership and both orientations; (c) odd-order absence
of-1 and the original theta residuals; (d) Gamma_p generator and sign facts;
(e) common-power elimination only at unit primes; (f) compose with the
separately formalized original-number-theoretic premises. No frozen Lean,
private axiom, truth count, governance file or CI rule is changed.

## Actual scope and limits

A covers new whole double-prime columns, including zero layers and a subset
of the previously allowed opposite signs. B expands the previous pure-dyadic
gcd condition to genuine odd square/fourth-power gcds for unbounded support.
No induction eliminating arbitrary support, arbitrary odd gcd, or every
common-quotient-compatible pair has been established. In particular the
11,19 local configuration remains compatible. Unrestricted i=3 and the
remaining original indices4..324 are not solved here. The inherited i>=325
regional statement is unchanged. Finite regression is not a completion rate.

"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import lru_cache
from math import comb, gcd, isqrt, lcm
import json

@lru_cache(None)
def factor(n: int) -> tuple[tuple[int,int], ...]:
    if n < 1: raise ValueError('factor requires positive integer')
    out=[]; p=2
    while p*p <= n:
        e=0
        while n%p == 0: n//=p; e+=1
        if e: out.append((p,e))
        p=3 if p==2 else p+2
    if n>1: out.append((n,1))
    return tuple(out)

def prime(p: int) -> bool:
    return p >= 2 and factor(p)==((p,1),)

def v2(n: int) -> int:
    if n<1: raise ValueError('v2 requires positive integer')
    return (n&-n).bit_length()-1

def oddpart(n: int) -> int:
    return n>>v2(n)

@lru_cache(None)
def order2(p: int) -> int:
    if p<=2 or not prime(p): raise ValueError('odd prime required')
    o=p-1
    for r,_ in factor(o):
        while o%r==0 and pow(2,o//r,p)==1: o//=r
    assert pow(2,o,p)==1
    assert all(pow(2,o//r,p)!=1 for r,_ in factor(o))
    return o

@lru_cache(None)
def orbit(p: int) -> tuple[int,...]:
    o=order2(p); a=1; out=[]
    for _ in range(o): out.append(a); a=2*a%p
    assert a==1 and len(set(out))==o
    return tuple(out)

@lru_cache(None)
def log3(p: int) -> int | None:
    row=orbit(p)
    result=row.index(3) if 3 in row else None
    assert (result is not None)==(pow(3,order2(p),p)==1)
    return result

def quotient_column(p: int, q: int) -> bool:
    if p==q or min(p,q)<5 or not prime(p) or not prime(q): return False
    m,n=order2(p),order2(q); g=gcd(m,n)
    if v2(m)!=v2(n) or g==1: return False
    a,b=log3(p),log3(q)
    return a is None or b is None or (b-a)%g not in {1%g,(-1)%g}

def old_column(p: int, q: int) -> bool:
    m,n=order2(p),order2(q)
    if v2(m)==0 or v2(m)!=v2(n): return False
    def chi(r: int, o: int) -> int:
        u=pow(3,o//2,r)
        return 1 if u==1 else -1 if u==r-1 else 0
    return (chi(p,m),chi(q,n)) not in {(1,-1),(-1,1)}

def power_class(j: int) -> tuple[int,int] | None:
    ps=[p for p,_ in factor(j) if p>2]
    if not ps: return 11,2
    r=ps[0]%24
    if r not in {5,11,13,19} or any(p%24!=r for p in ps): return None
    return r,2 if r in {11,19} else 4

def is_power(n: int, k: int) -> bool:
    if n<1 or k not in {2,4}: raise ValueError('positive n and k=2 or4 required')
    z=isqrt(n) if k==2 else isqrt(isqrt(n))
    return z**k==n

def power_pair(n: int, j: int) -> bool:
    d=power_class(j)
    return d is not None and is_power(oddpart(gcd(n,j)),d[1])

def vpbinom(n: int,j: int,p: int) -> int:
    s=0; u=p
    while u<=n:
        s+=n//u-j//u-(n-j)//u; u*=p
    return s

def carries(n: int,j: int,p: int) -> int:
    a,b,k,s=j,n-j,0,0
    while a or b or k:
        k=(a%p+b%p+k)//p; s+=k; a//=p; b//=p
    return s

@lru_cache(None)
def odd_cn3_primes(n: int) -> tuple[int,...]:
    f=Counter()
    for t in (n,n-1,n-2):
        for p,e in factor(t): f[p]+=e
    f[2]-=1; f[3]-=1
    return tuple(sorted(p for p,e in f.items() if p>2 and e>0))

def verify_witness(n: int,j: int,p: int, direct: bool=False) -> None:
    assert prime(p) and p>2 and 3<j<=n//2
    assert vpbinom(n,3,p)>0 and vpbinom(n,j,p)>0
    assert carries(n,j,p)==vpbinom(n,j,p)
    if direct: assert comb(n,3)%p==0 and comb(n,j)%p==0

def witness(n: int,j: int) -> int:
    p=next((p for p in odd_cn3_primes(n) if vpbinom(n,j,p)),None)
    assert p is not None,(n,j)
    verify_witness(n,j,p,n<=150)
    return p

def quotient_audit(max_order: int) -> dict:
    products=pairs=0
    for m in range(1,max_order+1):
        for n in range(1,max_order+1):
            g=gcd(m,n)
            diagonal={(t%m,t%n) for t in range(lcm(m,n))}
            assert len(diagonal)==m*n//g
            fibre=Counter()
            for a in range(m):
                for b in range(n):
                    u=(a-b)%g
                    assert ((a,b) in diagonal)==(u==0)
                    fibre[u]+=1; pairs+=1
            assert len(fibre)==g and len(set(fibre.values()))==1
            products+=1
    return {'cyclic_products':products,'all_element_pairs':pairs,'quotient_orders_verified':True}

def finite_field_audit(pmax: int) -> dict:
    ps=[p for p in range(5,pmax+1) if prime(p)]
    sign_checks=power_checks=period_pairs=0
    for p in ps:
        row=orbit(p); assert len(row)==order2(p)
        a=log3(p)
        if a is not None: assert pow(2,a,p)==3
        for u in (2,3):
            negatives=sum((i*u)%p>p//2 for i in range(1,(p+1)//2))
            expected=(p-1)//2-p//4 if u==2 else p//3-p//6
            assert negatives==expected
            assert pow(u,(p-1)//2,p)==(1 if negatives%2==0 else p-1)
            sign_checks+=1
        r=p%24
        if r in {5,11,13,19}:
            h=1 if r in {11,19} else 2; k=1<<h; u=(p-1)//k
            kernel={pow(t,k,p) for t in range(1,p)}
            assert len(kernel)==u and pow(2,(p-1)//2,p)==p-1
            cosets=[{pow(2,a,p)*t%p for t in kernel} for a in range(k)]
            assert len(set.union(*cosets))==p-1 and sum(map(len,cosets))==p-1
            assert p-1 in cosets[k//2] and 4 in cosets[2%k]
            assert all(pow(t,k,p) in kernel for t in range(1,p))
            power_checks+=1
    small=[p for p in ps if p<=100]
    for i,p in enumerate(small):
        for q in small[i+1:]:
            m,n=order2(p),order2(q); a,b=log3(p),log3(q); g=gcd(m,n)
            predicts=a is not None and b is not None and (b-a-1)%g==0
            cycle=lcm(m,n)
            brute=any((3*pow(2,N,p)-1)%p==0 and (3*pow(2,N,q)-2)%q==0 for N in range(cycle))
            assert predicts==brute
            if v2(m)==v2(n)==0 and g>1:
                assert all(not(pow(2,N,p)==1 and pow(2,N,q)==2) for N in range(cycle))
            period_pairs+=1
    opposite=[];zero=[]; old=allnew=0
    for i,p in enumerate(ps):
        for q in ps[i+1:]:
            prev=old_column(p,q); now=quotient_column(p,q)
            if prev: assert now; old+=1
            if not now: continue
            allnew+=1
            m,n=order2(p),order2(q)
            if v2(m)==0: zero.append((p,q,m,n))
            elif not prev:
                opposite.append((p,q,m,n,log3(p),log3(q),gcd(m,n)))
    assert quotient_column(11,211) and not old_column(11,211)
    assert quotient_column(7,73) and not old_column(7,73)
    assert not quotient_column(11,19) and not quotient_column(7,31)
    assert (3*pow(2,42,11)-1)%11==0 and (3*pow(2,42,19)-2)%19==0
    assert (2**6-1)%7==0 and (2**6-2)%31==0
    assert (log3(211)-log3(11))%10==5
    assert pow(2,8,11)==3 and pow(2,43,211)==3
    return {'primes':len(ps),'Gauss_sign_checks':sign_checks,'full_power_quotients':power_checks,
            'two_prime_complete_periods':period_pairs,'pairs_under_new_criterion':allnew,
            'old_positive_layer_pairs_retained':old,'new_zero_layer_pairs':len(zero),
            'new_opposite_sign_pairs':len(opposite),'opposite_sign_examples':opposite[:10],
            'zero_layer_examples':zero[:10],'compatible_negative_controls_retained':True}

def column_audit(nmax: int) -> dict:
    columns=[];new=[];odd=[];same=[]
    for j in range(4,nmax//2+1):
        ps=[p for p,_ in factor(j) if p>2]
        if len(ps)!=2 or min(ps)<5: continue
        p,q=ps
        if quotient_column(p,q):
            columns.append(j)
            if not old_column(p,q):new.append(j)
            if v2(order2(p))==0:odd.append(j)
            else:same.append(j)
    allpairs=newpairs=0;examples=[]
    newset=set(new)
    for j in columns:
        for n in range(2*j,nmax+1):
            p=witness(n,j);allpairs+=1
            if j in newset:
                newpairs+=1
                if n==2*j and len(examples)<12:examples.append((n,j,p))
    return {'nmax':nmax,'column_indices':len(columns),'original_pairs':allpairs,
            'columns_outside_old_equal_layer_predicate':len(new),'pairs_outside_that_predicate':newpairs,
            'zero_layer_column_indices':len(odd),'new_witness_examples':examples,
            'is_proof_by_sampling':False}

def power_audit(nmax: int) -> dict:
    tests=odd_gcd=0
    for j in range(4,nmax//2+1):
        d=power_class(j)
        if d is None: continue
        for n in range(2*j,nmax+1):
            if not power_pair(n,j): continue
            witness(n,j);tests+=1;odd_gcd+=oddpart(gcd(n,j))>1
    # Each selected target has three distinct odd primes and an actual odd gcd.
    # Witnesses are searched in a finite small-prime list; this is regression,
    # not a claim to have exhausted an infinite family using these primes.
    selections={5:(5,29,53),11:(11,59,83),13:(13,37,61),19:(19,43,67)}
    small=[p for p in range(3,5001,2) if prime(p)]
    targets=[]
    for r,ps in selections.items():
        k=2 if r in {11,19} else 4
        a=ps[0]; d0=a**k; B=ps[0]*ps[1]*ps[2]
        for c in (1,3):
            for b in (0,1):
                j=(1<<b)*d0*B
                N=max(4,(2*j//(c*d0)).bit_length())
                while c*d0*(1<<N)<2*j:N+=1
                for t in range(2):
                    n=c*d0*(1<<(N+t))
                    assert gcd(n,j)==(1<<b)*d0 and power_pair(n,j)
                    p=next((p for p in small if vpbinom(n,3,p)>0 and vpbinom(n,j,p)>0),None)
                    assert p is not None,(r,c,b,n,j)
                    verify_witness(n,j,p)
                    targets.append({'class':r,'power':k,'n':n,'j':j,'gcd':gcd(n,j),'shared_prime':p})
    # Keep the odd-gcd hypothesis nonvacuous and its boundary explicit.
    assert is_power(121,2) and not is_power(11,2)
    assert is_power(625,4) and not is_power(25,4)
    assert all(v['gcd']>1 and len([p for p,_ in factor(v['j']) if p>2])==3 for v in targets)
    return {'small_box_nmax':nmax,'verified_pairs':tests,'verified_odd_gcd_pairs':odd_gcd,
            'three_prime_odd_gcd_targets':targets,'target_count':len(targets)}

def tower_audit() -> dict:
    representatives=[]
    for k,q in ((2,73),(3,262657),(4,2593),(5,487)):
        assert prime(q) and order2(q)==3**k
        T=pow(2,3**(k-1),q)
        assert (T*T+T+1)%q==0 and quotient_column(7,q)
        representatives.append((k,q,order2(q)))
    return {'checked_representatives':representatives,'infinite_claim_uses_written_factorization_proof':True}

def symbolic_audit() -> dict:
    import sympy as S
    n,j=S.symbols('n j')
    assert S.expand(3*(n-j)*(n-j-1)-(n-1)*(n-2)-
                    (2*(n-1)*(n+1)-3*j*(2*n-1-j)))==0
    assert S.expand(3*(n-j)*(n-j-1)-2*(n-1)*(n-2)-
                    ((n-1)*(n+4)-3*j*(2*n-1-j)))==0
    assert 3*((-1)%4)*((-2)%4)%4==2
    assert 3*((-4)%16)*((-5)%16)%16==12
    assert 2*(-1)*(-2)%16==4
    return {'exact_theta_residuals':'passed','exceptional_mod4_mod16':'passed'}

def main() -> None:
    a=argparse.ArgumentParser(description='Exact common-quotient and odd-power audit; no whole-problem claim.')
    a.add_argument('--pmax',type=int,default=600)
    a.add_argument('--nmax',type=int,default=5000)
    a.add_argument('--power-nmax',type=int,default=1000)
    a.add_argument('--symbolic',action='store_true')
    args=a.parse_args()
    if args.pmax<211 or args.nmax<16 or args.power_nmax<16:a.error('pmax>=211 and both nmax>=16 required')
    result={'proof_type':'written dependent partial theorems; finite tests are self-audit',
            'quotient':quotient_audit(40),'fields':finite_field_audit(args.pmax),
            'columns':column_audit(args.nmax),'odd_gcd':power_audit(args.power_nmax),
            'tower':tower_audit(),'whole_erdos699_solved':False,'independently_reviewed':False,
            'new_Lean_verification':False}
    if args.symbolic:result['symbolic']=symbolic_audit()
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
