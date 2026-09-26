#!/usr/bin/env python3
"""Erdos 699: uniform closure of every 3-p column.

THEOREM (written proof, with an external theorem and a finite certificate).
For every prime p>=5, integers b>=0,s,t>=1, j=2^b*3^s*p^t and n>=2*j,
an odd prime divides both binomial(n,3) and binomial(n,j).
This closes that entire family, not unrestricted i=3 or all of Erdos699.
No independent review, Lean certification, or historical priority is claimed.

SOURCE AND INHERITED INTERFACE
Read #9769 at099fcb50996c20c286b9e603c705362b4c54fc2b. The inherited
single-row theorem is erdos699-single-row-check.py at a86c9013, source blob
cf02a3335ee695a591e687c579e67ef7961dacac. It implies, for a counterexample,
 n=2^N, N=1 mod6, N>=7, alpha=1+v3(N-1)>=2, D=3^alpha,
 P=p^t, Q=(n-1)/P, d=2^b, W=d*3^s, j=P*W,
 theta=(n-j)(n-j-1)/((n-1)(n-2))=x/D in lowest terms,
 D/4<x<D, 3 does not divide x, d<=2*x<2*D, Q>2*W.
In particular D<=3(N-1)/2. The present proof does NOT need the later
square-depth-check.py or the million-prime-base scan. The inherited
single-row proof uses the exact denominator-gap theorem from merged#10024;
that Lean theorem does not certify its number-theoretic premises or this
new theorem. Its statement and axiom boundary remain unchanged.

In fact the NEW uniform cofactor lemma needs only the displayed integer
interface, with arbitrary positive integers P,Q. It does not require P to
be a prime power, N to be a multiplicative order, or any binomial premise.

1. ARCHIMEDEAN GROWTH
The exact ratio equation, after n=P*Q+1,j=P*W, gives
 P*[D*(Q-W)^2-x*Q^2]=D*W-(D+x)*Q<0.
The bracket is a negative integer. Hence P<2*D*Q. Its negativity also
gives (D-x)*Q<2*D*W, so Q<2*D*W. Therefore
 2^N<8*D^3*W^2+1<32*D^5*3^(2s)+1.                  (R)
These conclusions use integrality of the ratio, not its numerical size alone.

2. THE SAME EQUATION FORCES EXCEPTIONAL 3-ADIC APPROXIMATION
Set A=D-x. Expanding exactly gives
 (n-1)*[A*n+2*x]=D*j*(2*n-1-j).
Since N is odd and3|j, n-1 is a3-unit and3 divides2*n-1-j. Thus
 v3(A*2^(N-1)+x)>=alpha+s+1.
Here gcd(A,x)=1 and both are3-units. Put gamma1=4,gamma2=(A/x)^2.
Both are1 mod3. The factor A*2^(N-1)-x is a3-unit, hence
 v3(gamma1^(N-1)*gamma2-1)>=alpha+s+1.                (V)

3. MULTIPLICATIVE DEPENDENCE IS COMPLETELY HANDLED
If gamma1,gamma2 are dependent, every odd-prime valuation of A/x is zero.
Coprimality implies {A,x}={1,2^r}. The equation3^alpha=1+2^r has only
(alpha,r)=(1,1),(2,3): for r>=3 reduction mod8 makes alpha even; the two
factors3^(alpha/2)-1 and3^(alpha/2)+1 are powers of2 with gcd2 and difference2,
so they are2,4. The cases r=1,2 are immediate. Since alpha>=2 and x>D/4,
only alpha2,x8 remains. Then gamma1^(N-1)*gamma2-1=4^(N-4)-1.
Elementary binomial lifting gives its valuation1+v3(N-4). By(V),
 3^s<=(N-4)/9 and N>=31 (s>=1).
(R) becomes2^N<23328*(N-4)^2+1, false already at31. The ratio
(2^N-1)/(N-4)^2 increases for N>=7, because its numerator grows by more
than2 and2*(N-4)^2>(N-3)^2. Thus the whole dependent branch is excluded.

4. PRECISE EXTERNAL INPUT AND UNIFORM CUTOFF
Use Bugeaud--Laurent1996 Corollary1, in the explicitly read formulation
Batte--Ddamulira--Kasozi--Luca2025, Lemma2.6, Period.Math.Hung.91,53-87,
doi:10.1007/s10998-025-00649-x. For multiplicatively independent rational
p-units gamma1,gamma2 and positive B1,B2, heights H_i>=max(h(gamma_i),log p),
common residue period g, put E'=B1/H2+B2/H1 and
 E=max(log E'+log log p+0.4,10,10 log p).
Then
 vp(gamma1^B1*gamma2^B2-1)
 <=24*p*g/((p-1)*(log p)^4)*E^2*H1*H2.               (BL)
The number-field degree is1 here. This is an external classical theorem,
not proved by the checker. The original1996 article is cited via that
checked published restatement; its full proof was not inspected here.
No hypothesis p does not divide B1 is used: that belongs to a different
specialized theorem. Our second exponent is1.

Take p3,g1,B1=N-1,B2=1,H1=log4,H2=2logD. The height of gamma2 is
2log(max(A,x))<2logD. These are valid3-units, and dependence was handled.
For N>=10^6, E'<N, log log3+0.4<1, 10log3<11<logN+1, so E<logN+1.
The exact numerical inequality72log4/(log3)^4<70 and(V) imply
 s<70*logD*(logN+1)^2<70*(logN+1)^3.                 (S)
Here logD<logN+1 follows from D<=3(N-1)/2.

Taking logarithms in(R), using log33<4, log3<11/10 and log2>2/3,
 (2/3)*N<4+5*u+154*u^3, u=logN+1.                  (T)
At N=10^6, u<15 and the right side is<519829<2000000/3.
For larger real N the three ratios1/N,u/N,u^3/N decrease; the last has
derivative u^2*(3-u)/N^2<0. Hence(T) is impossible for EVERY N>=10^6.
The new cutoff N<10^6 is independent of p,alpha,b,s,t and all their heights.
This is the crucial difference from a fixed-prime or fixed-depth cutoff.
All elementary logarithm constants are enclosed below by rational series.

5. COMPLETE TERMINAL ARITHMETIC, NO PRIME-BASE FACTORIZATION
For EVERY7<=N<10^6 with N=1 mod6, compute D=3^(1+v3(N-1)). For EVERY
integer D/4<x<D with3 not dividing x, an actual j would require the square
 E=1+4*x*(2^N-1)*(2^N-2)/D=(2*(n-j)-1)^2.
There are166666 rows and5523492(N,x) pairs, at depths2 through12. Each is
rejected by a quadratic nonresidue modulo a prime q with5<=q<=179.
All primes in this short interval are deterministically checked. The
first verifier uses Euler's criterion and updates2^N residues by multiplying
by64 at each row. A second verifier uses direct square-residue sets and
modular exponentiation. Every pair receives an actual witness; both have
identical witness streams. This is an explicit finite lemma in the proof,
not an arbitrary finite search promoted to an infinite conclusion.
The value of E is integral by binomial lifting v3(2^N-2)=1+v3(N-1).
All modular denominators are units since q is not3.
The two witness streams have SHA256
 6e81fd1795dfe799b2a0100a45d217d02dc358ac0705d1c0618849ef9b5b82b5.
Hashes are binding checks, not substitutes for redoing the arithmetic.
Together with the uniform bound this excludes the entire integer interface,
and the inherited single-row reduction proves the stated 3-p theorem.

FORMALIZATION HANDOFF
(a) The exact cofactor residual and negative integer coefficient yield(R).
(b) The original ratio residual yields(V) via valuations and two3-units.
(c) gcd(A,x)=1,A+x=3^alpha proves the dependence dichotomy above.
(d) A generic application of(BL) plus the documented rational constants
    yields N<10^6. Do not add an unproved private Lean axiom for(BL).
(e) The finite universal square predicate is decidable integer arithmetic.
(f) Compose with the inherited single-row theorem only when its premises
    have separately been formalized. #10024 alone is insufficient.
No Lean source, frozen theorem, resolution counter, or CI rule is changed.

REMAINING ORIGINAL PROBLEM
This is NOT all i=3: two odd-prime columns without3 and general multi-prime
endpoints remain beyond previously covered sectors. Also remaining are
indices4..324; the inherited i>=325 region is unchanged. The present new
proof requires independent review of its inherited premises and external
bound specialization. Regression counts are not a completion percentage.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
import json
from math import comb, gcd, isqrt

LIMIT = 1_000_000
WITNESS_HASH = '6e81fd1795dfe799b2a0100a45d217d02dc358ac0705d1c0618849ef9b5b82b5'


def primes(limit: int) -> list[int]:
    return [p for p in range(5, limit+1)
            if all(p % d for d in range(2, isqrt(p)+1))]


def vp(a: int, p: int) -> int:
    if a == 0 or p < 2:
        raise ValueError('nonzero integer and p>=2 required')
    a, e = abs(a), 0
    while a % p == 0:
        a //= p
        e += 1
    return e


def vpq(a: F, p: int) -> int:
    return vp(a.numerator, p)-vp(a.denominator, p)


def small_log_bounds(x: F, terms: int = 32) -> tuple[F, F]:
    if not 1 <= x <= 2:
        raise ValueError('x must be in [1,2]')
    z = (x-1)/(x+1)
    low = 2*sum((z**(2*k+1)/F(2*k+1) for k in range(terms)), F(0))
    tail = 2*z**(2*terms+1)/(F(2*terms+1)*(1-z*z))
    return low, low+tail


def log_bounds(n: int) -> tuple[F, F]:
    if n < 1:
        raise ValueError('positive n required')
    k = n.bit_length()-1
    l, u = small_log_bounds(F(n, 1 << k))
    l2, u2 = small_log_bounds(F(2))
    return l+k*l2, u+k*u2


def constant_audit() -> dict:
    l2, u2 = log_bounds(2)
    l3, u3 = log_bounds(3)
    _, u33 = log_bounds(33)
    lM, uM = log_bounds(LIMIT)
    assert l2 > F(2, 3) and 2*l2 > 1
    assert l3 > 1 and u3 < F(11, 10) and u33 < 4
    assert 72*2*u2/l3**4 < 70
    assert lM > 10 and uM < 14
    # log(log3)<log(1.1)<0.1 follows from log(1+t)<t.
    assert F(1,10)+F(2,5) < 1
    terminal = 4+5*15+154*15**3
    assert terminal == 519829 and 3*terminal < 2*LIMIT
    assert (1 << 31)-1 > 23328*(31-4)**2
    assert 3**13 > 3*(LIMIT-1)//2
    dependent = []
    for alpha in range(2, 13):
        D = 3**alpha
        for x in range(D//4+1, D):
            if x % 3 and x & (x-1) == 0 and (D-x) & (D-x-1) == 0:
                dependent.append((alpha,x))
    assert dependent == [(2,8)]
    for N in range(31, 201):
        assert 2*(N-4)**2 > (N-3)**2
        if N % 2:
            assert vp(pow(4,N-4)-1,3) == 1+vp(N-4,3)
    return {'rational_log_constants':'passed',
            'tail_cutoff':LIMIT, 'tail_upper_at_cutoff':terminal,
            'dependent_branch_first_impossible_N':31,
            'dependent_controls':dependent}


def finite_certificate(engine: str) -> dict:
    if engine not in ('euler','squares'):
        raise ValueError('unknown engine')
    ps = primes(179)
    if engine == 'euler':
        tables = {p:[pow(r,(p-1)//2,p) != p-1 for r in range(p)] for p in ps}
        residue = {p:pow(2,7,p) for p in ps}
    else:
        tables = {p:{r*r % p for r in range(p)} for p in ps}
    digest = sha256()
    rows = total = 0
    depth_counts: Counter = Counter()
    first_counts: Counter = Counter()
    for N in range(7, LIMIT, 6):
        alpha = 1+vp(N-1,3)
        D = 3**alpha
        assert D <= 3*(N-1)//2
        assert pow(2,N,3*D) % D == 2 and pow(2,N,3*D) != 2
        tests = []
        for p in ps:
            z = residue[p] if engine == 'euler' else pow(2,N,p)
            inverse = pow(D,p-2,p) if engine == 'euler' else pow(D,-1,p)
            assert D*inverse % p == 1
            if z not in (1,2):
                tests.append((p,4*(z-1)*(z-2)*inverse % p,tables[p]))
        count = 0
        for x in range(D//4+1,D):
            if x % 3 == 0:
                continue
            for p,c,table in tests:
                e = (1+c*x) % p
                nonresidue = not table[e] if engine == 'euler' else e not in table
                if nonresidue:
                    first_counts[p] += 1
                    digest.update(f'{N},{x},{p}\n'.encode())
                    break
            else:
                raise AssertionError(f'unexcluded necessary square: {(N,D,x)}')
            count += 1
        rows += 1
        total += count
        depth_counts[alpha] += count
        if engine == 'euler':
            for p in ps:
                residue[p] = 64*residue[p] % p
    assert rows == 166666 and total == 5523492
    assert digest.hexdigest() == WITNESS_HASH
    return {'engine':engine, 'N_upper_exclusive':LIMIT, 'rows':rows, 'pairs':total,
            'pairs_by_depth':dict(sorted(depth_counts.items())),
            'first_witness_counts':dict(sorted(first_counts.items())),
            'witness_sha256':digest.hexdigest(), 'survivors':0,
            'max_witness_prime':max(first_counts)}


def algebra_audit() -> dict:
    cofactor = valued = 0
    for P in range(1,22,2):
        for b in range(4):
            for s in range(1,4):
                d = 1 << b
                W = d*3**s
                for Q in range(2*W+1,2*W+14,2):
                    n,j = P*Q+1,P*W
                    theta = F((n-j)*(n-j-1),(n-1)*(n-2))
                    x,D = theta.numerator,theta.denominator
                    K = D*(Q-W)**2-x*Q*Q
                    assert P*K == D*W-(D+x)*Q < 0 and K <= -1
                    assert P < 2*D*Q and (D-x)*Q < 2*D*W
                    assert Q < 2*D*W and n < 8*D**3*W**2+1
                    # Non-dyadic rational controls; NOT original counterexamples.
                    cofactor += 1
    for N in range(3,100,2):
        n = 1 << N
        for j in range(6,min(150,n//2)+1,3):
            theta = F((n-j)*(n-j-1),(n-1)*(n-2))
            x,D = theta.numerator,theta.denominator
            A = D-x
            if A <= 0:
                continue
            assert (n-1)*(A*n+2*x) == D*j*(2*n-1-j)
            assert gcd(A,x)==1 and x%3 and A%3
            gamma = F(A*A,x*x)*pow(4,N-1)-1
            assert gamma != 0
            assert vpq(gamma,3)==vp(D,3)+vp(j,3)+vp(2*n-1-j,3)
            assert vpq(gamma,3)>=vp(D,3)+vp(j,3)+1
            valued += 1
    # Earlier fixed-period blind spot is genuinely caught in the new finite box.
    N,D,x = 973,729,184
    witnesses=[]
    for p in primes(179):
        z=pow(2,N,p)
        e=(1+4*x*(z-1)*(z-2)*pow(D,-1,p))%p
        if pow(e,(p-1)//2,p)==p-1:
            witnesses.append(p)
    assert witnesses
    return {'nonempty_rational_cofactor_controls':cofactor,
            'nonempty_three_adic_identity_controls':valued,
            'old_fixed_period_blind_spot_new_witnesses':witnesses}


def carry_count(n: int,j: int,p: int) -> int:
    a,b,carry,result = j,n-j,0,0
    while a or b or carry:
        carry=(a%p+b%p+carry)//p
        result+=carry
        a//=p
        b//=p
    return result


def vp_binom(n: int,j: int,p: int) -> int:
    result,q=0,p
    while q<=n:
        result+=n//q-j//q-(n-j)//q
        q*=p
    return result


def regression(nmax: int) -> dict:
    ps = [3]+primes(nmax)
    columns=set()
    for p in ps:
        if p==3:
            continue
        P=p
        while 6*P<=nmax:
            odd=3*P
            while 2*odd<=nmax:
                j=odd
                while 2*j<=nmax:
                    columns.add(j)
                    j*=2
                odd*=3
            P*=p
    pairs=direct=0
    for j in sorted(columns):
        for n in range(2*j,nmax+1):
            cn3=n*(n-1)*(n-2)//6
            for p in ps:
                if cn3%p==0 and vp_binom(n,j,p)>0:
                    assert carry_count(n,j,p)==vp_binom(n,j,p)
                    if n<=300:
                        assert comb(n,j)%p==0
                        direct+=1
                    break
            else:
                raise AssertionError((n,j))
            pairs+=1
    return {'nmax':nmax,'columns':len(columns),'original_pairs':pairs,
            'direct_binomial_checks':direct,'regression_is_proof':False}


def symbolic_audit() -> dict:
    import sympy as S
    n,j,D,x,P,Q,W,A,z=S.symbols('n j D x P Q W A z')
    ratio=D*(n-j)*(n-j-1)-x*(n-1)*(n-2)
    residual=(n-1)*((D-x)*n+2*x)-D*j*(2*n-1-j)
    assert S.expand(ratio-residual)==0
    cofactor=P*(D*(Q-W)**2-x*Q**2)-D*W+(D+x)*Q
    assert S.expand(ratio.subs({n:P*Q+1,j:P*W})-P*cofactor)==0
    assert S.expand((A*z)**2-x*x-(A*z-x)*(A*z+x))==0
    r=S.symbols('r',positive=True)
    u=S.log(r)+1
    assert S.simplify(S.diff(u**3/r,r)-u*u*(3-u)/r**2)==0
    assert S.simplify(S.diff(u/r,r)+S.log(r)/r**2)==0
    return {'ratio_to_valuation_identity':True,'cofactor_identity':True,
            'difference_of_squares':True,'tail_monotonicity_derivatives':True}


def main() -> None:
    parser=argparse.ArgumentParser(description='Uniform 3-p closure proof certificate.')
    parser.add_argument('--cross-check',action='store_true')
    parser.add_argument('--symbolic',action='store_true')
    parser.add_argument('--nmax',type=int,default=1000)
    args=parser.parse_args()
    if args.nmax<30:
        parser.error('--nmax must be at least30')
    out={'theorem_scope':'all i=3 columns j=2^b*3^s*p^t; p>=5,s,t>=1,b>=0',
         'external_input':'Bugeaud-Laurent1996, published rational restatement in BD KL2025 Lemma2.6',
         'constants':constant_audit(),'algebra':algebra_audit(),
         'finite_certificate':finite_certificate('euler'),
         'regression':regression(args.nmax),
         'unrestricted_erdos699_solved':False,'independent_review':False,
         'external_logarithm_theorem_reproved':False}
    if args.cross_check:
        other=finite_certificate('squares')
        assert all(out['finite_certificate'][k]==other[k] for k in other if k!='engine')
        out['independent_arithmetic_engine']=other
    if args.symbolic:
        out['symbolic']=symbolic_audit()
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    main()
