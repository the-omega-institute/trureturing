#!/usr/bin/env python3
"""Erdos 699: synchronized nonzero fourth-character phases.

CONTINUITY. Issue #9670 / PR #9769, read head
69acdc55ce0e68b7ce974b9ed9d81b2ab1094122. This is a written partial theorem
with exact self-audits, not a Lean-certified or independently reviewed
proof of unrestricted Erdos699. No historical-priority claim is made.

THEOREM. Let S be a finite set of primes all in ONE class r=5 or13 mod24.
For p in S and a prime-to-p integer z, define phi_p(z) in Z/4 by
 z^((p-1)/4) = (2^((p-1)/4))^phi_p(z) modp.
Assume that for each q in S there is lambda_q in Z/4 such that
 phi_p(q)=lambda_q for EVERY p in S other than q.
The lambda_q need not vanish or even be equal to each other.
Then every j=2^b*product(q^e_q), b,e_q>=0, j>=4, satisfies the original
 i=3 conclusion for ALL n>=2j: some odd prime divides both C(n,3),C(n,j).
There is no bound on |S|, the exponents, n, or gcd(n,j).

EXAMPLES. S=(5,53,173,10733) has every off-diagonal entry3. Every pair is
therefore a quadratic NONresidue, not merely a non-fourth-power residue.
S=(13,37,1597) also has all entries3. S=(5,29,1301,18701) has the constant
columns (2,2,0,0). These supports are outside the previous mutual-fourth-
residue premise. Only the finite eligibility checks use these numbers;
the whole-column theorem has the abstract quantified premise above.
No existence of arbitrarily large such supports is claimed.

INHERITED ARITHMETIC, PRECISELY SEPARATED FROM THE NEW GROUP ARGUMENT.
Under an original i=3 counterexample H, the deposited normal form and
mixed-support lemmas give d=gcd(n,j), n=c*2^a*d with c=1 or3,a>=2.
Write d=2^b*e, e odd. Then n=c*2^N*e with N=a+b, and v2(j)=b.
There is a prime P|j with P|n-1 and a prime R|j outside n(n-1).
For theta=(n-j)(n-j-1)/((n-1)(n-2))=x/y reduced, 0<theta<1 and y|3z,
where every prime of z divides j but divides neither n nor n-1.
These premises are in the original normalized-cubic and mixed-support
proofs; this script does not independently certify them. The present
proof uses neither the later uniform3-p logarithm theorem nor its scan.
Source: docs/develop/theory/ERDOS_699_BINOMIAL_COMMON_PRIME.md sections2-5;
tools/scripts/agent/openproblem/erdos699-mixed-support-check.py.

1. ACTUAL FORMAL GROUP-THEORY CONNECTION.
Read dev D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.lean,
blob79c32483be14a2333e043f151744877c4ea30fb8. Its verified-source statements
are power_character_joint_kernel_eq_power_subgroup,
power_quotient_has_exponent_dividing, and
power_subgroup_le_iff_quotient_pow_eq_one. They give the power subgroup
and its universal quotient, but NOT the new original-parameter theorem.
The source was read, not recompiled in this environment.
Also read Erdos699DenominatorGap.lean, blob982eb26f0fcd5b1363961f8023f2558bee790855.
That inequality and its registration are unchanged, and are NOT extra
premises of this new argument. No fresh arithmetic result is inferred
from the registration PR #10249.

For p=5 mod8, Gauss counting gives 2^((p-1)/2)=-1. Thus u_p=2^((p-1)/4)
has exact order4. Fermat implies each z^((p-1)/4) is one of its4 powers,
so phi_p is a well-defined homomorphism to additive Z/4. Its kernel is
(F_p^*)^4 (by cyclicity of the finite-field unit group), phi_p(2)=1 and
phi_p(-1)=2. Reduction mod2 is the Legendre character.
For primes in class5 or13 mod24, Legendre(3,p) is respectively -1 or+1.
These signs follow from the elementary Gauss counts for multipliers2,3:
 (p-1)/2-floor(p/4) and floor(p/3)-floor(p/6), respectively.
No noncanonical cyclic isomorphism is allowed to change the label2.

2. THE DIAGONAL REPLACES THE ZERO SUBGROUP.
For a nonempty active set U of primes, put V=(Z/4)^U and
 Diag={ (lambda)_p : lambda in Z/4 }.
Fix p0 in U. The map v -> (v_p-v_p0)_(p!=p0) is onto, with kernel Diag;
hence V/Diag is isomorphic to (Z/4)^(|U|-1).
For any homomorphism Psi into V, the inverse image of Diag is the
intersection of the kernels of these DIFFERENCE characters. Therefore
it is a subgroup and contains all products/powers of its generators.
This is an elementary diagonal-kernel lemma, not a new discovery of
finite-abelian duality. The new application retains common NONZERO phases.

3. LOCAL SYNCHRONIZATION LEMMA.
Assume all odd primes of j are in one of the same classes5,13. It suffices
that phi_p(e)=lambda have the SAME value at every active p|j,p not|d.
It need not be0. All field maps are only used where e is a unit.
Under H there are at least two active primes, by the two distinct roles.
Since p>=5, p not|d is equivalent to p not|n.

For c1, put nu=N+lambda in Z/4. At P|n-1 the character gives nu=0.
An active endpoint prime dividing n-2 would instead give nu=1. Thus none
exists. The denominator condition y|3z and its original denominator now
give y|3 (3 does not divide j or z), so theta=1/3 or2/3.
For theta1/3 the exact residual identity is
 2(n-1)(n+1)=3j(2n-1-j).
At the external endpoint prime R>=5 this forces R|n+1, hence nu=phi_R(-1)=2,
contradicting nu0.
For theta2/3 the residual is (n-1)(n+4)=3j(2n-1-j). A quartic character
alone cannot reject this: phi_R(-4)=0. Retain the original integer equation
 3(n-j)(n-j-1)=2(n-1)(n-2).
All endpoint odd primes are1 mod4, so oddpart(j)=1 mod4. If b=0, this
reads2=0 mod4. If b>0, N>=b+2 makes the valuations of the two sides b and2,
so b=2. NOW N>=4 follows from a>=2, NOT from nu=0. Thus n=0 mod16,j=4 mod16,
and the equality reads12=4 mod16. This handles the nonzero-phase case
without falsely inferring4|N from N+lambda=0.

For c3, use the square characters. Let sigma be the common Legendre(3,p).
For every active p, Legendre(n,p)=sigma*(-1)^(N+lambda). The n-1 role P
forces it to be1, while any n-2 endpoint prime would force it to be-1.
So none exists. But the raw theta denominator is prime to3, y>1 and y|3z;
a prime of y must be an active endpoint prime dividing n-2, a contradiction.
This closes both c branches and proves the local lemma.

4. ALL GCD ALLOCATIONS, WITHOUT ENUMERATION.
Fix an arbitrary n and j supported on S. Let T be the prime support of e
and U the active primes. They are disjoint, so for every p in U,
 phi_p(e)=sum_(q in T) v_q(e)*phi_p(q)
         =sum_(q in T) v_q(e)*lambda_q =lambda, independent of p.
The local lemma applies. Empty or one-element U is already incompatible
with the two inherited distinct prime roles. Missing exponents e_q=0
cause no issue. This proves the whole-support theorem.
Equivalently each shared-prime vector lies in Diag, and all products stay
there. Previous mutual-fourth-residue supports had only the zero vector.
Here the much larger diagonal is annihilated after synchronizing N.

5. STRICTNESS AND FORMALIZATION HANDOFF.
For S=(5,53,173,10733), j=492054385 and n=5*2^N for every N>=28,
d=gcd(n,j)=5. At each active prime phi_p(e)=3, so e is a quadratic
nonresidue and violates the old local-kernel premise. Synchronization is
nevertheless exact. This is an infinite comparison of TWO named criteria,
not a claim that every previous theorem fails on those pairs.
For arbitrary supports the difference matrix A_(p,q)=phi_p(q)-phi_p0(q)
provides an exponent-dependent sufficient condition A*f=0 mod4, with
f_q=v_q(e). The column-constant hypothesis makes it hold for ALL f.
A matrix failing this condition is not a counterexample to Erdos699.

Formalize separately: labelled finite-field characters; diagonal-kernel
identity; synchronized-phase arithmetic lemma with explicit inherited
hypotheses; then the finite-product corollary. There is no claim that a
character equality in one field identifies the elements of another field.
No private Lean axiom or new Lean file is introduced.

BOUNDARY. General non-synchronized supports, unrestricted i3 and i4..324
remain beyond this result. Existing i>=325 and earlier analytic results
retain their recorded status. No full-problem, CI or independent-review
claim is made. Tests below are exact self-audits; finite example eligibility
is elementary modular arithmetic, not an unbounded proof by sampling.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
import json
from math import comb, gcd, isqrt, prod


@lru_cache(None)
def factors(n: int) -> tuple[tuple[int, int], ...]:
    if n < 1:
        raise ValueError('positive factor input required')
    out = []
    p = 2
    while p*p <= n:
        k = 0
        while n % p == 0:
            k += 1
            n //= p
        if k:
            out.append((p, k))
        p = 3 if p == 2 else p+2
    if n > 1:
        out.append((n, 1))
    return tuple(out)


@lru_cache(None)
def prime(p: int) -> bool:
    return p >= 2 and all(p % q for q in range(2, isqrt(p)+1))


def v2(n: int) -> int:
    if n <= 0:
        raise ValueError('positive valuation input required')
    return (n & -n).bit_length()-1


def oddpart(n: int) -> int:
    return n >> v2(n)


@lru_cache(None)
def phase(p: int, z: int) -> int:
    if p % 24 not in (5, 13) or not prime(p) or z % p == 0:
        raise ValueError('eligible prime and nonzero residue required')
    h = (p-1)//4
    u, w = pow(2, h, p), pow(z, h, p)
    assert u*u % p == p-1
    for a in range(4):
        if pow(u, a, p) == w:
            return a
    raise AssertionError('fourth-root image not found')


@lru_cache(None)
def fourth_powers(p: int) -> frozenset[int]:
    return frozenset(pow(t, 4, p) for t in range(1, p))


def support_labels(S: tuple[int, ...]) -> tuple[int, ...] | None:
    if not S or len(set(S)) != len(S) or not all(prime(p) for p in S):
        return None
    r = S[0] % 24
    if r not in (5, 13) or any(p % 24 != r for p in S):
        return None
    labels = []
    for q in S:
        col = {phase(p, q) for p in S if p != q}
        if len(col) > 1:
            return None
        labels.append(next(iter(col)) if col else 0)
    return tuple(labels)


def vp_binom(n: int, j: int, p: int) -> int:
    ans, power = 0, p
    while power <= n:
        ans += n//power - j//power - (n-j)//power
        power *= p
    return ans


def carries(n: int, j: int, p: int) -> int:
    x, y, carry, ans = j, n-j, 0, 0
    while x or y or carry:
        carry = (x % p + y % p + carry)//p
        ans += carry
        x //= p
        y //= p
    return ans


def witness(n: int, j: int, candidates=None) -> int:
    if candidates is None:
        candidates = sorted({p for a in (n, n-1, n-2) for p, _ in factors(a) if p > 2})
    cn3 = n*(n-1)*(n-2)//6
    for p in candidates:
        if cn3 % p == 0 and vp_binom(n, j, p):
            assert prime(p)
            assert vp_binom(n, 3, p) > 0
            assert carries(n, j, p) == vp_binom(n, j, p)
            if n <= 200:
                assert comb(n, j) % p == 0
            return p
    raise AssertionError(('no witness in tested list', n, j))


def diagonal_audit() -> dict:
    cases = shifts = 0
    for k in range(2, 7):
        for size in range(1, 5):
            images = set()
            for v in product(range(k), repeat=size):
                image = tuple((t-v[0]) % k for t in v[1:])
                assert (not any(image)) == (len(set(v)) == 1)
                images.add(image)
                for t in range(k):
                    shifted = tuple((a+t) % k for a in v)
                    assert tuple((a-shifted[0]) % k for a in shifted[1:]) == image
                    shifts += 1
                cases += 1
            assert len(images) == k**(size-1)
    return {'element_vectors': cases, 'diagonal_shift_checks': shifts}


def example_audit() -> dict:
    examples = [((5, 53, 173, 10733), (3, 3, 3, 3)),
                ((13, 37, 1597), (3, 3, 3)),
                ((5, 29, 1301, 18701), (2, 2, 0, 0))]
    edges = monomials = common_nonzero = common_odd = 0
    records = []
    for S, expected in examples:
        assert support_labels(S) == expected
        table = []
        for p in S:
            row = []
            rp = fourth_powers(p)
            assert len(rp) == (p-1)//4
            for q in S:
                if q == p:
                    row.append(None)
                    continue
                a = phase(p, q)
                # Independent test via enumerating every fourth-power residue.
                assert [t for t in range(4) if q*pow(pow(2,t,p),-1,p) % p in rp] == [a]
                row.append(a)
                edges += 1
            table.append(row)
        for length in range(len(S)-1):
            for T in combinations(S, length):
                U = tuple(p for p in S if p not in T)
                for exps in product(range(1, 5), repeat=length):
                    e = prod(q**f for q, f in zip(T, exps))
                    lam = sum(expected[S.index(q)]*f for q, f in zip(T, exps)) % 4
                    assert {phase(p, e) for p in U} == {lam}
                    assert all(pow(e, (p-1)//2, p) == (1 if lam%2 == 0 else p-1) for p in U)
                    monomials += 1
                    common_nonzero += lam != 0
                    common_odd += lam % 2
        records.append({'support': S, 'column_labels': expected, 'phase_matrix': table})
    assert support_labels((5, 29, 53)) is None
    assert phase(29, 5) == 2 and phase(53, 5) == 3
    j = prod(examples[0][0])
    assert j == 492054385 and 5*(1<<28) >= 2*j
    assert gcd(j, 5*(1<<28)) == 5
    assert all(phase(p, 5) == 3 for p in examples[0][0] if p != 5)
    return {'examples': records, 'ordered_edge_checks': edges,
            'shared_monomial_cases': monomials, 'nonzero_common_phase_cases': common_nonzero,
            'odd_common_phase_cases': common_odd, 'failed_column_condition_control': [5,29,53]}


def arithmetic_audit(nmax: int) -> dict:
    residuals = two_thirds = 0
    for n in range(8, nmax+1):
        for j in range(4, n//2+1):
            m = n-j
            assert 3*m*(m-1)-(n-1)*(n-2) == 2*(n-1)*(n+1)-3*j*(2*n-1-j)
            assert 3*m*(m-1)-2*(n-1)*(n-2) == (n-1)*(n+4)-3*j*(2*n-1-j)
            residuals += 1
            if v2(n) < v2(j)+2 or oddpart(j) % 4 != 1:
                continue
            L, R = 3*m*(m-1), 2*(n-1)*(n-2)
            b = v2(j)
            if b == 0:
                assert L % 4 == 2 and R % 4 == 0
            elif b != 2:
                assert v2(L) == b and v2(R) == 2
            else:
                assert n % 16 == 0 and j % 16 == 4
                assert L % 16 == 12 and R % 16 == 4
            assert L != R
            two_thirds += 1
    # Dropping oddpart(j)=1 mod4 can make the actual theta equality true.
    assert Fraction((56-11)*(56-11-1), 55*54) == Fraction(2, 3)
    assert oddpart(11) % 4 == 3
    return {'ratio_residual_pairs': residuals, 'two_thirds_exclusions': two_thirds,
            'missing_oddpart_condition_control': [56, 11]}


def local_pair_audit(nmax: int) -> dict:
    counts = Counter()
    for j in range(4, nmax//2+1):
        S = tuple(p for p, _ in factors(j) if p > 2)
        if not S or S[0] % 24 not in (5, 13) or any(p%24 != S[0]%24 for p in S):
            continue
        for n in range(2*j, nmax+1):
            d = gcd(n, j)
            e = oddpart(d)
            U = tuple(p for p in S if d % p)
            phases = {phase(p, e) for p in U}
            if len(phases) > 1:
                continue
            witness(n, j)
            counts['synchronized_original_pairs'] += 1
            if len(U) >= 2:
                counts['at_least_two_active_primes'] += 1
                if phases != {0}:
                    counts['nonzero_phase_pairs_not_old_local_kernel'] += 1
    counts.setdefault('nonzero_phase_pairs_not_old_local_kernel', 0)
    return dict(counts)


def targeted_audit() -> dict:
    rows = []
    small_primes = [p for p in range(3, 2000, 2) if prime(p)]
    for S in ((5,53,173,10733),(13,37,1597),(5,29,1301,18701)):
        j = prod(S)
        for d in (S[0], S[1], S[0]*S[1]):
            if len(S) == 3 and d == S[0]*S[1]:
                continue
            N = 2
            while d*(1<<N) < 2*j:
                N += 1
            for c in (1,3):
                for extra in (0,1,4):
                    n = c*d*(1<<(N+extra))
                    assert gcd(n,j) == d
                    U = [p for p in S if d%p]
                    phases = {phase(p,d) for p in U}
                    assert len(phases) == 1
                    p = witness(n,j,small_primes)
                    rows.append({'S':S,'n':n,'j':j,'d':d,'common_phase':next(iter(phases)),
                                 'common_prime':p})
    return {'original_pairs':len(rows),'nonzero_phase_pairs':sum(row['common_phase']!=0 for row in rows),
            'all_rows':rows}


def main() -> None:
    parser = argparse.ArgumentParser(description='Exact self-audit for diagonal character synchronization.')
    parser.add_argument('--nmax',type=int,default=1200)
    args = parser.parse_args()
    if args.nmax < 8:
        parser.error('--nmax must be at least8')
    report = {'scope':'written i=3 support theorem; nonzero synchronized phases allowed',
              'diagonal':diagonal_audit(),'examples':example_audit(),
              'arithmetic':arithmetic_audit(min(args.nmax,400)),
              'local_pairs':local_pair_audit(args.nmax),'targeted':targeted_audit(),
              'unbounded_proof_by_sampling':False,'lean_verified_here':False,
              'independent_review':False,'whole_erdos699_solved':False}
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
