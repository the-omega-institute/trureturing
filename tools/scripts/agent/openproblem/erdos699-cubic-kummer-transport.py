#!/usr/bin/env python3
r"""# Erdős 699: cubic transport with arbitrary quadratic sign patterns

Continuation of issue #9670 / Draft PR #9769, read at
`2923594d4f5f66ccd0735b7297f030f8cf22975b`.

These are written partial theorems. The original-binomial conclusions use
explicitly inherited normal-form and mixed-support lemmas. Their independent
review and full formalization remain separate obligations. No full Erdős 699
solution, Lean certification, CI success, or historical priority is claimed.

## 1. Statements and actual advance

Call a finite set S of primes cubically admissible when every p in S satisfies

* p = 13 modulo 24;
* 2 is not a cube in F_p^*, and 3 is a cube;
* for every distinct p,q in S, q is a cube in F_p^*.

THEOREM A. For every such S, all integers

    j = 2^b product_(p in S) p^a_p >= 4,  b,a_p >= 0,

satisfy the original i=3 assertion for every n>=2j: an odd prime divides
both binomial(n,3) and binomial(n,j). The number of support primes, all
exponents, n and gcd(n,j) are unrestricted. The new transport deduction needs no
Chebotarev theorem or analytic estimate and has no new finite-search lemma;
inherited premises retain their own proof and review boundaries.

THEOREM B. Fix an admissible S of size m and prescribe independently any
sign epsilon_p in {+1,-1} for each p in S. There are infinitely many primes
q>max(S) for which S union {q} is still cubically admissible and

    Legendre(q,p) = Legendre(p,q) = epsilon_p,  p in S.

In fact the set of all such extensions (ignoring finitely many excluded
primes) has Dirichlet density 1/(36*18^m) among rational primes. The
existence and density use the classical Chebotarev theorem. The field
intersection and degree computations needed for this application are
proved below, rather than presuming independence of residue conditions.

COROLLARY. Every prescribed symmetric sign pattern on countably many
labelled vertices can be realized by an increasing prime sequence whose
all finite subsets are admissible. Every integer>=4 supported on 2 and a
finite subset of that sequence is an i=3 column covered by Theorem A.
A realization of a sign graph is not a theorem about every GIVEN prime
set with that graph. Cubic admissibility remains essential.

Example S=(661,853,2389) has quadratic signs (+1,+1,-1) on its three edges.
Thus all columns 2^b*661^s*853^t*2389^u are covered, including all positive
odd-prime exponents and arbitrary gcd. This is outside the preceding
homogeneous-quadratic-support hypothesis. At e=853 the active primes 661
and 2389 see opposite quadratic signs, while both cubic characters kill e.

## 2. Precise inherited original-parameter interface

For a hypothetical i=3 counterexample with 3<j<=n/2 and all odd primes of j
at least 5, the deposited normal-form/mixed-support chain supplies:

    d=gcd(n,j)=2^b*e, e odd, v2(j)=b;
    n=c*2^N*e, c in {1,3}, N>=b+2;
    an endpoint prime P|j,n-1;
    another endpoint prime R|j with R not dividing n(n-1);
    theta=(n-j)(n-j-1)/((n-1)(n-2))=x/y reduced, 0<theta<1;
    y|3z, every prime of z divides j but not n(n-1).

Only primes p|j with p not dividing d are used as field coordinates.
For these primes e is a unit and, since p>=5, p does not divide n.
The two distinct prime roles rule out fewer than two active primes.
Source interfaces: the main theory sections 2-5 and
`erdos699-mixed-support-check.py`, also explicitly retained in
`erdos699-quadratic-collapse-check.py`. The latter's standalone gcd
identity is proved again here. The present checker does not certify this
inherited chain from the definition of binomial coefficients.

## 3. Two observation layers, with arithmetic between them

LOCAL LEMMA. Suppose every odd prime of j is 5 modulo 8. At every active
prime p suppose there is a homomorphism

    phi_p: F_p^* -> Z/h, h>=2,

with phi_p(2)=1, phi_p(3)=tau, phi_p(e)=lambda, where h,tau,lambda are
common to all active coordinates. Then the original pair cannot be a
counterexample. Values tau and lambda need not be zero.

For c=1 or 3, phi_p(n) is the same value nu=N+lambda or N+lambda+tau.
The P|n-1 role forces nu=0. Any active prime of n-2 would force nu=1.
Consequently no endpoint prime divides n-2. This is the first observation
layer; its target group need not have order a power of 2.

If c=3, the original denominator (n-1)(n-2) is prime to 3. Since y>1 and
y|3z, a prime of y would be an active endpoint prime dividing n-2. This
contradicts what was just proved.

If c=1, every prime of y other than 3 would likewise give that forbidden
role. Since 3 does not divide j or z, y divides 3. Thus theta=1/3 or 2/3.
For any exact equation D(n-j)(n-j-1)=x(n-1)(n-2), reduction modulo d gives

    d | 2x.

Hence these two ratios force d|2 or d|4; in either case e=1 and n=2^N.
This is an exact arithmetic rank collapse, not removal of a legal group
generator just to make a quotient obstruction easier.

At every prime p=5 mod8, 2^((p-1)/2)=-1 and p-1=4m with m odd. Therefore
v2(ord_p(2))=2. This supplies a SECOND observation layer after e disappears.

For theta=1/3 the exact residual is

    2(n-1)(n+1)=3j(2n-1-j).

P|n-1 implies 4|N. The external prime R>=5 must divide n+1. Since 2 has
order 4 times an odd number modulo R, 2^N=-1 forces N=2 modulo4. Contradiction.

For theta=2/3 use the exact equation

    3(n-j)(n-j-1)=2(n-1)(n-2).

All odd primes of j are1 mod4, so oddpart(j)=1 mod4. If b=0 the equality
reads2=0 modulo4. If b>0, its two 2-adic valuations are b and2, using
N>=b+2, so b=2. Now N>=4; n=0,j=4 modulo16. The equation reads12=4 modulo16.
This exhausts the special cases and proves the local lemma.

For Theorem A take h=3. Set u_p=2^((p-1)/3). It has exact order3 because
2 is not a cube. Every z^((p-1)/3) is a unique u_p power; write that
exponent as phi_p(z). This is a homomorphism with kernel (F_p^*)^3 and
phi_p(2)=1. Admissibility gives phi_p(3)=0. Every prime factor of e belongs
to S minus {p}, hence is a cube at p. The power subgroup is closed under
products and powers, so phi_p(e)=0 for every active p. Apply the local
lemma with tau=lambda=0. This proves A for all gcd allocations at once.
The quadratic symbols of these factors are irrelevant to this first layer.

## 4. Radical independence: a norm argument instead of assumed disjointness

Write S={p_1,...,p_m}, K=Q(zeta_3), and

    L=K(cuberoot(2), cuberoot(3), cuberoot(p_1),...,cuberoot(p_m)).

Use positive real cube roots. Let r=m+2 and a_1,...,a_r be the distinct
rational primes 2,3,p_1,...,p_m.

Their classes are independent in K^*/(K^*)^3. Indeed if product a_i^e_i
is a cube z^3 in K, with e_i in {0,1,2}, its norm to Q gives

    product a_i^(2e_i) = Norm_(K/Q)(z)^3.

Rational prime valuations force 3|2e_i, hence every e_i=0. This also
handles the ramified prime3, without an unproved ramification shortcut.

L/K is a finite Galois splitting field. Each automorphism sends a_i^(1/3)
to zeta_3^v_i a_i^(1/3), giving an injection Gal(L/K)->(F_3)^r. If its
image were proper, a nonzero linear functional e would annihilate it.
Then product a_i^(e_i/3) would be fixed by the whole Galois group, hence
belong to K. Its cube contradicts the norm independence. Therefore

    Gal(L/K) = V = (C3)^r,       [L:K]=3^r.

This proves the needed multiradical rank directly. It is not an inference
from the existence of separate cyclic cubic extensions.

## 5. The nonabelian group makes the two residue specifications compatible

Complex conjugation tau fixes the real cube roots and inverts zeta_3.
Consequently

    Gal(L/Q) = V semidirect C2,  tau*sigma_v*tau^-1 = sigma_(-v).

In multiplicative commutator notation [tau,sigma_v]=sigma_(-2v)=sigma_v,
because V has exponent3. The commutator subgroup is therefore exactly V;
the reverse inclusion follows since the quotient by V is abelian C2.
It follows that the maximal abelian subextension of L/Q is exactly K.

Let M=24*product p_i and F=Q(zeta_M). F/Q is abelian and contains K, so

    L intersect F = K.

Indeed the intersection is an abelian subextension of L and must lie in K.
This proves the intersection before combining local conditions. In
particular the quadratic residue choices in F do not force additional
relations among the radical automorphisms in V.

The restriction map identifies Gal(LF/Q) with the fiber product over Gal(K/Q),
and its order is

    3^(m+2) * phi(M) = 3^(m+2)*8*product(p_i-1).

The classical group here is a generalized dihedral group. Neither its
semidirect description nor Chebotarev's theorem is claimed as a new fact.
The new use is to preserve the binomial exclusion while allowing ANY
prescribed quadratic sign vector at each extension step.

## 6. Chebotarev extension with every quadratic sign allowed

For each old p select a residue a_p in F_p^* which is both a cube and has
Legendre symbol epsilon_p. Both signs are possible: the cube subgroup has
even order and its quadratic character is nontrivial. Each sign occurs
exactly (p-1)/6 times. Prescribe a=13 mod24 and a=a_p modp for all p in S.
CRT yields a unit class a modulo M. In particular a=1 mod3, so its
cyclotomic automorphism fixes K.

Take sigma in V to act nontrivially on cuberoot(2), but trivially on
cuberoot(3) and on every cuberoot(p_i). There are two such automorphisms,
sigma and sigma^-1. Since L intersect F=K, each is compatible with the
chosen cyclotomic automorphism. Their conjugacy class in Gal(LF/Q) has
exactly two elements; conjugation acts by inversion on V and does not
change the cyclotomic component.

Apply Chebotarev to this nonempty conjugacy class. Every unramified prime
q in it has q=a modM. Since q=1 mod3, its residue field contains cube roots
of unity. The Frobenius conditions say exactly:

    2 is NOT a cube modulo q;
    3 and every old p_i ARE cubes modulo q.

The CRT conditions say q is13 mod24, q is a cube at every old p_i, and
Legendre(q,p_i)=epsilon_i. All primes are1 mod4, so reciprocity gives the
reverse signs too. Thus S union {q} is admissible with the prescribed signs.

For completeness, vary all the product (p_i-1)/6 allowed CRT choices.
They are distinct cyclotomic components, hence disjoint conjugacy classes.
Chebotarev gives Dirichlet density

    [2*product((p_i-1)/6)]/[3^(m+2)*8*product(p_i-1)]
       = 1/(36*18^m).

These are exactly the stated extension conditions away from finitely many
ramified primes. In particular every sign pattern has positive density,
not merely one conveniently chosen pattern. There is no asserted useful
bound on the least next prime, and no GRH hypothesis is used.

Starting with the empty support, prescribe any symmetric sign matrix on
natural-number labels. At stage m prescribe its m signs against the old
vertices, and choose q larger than all old primes. The extension theorem
applies at every stage. Every finite subset belongs to a finite prefix,
so Theorem A proves its complete columns. This proves the corollary.

## 7. Concrete nonhomogeneous support and a strict local comparison

For S=(661,853,2389), 2^((p-1)/3) equals respectively296,632,689, all non1.
Cube-root witnesses at p, in order3 and the other support elements, are:
 p661: 261^3=3,337^3=853,12^3=2389 (mod661);
 p853: 145^3=3,230^3=661,153^3=2389 (mod853);
 p2389:594^3=3,1113^3=661,26^3=853 (mod2389).
The edge Legendre signs on (661,853),(661,2389),(853,2389) are(+,+,-).
All identities and primality are checked exactly in the companion program.

The product j=1346997037 and rows n=853*2^N for every N>=22 have gcd853.
At the two active primes the quadratic signs of853 are opposite, so the
previous LOCAL quadratic-synchronization criterion fails on this whole
unbounded comparison family. Cubic transport holds nonetheless. This
compares two named criteria; no claim that every older filter fails is made.

There are also explicit one-prime extensions of S=(61,613) for ALL four
sign vectors: q51229 for(-,-),q74149 for(+,-),q197773 for(-,+),q260461 for(+,+).
They verify nonempty examples; the infinity and density statements come
from the proved field intersection and the external Chebotarev theorem.

## 8. Sources, actual formalization correspondence, and limits

Read current dev `GeneralPowerCharacterLayer.lean`, blob
79c32483be14a2333e043f151744877c4ea30fb8. Its n=3 power-subgroup/character
interface is the first observation layer. Read `QuadraticCompositeRank.lean`,
blobe1032eaff92f53700f639ceb3bab3292b151651c: it proves a concrete
biquadratic rank, not our multiradical cubic rank. The proof above supplies
the missing independence rather than assuming a direct product of groups.
Official Mathlib KummerExtension documentation exposes single-radical
`autEquivRootsOfUnity` and `autEquivZmod`; this is a starting interface,
not an existing formalization of our whole tower or Chebotarev application.
No existing source was recompiled in this environment and no new Lean
axiom or untested truth declaration is introduced.

External classical input for B: A.V. Sutherland, MIT18.785 Fall2021,
Lecture28, Theorem28.9, printed p6, Chebotarev for any conjugacy-stable
subset C of a finite Galois group: Dirichlet density |C|/|G|. The parsed
statement AND screenshot of that page were read this turn. Stacks Project
09I6/09DX and official Mathlib KummerExtension documentation were read
for the elementary radical setup. The proof does not use Stacks09I6's
separate subextension lemma or assume full multiradical degree from it.

Formalize in order: local cyclic-character arithmetic lemma; finite
products of cube residues; norm injectivity on rational cube classes;
annihilator proof of full radical rank; semidirect commutator; abelian
intersection; Frobenius/CRT compatibility and Chebotarev specialization.
The last step remains an external-theorem boundary until formalized.
Theorem A and its explicit supports do not depend on that last step.

This does not settle arbitrary GIVEN prime supports, unrestricted i=3,
or remaining original indices4..324. The old uniform3-p and i>=325 proofs
are retained at their recorded scope and are not recertified here. The
advance is new nonsynchronized support columns plus an extension theorem
allowing arbitrary quadratic graphs; arbitrary cubic data remain constrained.
Finite computations below are self-audits and example eligibility checks,
not an exhaustive original-counterexample proof or independent review.

"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
import json
from math import comb, gcd, isqrt, prod


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


@lru_cache(None)
def prime(p: int) -> bool:
    return p >= 2 and all(p % q for q in range(2, isqrt(p) + 1))


@lru_cache(None)
def factors(n: int) -> tuple[tuple[int, int], ...]:
    if n < 1:
        raise ValueError('positive integer required')
    out = []
    p = 2
    while p*p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            out.append((p, exponent))
        p = 3 if p == 2 else p+2
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def v2(n: int) -> int:
    if n <= 0:
        raise ValueError('nonzero positive input required')
    return (n & -n).bit_length() - 1


def legendre(a: int, p: int) -> int:
    require(prime(p) and p > 2, 'odd prime required')
    residue = pow(a % p, (p-1)//2, p)
    require(residue in (0, 1, p-1), 'Euler value')
    return -1 if residue == p-1 else residue


def cube(a: int, p: int) -> bool:
    require(prime(p) and p % 3 == 1, 'split cubic prime required')
    return a % p != 0 and pow(a % p, (p-1)//3, p) == 1


def phi(a: int, p: int) -> int:
    require(prime(p) and p % 3 == 1 and a % p != 0, 'character domain')
    u = pow(2, (p-1)//3, p)
    require(u != 1 and pow(u, 3, p) == 1, 'distinguished generator')
    return (1, u, u*u % p).index(pow(a % p, (p-1)//3, p))


def admissible(S: tuple[int, ...]) -> bool:
    return (len(set(S)) == len(S)
            and all(prime(p) and p % 24 == 13 and cube(3, p)
                    and not cube(2, p) for p in S)
            and all(cube(q, p) for p in S for q in S if p != q))


def least_cube_root(a: int, p: int) -> int:
    for r in range(1, p):
        if (r*r*r) % p == a % p:
            return r
    raise AssertionError(f'no cube root: {a} mod {p}')


SAMPLE = (661, 853, 2389)
EXTENSIONS = (((-1, -1), 51229), ((1, -1), 74149),
              ((-1, 1), 197773), ((1, 1), 260461))


def field_audit() -> dict:
    require(admissible(SAMPLE), 'main example')
    rows = []
    unit_checks = hom_checks = 0
    for p in SAMPLE:
        cubes = {pow(z, 3, p) for z in range(1, p)}
        values = {z: phi(z, p) for z in range(1, p)}
        require(len(cubes) == (p-1)//3, 'cube subgroup size')
        require(phi(2, p) == 1 and phi(3, p) == 0, 'labelled values')
        require(phi(-1, p) == 0, 'cubic observation loses -1')
        for z in range(1, p):
            require((z in cubes) == (values[z] == 0), 'exact kernel')
            unit_checks += 1
            for a in (2, 3) + tuple(q for q in SAMPLE if q != p):
                require(values[z*a % p] == (values[z]+values[a % p]) % 3,
                        'character homomorphism on complete generator edges')
                hom_checks += 1
        roots = {str(a): least_cube_root(a, p)
                 for a in (3,) + tuple(q for q in SAMPLE if q != p)}
        require(all(pow(v, 3, p) == int(a) % p for a, v in roots.items()),
                'explicit roots')
        o = p-1
        for q, _ in factors(o):
            while o % q == 0 and pow(2, o//q, p) == 1:
                o //= q
        require(v2(o) == 2, 'second observation layer')
        rows.append({'p': p, 'order2': o, 'u': pow(2, (p-1)//3, p),
                     'cube_roots': roots})
    signs = [legendre(p, q) for p, q in combinations(SAMPLE, 2)]
    require(signs == [1, 1, -1], 'nonhomogeneous sign graph')
    require(legendre(853, 661) == 1 and legendre(853, 2389) == -1,
            'old local synchronization fails')
    require(phi(853, 661) == phi(853, 2389) == 0, 'new local kernel')
    extensions = []
    for signs_wanted, q in EXTENSIONS:
        require(admissible((61, 613, q)), 'extension eligibility')
        actual = tuple(legendre(q, p) for p in (61, 613))
        require(actual == signs_wanted, 'arbitrary sign example')
        require(tuple(legendre(p, q) for p in (61, 613)) == actual,
                'reverse signs')
        extensions.append({'q': q, 'signs': actual,
                           'new_field_cube_roots':
                           {str(a): least_cube_root(a, q) for a in (3, 61, 613)}})
    require(not admissible((5, 29, 53)), 'old unresolved support not covered')
    require(not admissible((13,)), '3-cube condition is not omitted')
    return {'complete_unit_checks': unit_checks, 'homomorphism_edges': hom_checks,
            'main_support': rows, 'quadratic_signs': signs, 'extensions': extensions}


def add(u: tuple[int, ...], v: tuple[int, ...]) -> tuple[int, ...]:
    return tuple((x+y) % 3 for x, y in zip(u, v))


def scale(k: int, u: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(k*x % 3 for x in u)


def mul(g, h):
    u, s = g
    v, t = h
    return add(u, scale(-1 if s else 1, v)), (s+t) % 2


def inverse(g):
    u, s = g
    return scale(1 if s else -1, u), s


def conjugate(g, h):
    return mul(mul(g, h), inverse(g))


def commutator(g, h):
    return mul(conjugate(g, h), inverse(h))


def group_audit() -> dict:
    commutators = conjugations = 0
    dimensions = []
    for r in range(1, 5):
        V = tuple(product(range(3), repeat=r))
        zero = (0,)*r
        G = tuple((v, s) for v in V for s in range(2))
        tau = (zero, 1)
        derived = set()
        for v in V:
            require(commutator(tau, (v, 0)) == (v, 0), 'inversion commutator')
            require(all((2*x) % 3 == 0 for x in v) == (v == zero),
                    'norm scalar injectivity')
        for g in G:
            require(mul(g, inverse(g)) == (zero, 0), 'inverse')
            for h in G:
                derived.add(commutator(g, h))
                commutators += 1
        require(derived == {(v, 0) for v in V}, 'exact derived subgroup')
        e0 = (1,) + (0,)*(r-1)
        conj = {conjugate(g, (e0, 0)) for g in G}
        conjugations += len(G)
        require(conj == {(e0, 0), (scale(-1, e0), 0)}, 'two conjugates')
        dimensions.append({'r': r, 'group_order': len(G),
                           'derived_order': len(derived), 'class_size': len(conj)})
    # All linear subspaces in dimensions at most 3, checked by actual spans.
    subspace_counts = []
    for r in range(1, 4):
        V = tuple(product(range(3), repeat=r)); zero = (0,)*r
        todo = [frozenset((zero,))]; spaces = set(todo)
        while todo:
            W = todo.pop()
            for v in V:
                span = frozenset(add(w, scale(t, v)) for w in W for t in range(3))
                if span not in spaces:
                    spaces.add(span); todo.append(span)
        for W in spaces:
            annihilator = [a for a in V if all(sum(x*y for x, y in zip(a, w)) % 3 == 0
                                              for w in W)]
            require(len(annihilator)*len(W) == len(V), 'annihilator size')
            require((len(W) < len(V)) == any(a != zero for a in annihilator),
                    'proper image has a nonzero functional')
        subspace_counts.append({'r': r, 'subspaces': len(spaces)})
    # Dependence controls: distinct radicands need not have independent cube classes.
    require(tuple(e % 3 for _, e in factors(16)) == (1,), '2 and 16 dependent')
    require(all(e % 3 == 0 for _, e in factors(8)), '8 is already a cube')
    return {'dimensions': dimensions, 'all_pair_commutators': commutators,
            'conjugations': conjugations, 'subspaces': subspace_counts}


def crt(residues: tuple[int, ...], moduli: tuple[int, ...]) -> int:
    x = 0; modulus = 1
    for a, m in zip(residues, moduli):
        require(gcd(modulus, m) == 1, 'coprime CRT moduli')
        x += modulus * (((a-x) * pow(modulus, -1, m)) % m)
        modulus *= m
    return x % modulus


def extension_audit() -> dict:
    S = (61, 613)
    require(admissible(S), 'old support for extension')
    groups = {}
    for p in S:
        roots = {pow(z, 3, p) for z in range(1, p)}
        groups[p] = {sign: tuple(a for a in range(1, p)
                                if a in roots and legendre(a, p) == sign)
                     for sign in (-1, 1)}
        require(all(len(values) == (p-1)//6 for values in groups[p].values()),
                'both signs on the cube subgroup')
    crt_checks = 0
    for signs in product((-1, 1), repeat=2):
        for a, b in product(groups[61][signs[0]], groups[613][signs[1]]):
            q_class = crt((13, a, b), (24, 61, 613))
            require(q_class % 24 == 13 and q_class % 61 == a and q_class % 613 == b,
                    'actual CRT class')
            require(gcd(q_class, 24*61*613) == 1, 'unit class')
            require(q_class % 3 == 1, 'compatible on common field')
            crt_checks += 1
    densities = []
    for m in range(9):
        counting = Fraction(2, 3**(m+2)*8*6**m)
        stated = Fraction(1, 36*18**m)
        require(counting == stated, 'exact density simplification')
        densities.append(str(stated))
    return {'all_crt_unit_classes_checked': crt_checks,
            'density_formulas_m0_to_m8': densities,
            'density_scope': 'algebraic count only; Chebotarev is an external theorem'}


def ratio_audit(limit: int) -> dict:
    count = specials = parity_cases = 0
    for n in range(8, limit+1):
        for j in range(4, n//2+1):
            theta = Fraction((n-j)*(n-j-1), (n-1)*(n-2))
            x, D = theta.numerator, theta.denominator
            require(2*x % gcd(n, j) == 0, 'ratio gcd collapse')
            require((n-1)*((D-x)*n+2*x) == D*j*(2*n-1-j), 'exact residual')
            if theta in (Fraction(1, 3), Fraction(2, 3)):
                require(gcd(n, j) in (1, 2, 4), 'special ratio shared odd part')
                specials += 1
            if n % 4 == 0 and v2(n) >= v2(j)+2 and (j >> v2(j)) % 4 == 1:
                require(theta != Fraction(2, 3), 'independent two-thirds exclusion')
                parity_cases += 1
            count += 1
    # The original two-thirds equation has solutions outside the binary premises.
    require(Fraction((56-11)*(56-12), 55*54) == Fraction(2, 3), 'nonempty control')
    return {'actual_ratios': count, 'special_ratio_controls': specials,
            'binary_two_thirds_cases': parity_cases}



def valuation_binomial(n: int, k: int, p: int) -> int:
    z = n-k; total = 0
    while n:
        n //= p; k //= p; z //= p
        total += n-k-z
    return total


def carries(n: int, k: int, p: int) -> int:
    a, b = k, n-k; carry = count = 0
    while a or b or carry:
        carry = (a % p + b % p + carry) // p
        count += carry
        a //= p; b //= p
    return count


def witness(n: int, j: int, pool: tuple[int, ...]) -> int:
    for p in pool:
        a = valuation_binomial(n, 3, p)
        if a > 0:
            b = valuation_binomial(n, j, p)
            if b > 0:
                require(a == carries(n, 3, p) and b == carries(n, j, p),
                        'Legendre and carries agree')
                return p
    raise AssertionError(f'no witness found in audit pool for n={n},j={j}; not a disproof')


def regression(limit: int) -> dict:
    pool = tuple(p for p in range(3, 10000, 2) if prime(p))
    columns = []
    for j in range(4, limit//2+1):
        S = tuple(p for p, _ in factors(j) if p != 2)
        if admissible(S):
            columns.append(j)
    small = direct = 0
    for j in columns:
        for n in range(2*j, limit+1):
            p = witness(n, j, pool)
            if n <= 150:
                require(comb(n, 3) % p == comb(n, j) % p == 0, 'direct binomials')
                direct += 1
            small += 1
    targeted = []
    exponents = ((1, 1, 1), (1, 2, 1), (2, 1, 1), (1, 1, 2))
    shared = ((), (661,), (853,), (2389,), SAMPLE)
    nonconstant = 0
    for powers in exponents:
        odd_j = prod(p**a for p, a in zip(SAMPLE, powers))
        for b, c, T, offset in product((0, 1, 3), (1, 3), shared, (0, 2)):
            j = (1 << b)*odd_j; e = prod(T)
            N = max(b+2, (2*j//(c*e)).bit_length()) + offset
            n = c*(1 << N)*e
            require(n >= 2*j and gcd(n, j) == (1 << b)*e, 'genuine shared factors')
            active = tuple(p for p in SAMPLE if p not in T)
            if len({legendre(e, p) for p in active}) > 1:
                nonconstant += 1
            require(all(phi(e, p) == 0 for p in active), 'cubic shared kernel')
            ell = witness(n, j, pool)
            targeted.append({'n': n, 'j': j, 'gcd': (1 << b)*e, 'prime': ell})
    return {'small_columns': len(columns), 'small_original_pairs': small,
            'small_box_has_three_prime_example': any(j % prod(SAMPLE) == 0 for j in columns),
            'direct_binomial_checks': direct, 'targeted_three_prime_pairs': len(targeted),
            'targeted_nonsynchronized_quadratic_pairs': nonconstant,
            'targeted_witnesses': targeted,
            'scope': 'self-audit only; no cutoff on the universal theorem'}


def symbolic_audit() -> dict:
    import sympy as sp
    n, j, D, x = sp.symbols('n j D x')
    raw = D*(n-j)*(n-j-1)-x*(n-1)*(n-2)
    transformed = (n-1)*((D-x)*n+2*x)-D*j*(2*n-1-j)
    require(sp.expand(raw-transformed) == 0, 'symbolic residual')
    a, b = sp.symbols('a b')
    z = -sp.Rational(1, 2) + sp.sqrt(3)*sp.I/2
    actual_norm = sp.expand((a+b*z)*(a+b*sp.conjugate(z)))
    require(sp.simplify(actual_norm-(a*a-a*b+b*b)) == 0, 'quadratic-field norm formula')
    require(sp.expand((a*a-a*b+b*b)**3-
                       (a+b*z)**3*(a+b*sp.conjugate(z))**3) == 0,
            'norm of cube')
    return {'exact_symbolic_identities': 3}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--nmax', type=int, default=800)
    parser.add_argument('--ratio-nmax', type=int, default=250)
    parser.add_argument('--symbolic', action='store_true')
    args = parser.parse_args()
    if args.nmax < 8 or args.ratio_nmax < 8:
        parser.error('bounds must be at least 8')
    report = {'status': 'exact self-audits passed; not independent or Lean verification',
              'field': field_audit(), 'groups': group_audit(),
              'extensions': extension_audit(), 'ratios': ratio_audit(args.ratio_nmax),
              'regression': regression(args.nmax)}
    if args.symbolic:
        report['symbolic'] = symbolic_audit()
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
