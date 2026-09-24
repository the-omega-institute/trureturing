---
bibkey: medina2015fibonacciregularity
authors: L. A. Medina; E. Rowland
year: 2015
title: p-regularity of the p-adic valuation of the Fibonacci sequence
doi: null
url: https://arxiv.org/abs/0910.2907
claim: Theorem 1.4 restates Lengyel's Fibonacci valuation formulas for every prime, retaining the initial rank valuation and the separate formulas for two and five.
strata_touched: []
license: citation-only
triage: anchor
---

# Fibonacci valuations for every prime

## Verified locator

L. A. Medina and E. Rowland, *p-regularity of the p-adic valuation of the
Fibonacci sequence*, The Fibonacci Quarterly 53(3) (2015), 265–271.
The arXiv record https://arxiv.org/abs/0910.2907 gives the journal reference;
Theorem 1.4 (Lengyel) is on page 2 of arXiv:0910.2907v4 (26 January 2015),
https://arxiv.org/pdf/0910.2907v4 .
The proposed DOI 10.1080/00150517.2015.12427843 returns HTTP 404 from
Crossref and doi.org (checked 2026-09-16); the attested locator is arXiv.

## Claim and scope

Write alpha(p) for the least positive index with p dividing F_n. For n>=1,
Theorem 1.4 states v_5(F_n)=v_5(n), and

- v_2(F_n)=v_2(n)+2 when n is zero modulo six;
- v_2(F_n)=1 when n is three modulo six;
- v_2(F_n)=0 in the other four residue classes modulo six.

For a prime p outside {2,5}, v_p(F_n)=v_p(n)+v_p(F_alpha(p)) when
alpha(p) divides n, and v_p(F_n)=0 otherwise. The initial valuation
v_p(F_alpha(p)) is not assumed to be one.

These formulas imply the square-transport equivalence in FPD.1 of
`docs/develop/theory/WALL_SUN_SUN_GOLDEN_UNIT_RESEARCH.md` for positive multipliers;
the zero multiplier is handled separately by F_0=0. The full valuation
formula is attributed to Lengyel, rather than claimed as a new consequence
of the dossier. The paper's computational WSS bound is historical.

## HD. Actual-rank harmonic cancellation and a false WSS construction

This is a written-theory continuation of the existing WSS/Wieferich family.
It keeps the original Fibonacci sequence and fixed golden unit. No new
Problems entry or formal declaration is introduced. In particular, the
following results are not a proof of WSS existence or a new infinite
non-WSS prime family.

### HD.1 Fixed objects and the independent question

Let p>5 be prime, epsilon=(5/p), N=p-epsilon and rho the least positive
index with p dividing F_rho. Put h=v_p(F_rho)=v_p(F_N)>=1 and
q_p=F_N/p modulo p. The rank bound rho|N and the classical valuation
formula justify the equality of depths without assuming h=1. Let L_n
be the original Lucas sequence, L_0=2,L_1=1.

All congruences involving rational numbers below are in Z_(p), the
rationals with denominator prime to p. For 1<=k<rho the integer F_k is
a p-unit. Define the actual rational numbers

$$S_\rho=\sum_{k=1}^{\rho-1}\frac{L_k}{F_k},\qquad
B_\rho=\sum_{k=1}^{\rho-1}\frac{(-1)^k}{F_k^2},\qquad
A_\rho=\sum_{k=1}^{\rho-1}\frac1{F_kF_{\rho-k}}.$$

The attempted construction was to use unexpectedly strong divisibility
of S_rho to force an initial WSS exception. HD.5 shows exactly why that
single-test construction fails. HD.4 gives a necessary nonvanishing
condition for genuine maximal-rank WSS primes.

### HD.2 A complete torsion comparison at the actual initial depth

**Lemma HD1.** For every p>5 and its actual rho,h,

$$\boxed{B_\rho\equiv-\frac{5(\rho^2-1)}{12}\pmod{p^h}.}\tag{HD1}$$

Also, with

$$C_\rho=\sum_{k=1}^{\rho-1}\frac{(-1)^kL_k}{F_k^3},$$

one has C_rho=0 modulo p^h.

**Proof.** Put phi=(1+sqrt(5))/2, psi=1-phi, delta=sqrt(5) and
nu=phi/psi=-phi^2 in the unramified quadratic p-adic algebra
O tensor Z_p. In the split case this algebra is a product of two
p-adic fields; it is not treated as one field. Binet's identity gives

$$\nu^k-1=\delta F_k/\psi^k.$$

Thus nu modulo p has exact order rho, p does not divide rho, and
v_p(nu^rho-1)=h. The valuation on the quadratic algebra denotes
coefficientwise p-divisibility; the displayed identity gives the same
depth in both split factors. Simple-root Hensel lifting for X^rho-1
produces a unique rho-torsion point zeta congruent to nu modulo p.
Factoring nu^rho-zeta^rho shows v_p(nu-zeta)=h, since the remaining
geometric sum reduces to rho*zeta^(rho-1), a unit. Every nu^k-1 and
zeta^k-1 for 1<=k<rho is a unit.

In characteristic zero, the polynomial P(X)=(X^rho-1)/(X-1) gives

$$\sum_{k=1}^{\rho-1}\frac1{1-\zeta^k}=\frac{\rho-1}{2},\qquad
\sum_{k=1}^{\rho-1}\frac1{(1-\zeta^k)^2}
=\frac{(\rho-1)(5-\rho)}{12}.$$

Indeed P(1)=rho, P'(1)=rho(rho-1)/2 and
P''(1)=rho(rho-1)(rho-2)/3. Apply P'/P and its derivative at one.
Subtracting the first sum from the second yields

$$\sum_{k=1}^{\rho-1}\frac{\zeta^k}{(\zeta^k-1)^2}
=-\frac{\rho^2-1}{12}.$$

The exact identities

$$\frac{(-1)^k}{F_k^2}=5\frac{\nu^k}{(\nu^k-1)^2},\qquad
\frac{(-1)^kL_k}{F_k^3}
=\delta^3\frac{\nu^k(\nu^k+1)}{(\nu^k-1)^3}$$

now prove the claims. Rational expressions with unit denominators
preserve congruence modulo p^h. For the second expression its sum at
zeta is exactly zero: replacing k by rho-k negates the term, and a
possible middle term has zeta^k=-1 and is zero. The resulting rational
sums descend to Z_(p). This proof uses no sampled value of h.

### HD.3 Exact factorization and cubic-depth remainder

**Lemma HD2.** The following identity and congruence hold for every p>5:

$$\boxed{S_\rho=F_\rho A_\rho,\qquad
S_\rho\equiv-\frac{2F_\rho}{L_\rho}B_\rho\pmod{p^{3h}}.}\tag{HD2}$$

Moreover,

$$\boxed{A_\rho\equiv\frac{5(\rho^2-1)}{6L_\rho}\pmod{p^h}.}\tag{HD3}$$

**Proof.** The addition identity
L_k F_(rho-k)+L_(rho-k) F_k=2F_rho, summed after division by
F_k F_(rho-k), gives the exact identity. Also

$$2(-1)^kF_{\rho-k}=F_\rho L_k-L_\rho F_k.$$

The norm identity L_rho^2-5F_rho^2=4(-1)^rho makes L_rho a p-unit.
Put z=F_rho/L_rho, R_k=L_k/F_k and b_k=(-1)^k/F_k^2. Then

$$A_\rho=-\frac2{L_\rho}\sum_k\frac{b_k}{1-zR_k}.$$

Every denominator here is a p-unit. Use the exact expansion

$$\frac1{1-zR}=1+zR+\frac{z^2R^2}{1-zR}.$$

The linear correction sums to z*C_rho, which has valuation at least
2h by HD1. The remaining correction also has valuation at least 2h.
Thus A_rho+2B_rho/L_rho belongs to p^(2h)Z_(p). Multiplication by
F_rho proves HD2. Substitution of HD1 gives HD3.

The pairing and quotient-sum expansion are classical. In the published
version of Ballot's paper listed in HD.7, Lemma 23 proves the maximal-rank
specialization modulo p^4. HD2 exposes the p^(3h) control while retaining
arbitrary actual depth and allowing nonmaximal ranks. It is presented
as an ordinary deduction from the displayed identities, not as a claim
that this proof mechanism is new.

### HD.4 Exact depth separation and a genuine necessary WSS condition

**Theorem HD3.** If rho<N, then

$$\boxed{v_p(S_\rho)=h.}\tag{HD4}$$

If rho=N and h>=2, then

$$\boxed{v_p(B_\rho)=1,\quad v_p(A_\rho)=1,\quad
v_p(S_\rho)=h+1,}\tag{HD5}$$

with the exact nonzero first digits

$$\boxed{\frac{B_\rho}{p}\equiv\frac{5\epsilon}{6},\qquad
\frac{S_\rho}{pF_\rho}\equiv-\frac56\pmod p.}\tag{HD6}$$

**Proof.** One has 2<rho<=p+1. If p divides rho^2-1 then rho is p-1
or p+1. Combining either possibility with rho|p-epsilon forces rho=N.
Thus in the nonmaximal case HD3 is a unit, so A_rho is a unit and HD2
gives HD4.

In the maximal case,

$$\rho^2-1=p(p-2\epsilon),\qquad v_p(\rho^2-1)=1.$$

Under h>=2, HD1 fixes B_rho modulo p^2 at a quantity of valuation one,
and B_rho/p=5epsilon/6 modulo p. HD3 likewise makes A_rho have valuation
one. Also L_N=2epsilon modulo p, since phi^N=epsilon modulo p and
psi^N=epsilon modulo p. Dividing HD3 by p therefore gives
A_rho/p=-5/6 modulo p. Multiplication by F_rho gives all remaining
statements. Nonzero constants are legitimate because p>5.

In particular the following exclusion is unconditional:

$$\boxed{\rho=p-\epsilon\ \text{and}\ B_\rho\in p^2\mathbb Z_{(p)}
\quad\Longrightarrow\quad h=1.}\tag{HD7}$$

This specifies an arithmetic class disjoint from WSS. No infinite size,
density, or newly unbounded prime family for that class has been proved.

### HD.5 The false-positive branch and a corrected two-test criterion

**Theorem HD4.** For maximal rank rho=N, the following two alternatives
are disjoint, and they are exactly the causes of S_rho in p^3 Z_(p):

$$\boxed{
S_\rho\in p^3\mathbb Z_{(p)}
\quad\Longleftrightarrow\quad
\bigl(h\ge2\bigr)\ \text{or}\
\bigl(h=1\ \text{and}\ B_\rho\in p^2\mathbb Z_{(p)}\bigr).
}\tag{HD8}$$

Equivalently,

$$\boxed{
p\text{ is WSS}\quad\Longleftrightarrow\quad
S_\rho\in p^3\mathbb Z_{(p)}\ \text{and}\
B_\rho\notin p^2\mathbb Z_{(p)},
\qquad \rho=p-\epsilon.
}\tag{HD9}$$

**Proof.** HD1 always makes B_rho divisible by p in this rank regime.
If h>=2, HD5 proves the first alternative and excludes the second.
If h=1, HD2 holds modulo p^3, and its multiplier -2F_rho/L_rho has
valuation exactly one. Thus S_rho is zero modulo p^3 precisely when
B_rho is zero modulo p^2. This proves both directions and disjointness.
For nonmaximal rank the separate criterion is simply S_rho in p^2Z_(p),
by HD4. None of these equivalences alone supplies an existence argument.

**Exact counterexample to the one-test construction.** At p=11,
epsilon=1, rho=10, F_10=55 and q_11=5. Direct rational summation gives

$$S_{10}=\frac{602943}{30940}
=\frac{3\cdot11^3\cdot151}{30940},$$

$$B_{10}=-\frac{5782018759}{34462209600}
=-\frac{11^2\cdot2273\cdot21023}{34462209600},\qquad
A_{10}=\frac{54813}{154700}.$$

Both displayed denominators of S and B are units at eleven. Therefore
v_11(S_10)=3 and v_11(B_10)=2, although h_11=1. This is an actual
Fibonacci example, not a changed generator or artificial residue vector.
The additional divisibility of S comes from cancellation in A. At the
second diagnostic example p=1559, rho=1558, exact computations modulo
p^5 similarly give q_p=36, v_p(S_rho)=3 and v_p(B_rho)=2.

### HD.6 Connection to the latest torsion-state draft and remaining target

The actual SJC.2-SJC.5 text in #8343 was read at
c5e9479e82bfc38925453bdf95309ebf3c166c43. It writes multiplication by
v=phi^2 as a torsion phase and the original drift -q_p, and proves
that a rephasing cannot remove its accumulated drift. The torsion
comparison in HD1 uses nu=phi/psi=-phi^2 instead. Its order rho is the
Fibonacci zero rank; it must not be confused with the order of v in SJC.
Both constructions keep the actual mixed-characteristic algebra and
use multiplicative torsion sections, not a ring section modulo p^2.

This continuation evaluates arithmetic functions on the complete rho
orbit to test whether a high-order cancellation independently selects
a WSS prime. HD8 proves that it does not: a second non-WSS cancellation
branch exists. Requiring B_rho to vanish even more strongly actually
excludes the maximal-rank WSS branch, by HD7.

The remaining sufficient target in this formulation is a prime of
maximal rank with S_rho zero modulo p^3 and B_rho nonzero modulo p^2,
or a nonmaximal-rank prime with S_rho zero modulo p^2. The formulas here
do not force either event, prove their infinitude, or make them cheaper
to find than the original Fibonacci quotient. The primewise joint
arithmetic of the two sums still needs an independent estimate or an
explicit witness. WSS existence is not declared completed.

### HD.7 Sources, finite checks and scope

Christian Ballot, *The Congruence of Wolstenholme for Generalized Binomial
Coefficients Related to Lucas Sequences*, Journal of Integer Sequences
18 (2015), Article 15.5.4, published 19 May 2015:
https://cs.uwaterloo.ca/journals/JIS/VOL18/Ballot/ballot14.html .
The official 22-page PDF, printed page 16, Lemma 23, supplies the related
maximal-rank quotient-sum congruence modulo p^4; its numbering differs
from the earlier arXiv version 1409.8629. Lemma 22 and Theorem 24 record
related higher congruences and Lucasnomial consequences. The publication
text and displayed formulas supply the cited comparison; no claim here
depends on visual rendering.

The valuation input remains Lengyel's theorem recorded in the original
Medina-Rowland note above. Root-of-unity power sums, Hensel lifting and
Lucas addition identities are classical. Repository keyword searches
for Wolstenholme/Ballot found no matching indexed entry, but this is not
an exhaustive statement about every unmerged branch. Bounded external
searches did not establish global priority for the all-depth partition
HD8. No first-ever arithmetic theorem, external conjecture resolution,
or new unbounded WSS exclusion family is claimed.

The final exact checker uses the original recurrence modulo p^5, batch
inversion, independent Fibonacci doubling and integer matrix powers.
For the 427 primes from 7 through 3000, it checks HD1-HD4, the cubic-depth
identity, and HD8-HD9 where the rank is maximal (163 primes). All actual
initial depths are one. It independently constructs the rational p=11
counterexample. The two harmonic false positives in this range are 11
and 1559. Earlier exploratory checks of B_rho modulo p^2 covered 854
maximal-rank primes at most 20000 and gave the same two examples; this
is not a new WSS search bound or a proof of their absence beyond that
range. Finite tests do not certify the hypothetical h>=2 cases, whose proofs
retain h symbolically. These written claims are not Lean/Scribe artifacts
and are not kernel-certified.

## DF. A phase-preserving two-scale filter with no harmonic false-positive branch

This is a written-theory continuation of HD in the SAME WSS/Wieferich
problem family. It retains the original Fibonacci/Lucas sequences. The
new observation combines two samplings of that sequence; it does not
replace the golden unit by a freely chosen Hensel lift. The result removes
the cancellation that produced the actual p=11 and p=1559 false positives.
It is not a proof that an original WSS prime exists.

### DF.1 The explicit observable and its exact depth

Fix a prime p>5, epsilon=(5/p), N=p-epsilon, rho=r(p), and the actual
h=v_p(F_rho)=v_p(F_N)>=1. For a positive integer a with a=1 modulo rho,
put

$$\mathcal H_\rho(a)=\sum_{k=1}^{\rho-1}\frac{L_{ak}}{F_{ak}},\qquad
\mathcal D_{\rho,a}=a^2\mathcal H_\rho(1)-\mathcal H_\rho(a).$$

Every denominator is a p-unit: rho dividing ak would imply rho dividing
k because gcd(a,rho)=1. These are ordinary rational numbers in Z_(p).
Assume additionally p does not divide a(a-1). Such a scale can always
be chosen without knowing h or q_p:

$$a=\begin{cases}2\rho+1,&\rho=p-1,\\\rho+1,&\rho\ne p-1.\end{cases}
\tag{DF1}$$

**Theorem DF1 (cubic-depth congruence and exact valuation).**

$$\boxed{\mathcal D_{\rho,a}\equiv
\frac{5a(a-1)(\rho^2-1)}{6L_\rho}F_\rho\pmod{p^{3h}}.}
\tag{DF2}$$

Consequently, with e=1 if rho=N and e=0 otherwise,

$$\boxed{v_p(\mathcal D_{\rho,a})=h+e.}\tag{DF3}$$

In particular, the exceptional cancellation in HD.5 has been removed
for EVERY prime in the theorem, rather than only excluded by a second
condition on B_rho. The observable is nonzero as a rational number.

**Proof.** The rank bound gives 2<rho<=p+1 and p does not divide rho.
It follows that v_p(rho^2-1) is one precisely at rho=N and is zero
otherwise, as proved in HD.4. The proposed a has a=1 modulo rho;
a-1 is either rho or 2rho and is a p-unit. The only possible nonunit
rho+1 is p, at rho=p-1, and the alternative 2rho+1=2p-1 is a unit.
Thus DF1 supplies the stated scale in every case.

The proof of DF2 is given in DF.2-DF.3 below using an integral Taylor
expansion and a torsion point only as a proof coordinate. Its displayed
leading term has valuation h+e, because L_rho,6,5,a,a-1 are p-units.
For h>=1 and e<=1, h+e<3h. Hence the remainder cannot change that
valuation, proving DF3. No actual depth is replaced by one.

### DF.2 Explicit elimination of the unknown quadratic coefficient

Work in O_p=Z[phi] tensor Z_p, and set delta=sqrt(5) and nu=phi/psi.
For split p this algebra is the product of two unramified local rings;
coefficientwise p-divisibility is used throughout. Let zeta be the unique
rho-torsion lift of nu modulo p. HD.2 proves that

$$x=\nu/\zeta-1\in p^hO_p,\qquad v_p(x)=h.$$

Define the actual rational function

$$G_\rho(X)=\sum_{k=1}^{\rho-1}\frac{X^k+1}{X^k-1}.$$

All denominators at zeta are units. Therefore G_rho(zeta(1+X)) has
an integral power series on X in pO_p. Pairing k and rho-k gives its
constant coefficient zero. Write its first terms as

$$G_\rho(\zeta(1+X))=A X+B X^2+X^3E(X),\qquad E(X)\in O_p[[X]].$$

Here the same letter B does not denote the rational sum B_rho of HD.
It is an unknown Taylor coefficient, and no nonvanishing of it is assumed.
The linear coefficient is known exactly:

$$\boxed{A=\frac{\rho(\rho^2-1)}{12}.}\tag{DF4}$$

Indeed, differentiation gives
A=-2 sum_(k=1..rho-1) k*zeta^k/(zeta^k-1)^2.
The unweighted term is unchanged by k -> rho-k, so its weighted sum
is rho/2 times its unweighted sum. The exact root-of-unity identity
in HD.2 now gives DF4. A possible middle term at even rho obeys the
same identity.

Since a=1 modulo rho, nu^a=zeta(1+x)^a. Using the integral expansion
(1+X)^a-1=aX+a(a-1)X^2/2+X^3J_a(X), one obtains

$$\boxed{
a^2G_\rho(\zeta(1+X))-G_\rho(\zeta(1+X)^a)
=a(a-1)A(X-X^2/2)+X^3R_a(X),\quad R_a\in O_p[[X]].
}\tag{DF5}$$

This follows by substituting into A X+B X^2: the two B terms are
+a^2 B X^2 and -a^2 B X^2 and cancel identically. The coefficient
of X^2 that remains is -A*a(a-1)/2. Cubic and higher terms remain
integral because every denominator has a unit constant term. In
particular no division by a factorial divisible by p occurs.

By Binet, delta*G_rho(nu^a)=H_rho(a). Thus the left side of DF5 at
X=x is D_(rho,a)/delta. The unwanted quadratic coefficient has been
eliminated before any arithmetic value of q_p is selected.

### DF.3 Return to the fixed original Fibonacci error

Put z=delta F_rho/L_rho. The norm identity makes L_rho a p-unit,
so z belongs to p^h O_p. The exact identity is

$$(1+x)^\rho=\nu^\rho=\frac{1+z}{1-z}.$$

To degree two, subtract one from each side and then subtract half
its square. The left side becomes rho(X-X^2/2) modulo X^3; the
right side becomes 2z modulo z^3. Consequently,

$$\rho(x-x^2/2)\equiv2\delta F_\rho/L_\rho\pmod{p^{3h}}.
\tag{DF6}$$

This is a finite rational-function computation with unit denominators.
An infinite logarithm or a characteristic-p substitute for O/p^2O is
not required. Substitute DF4 and DF6 into delta times DF5. Since
rho and delta are units and delta^2=5, the result is exactly DF2.
The resulting congruence is between rational numbers; intersecting
p^(3h)O_p with Q_p gives the stated Z_(p) congruence.

### DF.4 A single corrected test at the original WSS threshold

**Corollary DF2.** For every permitted a,

$$p\text{ is WSS}\quad\Longleftrightarrow\quad
\mathcal D_{\rho,a}\in p^{2+e}\mathbb Z_{(p)},\qquad
 e=1_{\rho=N}.\tag{DF7}$$

At maximal rank and the deterministic choice DF1,

$$\boxed{\frac{\mathcal D_{N,a}}{p^2}
\equiv-\frac53 q_p\pmod p,\qquad
p\text{ is WSS}\Longleftrightarrow
\mathcal D_{N,a}\equiv0\pmod{p^3}.}\tag{DF8}$$

**Proof.** DF7 follows from DF3. At rho=N one has
(rho^2-1)/p=p-2epsilon and L_rho=2epsilon modulo p. For epsilon=1,
DF1 gives a=2p-1; for epsilon=-1 it gives a=p+2. In BOTH cases
a(a-1)=2 modulo p. Divide DF2 by p^2. Its remainder has valuation
at least3h-2>=1; F_N/p=q_p modulo p. The resulting coefficient is
-5/3, a unit. This includes h>=2, when both residues vanish.

**Actual false-positive repaired.** At p=11, rho=10 and a=21,

$$\mathcal H_{10}(1)=602943/30940\equiv0\pmod{11^3},$$

but exact rational summation gives

$$\boxed{441\mathcal H_{10}(1)-\mathcal H_{10}(21)
\equiv1210=10\cdot11^2\not\equiv0\pmod{11^3}.}\tag{DF9}$$

Its valuation is exactly two, as required for the actual h_11=1.
Likewise, at the prior false-positive prime 1559, rho=1558, a=3117,
q_p=36 and D_(rho,a)/p^2=1499 modulo p, nonzero. Neither false
positive survives the corrected observation.

The condition p not dividing a(a-1) is essential for the valuation
claim. For example the tempting scale a=rho+1=11 at p=11 is excluded.
It introduces an automatic index lift and does not have DF3's depth.
The valid scale 21 avoids this effect. Sampling the fixed sequence is
not permission to identify a multiplier-produced depth with h_p.

### DF.5 The repaired observable has a unique zero in the entire local ball

The construction has a stronger local normal-form property. For the
fixed torsion point zeta define, for X in pO_p,

$$D_a(X)=\delta\{a^2G_\rho(\zeta(1+X))
                  -G_\rho(\zeta(1+X)^a)\}.$$

**Theorem DF3.** For all X,Y in pO_p,

$$\boxed{v_p(D_a(X)-D_a(Y))=e+v_p(X-Y)\quad(X\ne Y).}\tag{DF10}$$

Moreover D_a maps pO_p bijectively onto p^(e+1)O_p. Its unique zero
is X=0, and division by p^e makes it a distance-preserving coordinate.
This statement is componentwise in the split algebra as well.

**Proof.** In DF5 put C=delta*a(a-1)*A, so v_p(C)=e and C/p^e is a
unit in every factor. The divided difference of X-X^2/2 at X,Y is
1-(X+Y)/2, which is one modulo p. The divided difference of
X^3 R_a(X) has coefficients with at least two factors from X,Y;
it therefore belongs to p^2O_p on this ball. After division by p^e,
where e<=1, that correction belongs to pO_p. The complete divided
difference is a unit times p^e, proving DF10.

For surjectivity write X=pW. The function D_a(pW)/p^(e+1) has the
form (C/p^e)W+pE_1(W), with integral coefficients converging on O_p.
Its reduction is multiplication by a unit, and its derivative is the
same unit modulo p. Every target has a unique first residue solution
and a unique successive base-p digit solution. Completeness gives a
unique preimage. The argument applies to each factor in the split
case. Since D_a(0)=0, zero is the sole root. Thus the harmonic
false-positive branch has been removed at all precisions locally,
not merely from the two previously observed examples.

### DF.6 Scope, prior art, and remaining arithmetic

The same construction admits controlled higher-depth diagnostics:
replace nu by nu^c with c=1 modulo rho. Its depth becomes
h_c=h+v_p(c), and replace H_rho(a) by sum L_(ack)/F_(ack) and
F_rho/L_rho in DF2 by F_(c rho)/L_(c rho). The proof is unchanged.
These are labelled sampled subsequences; h_c>=2 is NOT evidence of
an original WSS prime. The theorem itself retains h symbolically.

Classical inputs are the Fibonacci rank/valuation theorem already
cited in this note, root-of-unity logarithmic derivatives, and
unit-denominator Taylor expansion. Ballot's published 2015 paper,
Lemma 23 and Theorem 24, supplies the nearby harmonic/Lucasnomial
congruence context. The characteristic-zero cancellation of a quadratic
error by two samplings is also a standard extrapolation mechanism.
The present contribution is the explicit phase-preserving arithmetic
construction, cubic-depth remainder, and exact all-depth exclusion of
the prior harmonic false-positive branch. Bounded searches for Lucas
harmonic sums with dilation, extrapolation, and the displayed scale
combination did not establish its global priority; no first-ever or
external-open-problem-resolution claim is made.

The construction is a correct observation of the original q_p, not
an independent theorem forcing q_p to vanish. It supplies neither an
original WSS example nor an unbounded prime-family exclusion. Direct
Fibonacci doubling tests q_p using O(log p) modular operations; the
harmonic filter uses O(rho) such operations after initialization,
with batch inversion available. No faster WSS search is asserted.
The remaining existence obligation is still a new primewise arithmetic
constraint or a certified prime at which the original quotient vanishes.
This written proof is not a Lean/Scribe artifact and carries no
kernel-certified claim.
