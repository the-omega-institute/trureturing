---
bibkey: niedbala2026carlitz
authors: David Niedbala Giraudin
year: 2026
title: "A counterexample to a conjecture of Thakur on Carlitz-Wieferich primes"
doi: 10.48550/arXiv.2607.15305
url: https://arxiv.org/abs/2607.15305
claim: "Version 2, Conjecture 4.2: over F_(19^3), gcd(T^(q^5)-T,M_(5,q)) equals mu(T^q-T), with mu=X^5+5X^3+3X^2-4X-9."
strata_touched:
  - D5/S3/Arith/FunctionField/CarlitzFiveOrbit
license: CC-BY-4.0
triage: anchor
---

# Carlitz degree-five exactness

The relevant primary version is arXiv:2607.15305v2, dated 22 July 2026:
https://arxiv.org/html/2607.15305v2 . The abstract and version comment explicitly
say that the former exactness theorem was corrected to a conjecture. It is
not valid to quote the superseded version-one exactness label as a proof.

Theorem 1.1 supplies an explicit irreducible Carlitz-Wieferich quintic over
F_(19^3). Theorem 4.1 proves that its 6859 translates have product
mu(T^q-T) and that this product divides the gcd. Those results are established
inputs of the source, not the new target. Conjecture 4.2 asks whether any
additional factor exists. The discussion isolates a possible difference
eta=theta^q-theta of degree fifteen over F19; the low-degree difference
case was already accounted for.

The companion *Effective determination of Carlitz-Wieferich primes of given
degree* is listed as in preparation in version 2. Searches for the exact
arXiv identifier, exactness conjecture number, companion title, and combined
Carlitz-Wieferich completeness terms did not locate a later published proof
in the checked sources. This is a bounded literature check, not an assertion
of worldwide priority or author/editor acceptance.

The new certificate uses the literal nested residual from equation (2),
its five conjugates, and the literal mu from Conjecture 4.2. It proves that
all solutions of the resulting orbit equations have quintic difference.
The corresponding ordinary proof concludes exactness and also handles all
constant fields F_(19^s). The original counterexample to Thakur's suggestion
is not counted again.

Earlier primary sources for the criterion are:

- D. S. Thakur, *Fermat versus Wilson congruences, arithmetic derivatives and
  zeta values*, Finite Fields and Their Applications 32 (2015), 192-206.
- A. S. Bamunoba and J. Bergstrom, *A search for c-Wieferich primes*,
  International Journal of Number Theory 17 (2021), 1599-1616,
  https://arxiv.org/abs/2011.11727 .

Function-field Carlitz-Wieferich primes are distinct from integer
Wall-Sun-Sun primes. The characteristic-nineteen elimination certificate
has no asserted implication of integer WSS existence.

## Unified owner and the all-characteristic continuation

All CF1-CF5 proofs now live under the existing owner
`Problems/wall-sun-sun-golden-unit-lift.md`, followed by CX1-CX6. The former
separate Carlitz problem file was removed only after its complete mathematics
was retained there. This Library note remains a source record, not a second
open-problem entry. The existing CarlitzFiveOrbit Lean/Scribe pair is unchanged.

The source's Proposition 5.2 reports finite prime-field computations, with
its degree-five row covering p=3,7,11,13,17,19,23,29,31,37. It does not give
the uniform all-odd-characteristic classification developed in CX. The new
integer five-orbit certificate restricts odd characteristic to5,19,263 and
519555805809266011. Additional exact certificates and constructions give
extension classes s=3 modulo5 for263 and s=4 modulo5 for the large prime.
Together with CF this excludes degree-five nonconforming examples over every
odd prime field. These new mathematical conclusions are not attributed to
the source author, and do not answer the source's prime-field question in
higher degrees.

The companion paper remains listed as in preparation in the checked v2.
Exact searches for Carlitz-Wieferich together with263, the large characteristic,
the companion title and degree-five completeness did not locate the new
families in the checked primary sources. The known characteristic19 result
and its already delivered completeness proof are not counted again. Neither
absence from indexed search nor an unpublished companion's unknown contents
establishes worldwide priority. External acceptance remains unconfirmed.

## Applicability audit: the characteristic-selection construction fails

This records a limitation of the proposed transfer inside the same Wieferich
problem family. It is not a new open-problem entry or an attribution to the
source author. The attempted construction takes the rational characteristic
p>5 of a degree-five Carlitz-Wieferich example over some F_(p^s), and uses that
same p as an integer Fibonacci WSS candidate.

The existing CX characteristic restriction leaves only

$$p=19,\quad263,\quad P_*=519555805809266011.$$

Exact modular Fibonacci evaluation gives, with epsilon=(5/p),

$$\begin{array}{c|r|r}
p&F_{p-\epsilon}\bmod p^2&q_p=F_{p-\epsilon}/p\bmod p\\\hline
19&57&3\\
263&27615&105\\
P_*&218822702976076845315377336456939760&421172664282398160.
\end{array}$$

Every quotient is nonzero. The primality of P_* has a recursive Lucas
certificate. Thus the complete characteristic-selection route produces no
integer WSS prime. This does not exclude other maps between the two arithmetic
problems, or invalidate the function-field constructions.

### The unchanged five residuals cannot lift to characteristic p squared

Write R(a,b,c,d)=1-d(1-c(1-b(1-a))) and
 tau(a,b,c,d)=(b-a,c-a,d-a,-a). The actual source
`CarlitzFiveCharacteristic.lean` contains the integer identity

$$\sum_{i=0}^4 S(\tau^i(a,b,c,d))R(\tau^i(a,b,c,d))=D,$$

where

$$D=4673196650932024062540600
=3^2\cdot8\cdot25\cdot19\cdot263\cdot P_*.$$

Its polynomial identity uses only integer coefficients and ring operations,
even though the public source theorem is stated for fields. Therefore it is
valid in every commutative ring. If all five residuals vanish in a ring of
exact characteristic p^e, then p^e divides D. For p in {19,263,P_*}, the
exponent of p in D is exactly one. Consequently there is no such simultaneous
solution in any ring of exact characteristic p^e with e>=2. In particular,
none of the known residual solutions lifts to an unramified length-two ring
while preserving all five equations. The case p=5 is not covered by this
first-power obstruction.

This is a statement about the rational constant p squared. The Carlitz
congruence modulo a polynomial P(T)^2 is in equal characteristic p, where
p itself is zero. There is no contradiction between the two statements.

### A concrete first-order obstruction and the unique scalar deformation

Fix p=19 and the monic integer lift

$$\widetilde P(T)=T^5+13T^3+3T^2+10T+15.$$

In W=(Z/19^2)[t]/(Ptilde), let sigma be the unramified automorphism lifting
the 19^3-power Frobenius. In the basis (1,t,t^2,t^3,t^4), its value at t is
(176,41,237,82,105) modulo361. Polynomial substitution verifies Ptilde(sigma(t))=0
and sigma^5(t)=t. Put

$$\mathcal E(x)=R(\sigma x-x,\sigma^2x-x,\sigma^3x-x,\sigma^4x-x).$$

For every z in F_(19^5), exact first-order expansion gives

$$\mathcal E(t+19z)/19=e+Jz\quad\text{in }\mathbb F_{19}^5,$$

where

$$e=\begin{pmatrix}10\\8\\1\\3\\11\end{pmatrix},\qquad
J=\begin{pmatrix}
0&5&10&16&13\\
0&6&11&10&0\\
0&14&5&0&5\\
0&0&14&2&2\\
0&13&16&17&3
\end{pmatrix}.$$

The row w=(4,2,14,15,0) satisfies wJ=0 and we=1. Hence no choice of z
can make the original residual vanish modulo361. The four nonconstant
columns have rank four; the minor obtained by deleting the first row has
determinant8 modulo19. Thus the attainable error vectors form exactly the
affine hyperplane w y=1, with19 preimages for each error. Constant translations
are precisely the one-dimensional kernel. This conclusion concerns every
lift, not a finite sample of z values.

If one changes the equation to E(x)=19c with c in F19, solvability instead
requires 4c=1, hence c=5. Fixing the constant coefficient of z to zero gives
one solution z=(0,13,0,18,9). The augmented derivative in the four nonconstant
coordinates and c has nonzero determinant11. Successively correcting the
five coordinates therefore gives, in the unramified degree-five extension
of Z_19, a unique normalized x and scalar kappa in19 Z_19 such that
E(x)=kappa, x=t modulo19. Its first digit is kappa/19=5 modulo19, so
v_19(kappa)=1. The same sigma makes all five translated-origin residuals
exactly equal to kappa. To precision19^4 the constructed scalar is80237.
The inverse derivative proves existence and uniqueness at every precision:
at each step the same invertible residual linear map determines the next
five digits, and completeness supplies their compatible limit.

The corresponding exact calculations for263 and P_* also give rank-four
linearization and a nonzero augmented determinant. With coefficient lifts
in [0,p-1] of the canonical polynomials P_263 and P_P* from CX, their unique
first scalar digits are respectively248 and311747520347328037. The augmented
determinants are17 and140776401079060105. The constructed scalars have
p-adic valuation one in both cases. These scalar digits depend on the stated
integral models and normalization; they are not asserted to be invariant
under arbitrary changes to the residual equation.

This construction solves a deformed equation E=kappa with kappa nonzero.
It is not a mixed-characteristic solution of E=0 and not an integer WSS
construction. Merely allowing a correction parameter can hide the original
obstruction, so the parameter must remain part of the conclusion.

### Comparison with the fixed golden lift, using the current owner CG.2/CG.6

For p>5 retain the actual golden ring, phi^2=phi+1, d=2phi-1, d^2=5,
and sigma equal to the identity or conjugation according to epsilon=(5/p).
For a lift x=phi+pz define, by division before reduction,

$$U(x)=(x^2-x-1)/p,\qquad V(x)=(x^p-\sigma x)/p\quad\bmod p.$$

The existing owner formula for the golden p-derivation gives

$$\Delta_p=(\phi^p-\sigma\phi)/p
=\frac{5+\epsilon d}{4}q_p\pmod p.$$

Expansion in the actual quadratic ring yields

$$U(x)=dz,\qquad V(x)=\Delta_p-\sigma z,\qquad
V(x)+\sigma(d^{-1}U(x))=\Delta_p.$$

The coefficient (5+epsilon*d)/4 is a unit: its norm is5/4. Thus simultaneous
preservation of the original quadratic equation and the Frobenius equation
is equivalent to q_p=0. If only the Frobenius equation is kept, the unique
correction is z=q_p(phi+2)/2. It preserves norm minus one but changes the
trace to 1+5p q_p/2 modulo p^2; the fixed quadratic then has residual
p*(5q_p/2)*phi. It solves the modified trace-parameter quadratic, not the
original one unless q_p=0.

This comparison is an explicit consequence of the already recorded CG
identities. It is not a newly independent constraint on the WSS zero set.
The useful new boundary is that the five-residual characteristic restriction
cannot simply be carried through a mixed-characteristic lift. A successful
transfer must supply the genuine integer lifting equations and preserve
their fixed parameters, rather than infer integer WSS from an adjustable
residual or from the existence of some lifted root. Neither a WSS prime
nor an unbounded WSS exclusion family is proved by this audit.
