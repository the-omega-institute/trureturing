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

## Verified locator

- DOI: 10.48550/arXiv.2607.15305
- URL: https://arxiv.org/abs/2607.15305

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

## Carlitz orbit elimination and characteristic support

The following arguments concern the function-field branch of the [WSS/Wieferich problem family](../../Problems/wall-sun-sun-golden-unit-lift.md). The source conjecture, prior results, repository derivations and remaining integer WSS boundary are distinguished below.

<a id="wss-cf"></a>

### CF. Carlitz degree-five exactness within the same Wieferich family

The integer WSS target and the following function-field subproblem share
this single problem dossier. The CF proof was previously delivered in
PR8170 and is preserved here without recounting it as a new result.
Its independent primary source remains `niedbala2026carlitz`.

#### CF.0 Problem and literal orbit definitions

David Niedbala Giraudin, *A counterexample to a conjecture of Thakur on
Carlitz-Wieferich primes*, arXiv:2607.15305v2 (22 July 2026), Conjecture 4.2,
asks whether, for q=19^3,

$$\gcd(T^{q^5}-T,M_{5,q}(T))=\mu(T^q-T),$$

where

$$\mu(X)=X^5+5X^3+3X^2-4X-9\in\mathbb F_{19}[X]$$

and, with [i]_q=T^(q^i)-T,

$$M_{5,q}=1-[4]_q(1-[3]_q(1-[2]_q(1-[1]_q))).$$

The gcd is monic. Version 2 explicitly corrects the former exactness theorem
to a conjecture. The known factor is a product of 6859 distinct monic
Carlitz-Wieferich primes of degree five. The remaining possibility described
in the paper is an associated difference of degree fifteen over F19, outside
the known quintic difference field. The original counterexample and the
known-factor theorem are prior results, not new claims here.

For a commutative ring define

$$R(a,b,c,d)=1-d(1-c(1-b(1-a))).$$

For indeterminates a,b,c,d put

$$\begin{aligned}
f_0&=R(a,b,c,d),\\
f_1&=R(b-a,c-a,d-a,-a),\\
f_2&=R(c-b,d-b,-b,a-b),\\
f_3&=R(d-c,-c,a-c,b-c),\\
f_4&=R(-d,a-d,b-d,c-d).
\end{aligned}$$

These are the five residuals obtained by changing the origin successively
around the ordered five-point cycle (0,a,b,c,d). Each has total degree four.

#### CF1. A polynomial certificate valid in every characteristic-19 ring

**Theorem.** If a,b,c,d lie in any commutative ring of characteristic nineteen
and f_0=f_1=f_2=f_3=f_4=0, then mu(a)=0.

**Proof.** There are explicit integer polynomials A_0,...,A_4,H satisfying

$$\boxed{\sum_{i=0}^4 A_i f_i-19H=\mu(a)}. \tag{CF1}$$

Their total degrees are respectively 8,8,8,8,7,12. The coefficients A_i
are the centered representatives in [-9,9] of a finite-field elimination
certificate. Their nonzero monomial counts are 382,135,203,182,131.
The five complete Horner expressions A_i occur in the companion Lean proof.
Expanding their weighted sum minus mu gives integer coefficients all
divisible by nineteen. Dividing those coefficients by nineteen defines H,
which has 591 nonzero monomials. This is the integer identity CF1; the
Lean proof instead checks the equivalent identity directly in characteristic
nineteen. No assertion about a search range is involved. Under the five
residual hypotheses both terms on the left of CF1 vanish, proving the result.

The certificate can be found by linear algebra: multiply the five quartics
by every monomial of degree at most eight, then solve for the coefficient
vector of mu(a) in their span over F19. Degree twelve suffices. The direct
identity CF1 is the proof certificate; the elimination program or its claimed
Groebner basis is not an additional mathematical assumption.

#### CF2. Closure under all five conjugate equations

**Theorem.** Let K be a field of characteristic nineteen, sigma a ring
endomorphism of K, and theta an element with sigma^5(theta)=theta. If

$$R(\sigma\theta-\theta,\sigma^2\theta-\theta,
     \sigma^3\theta-\theta,\sigma^4\theta-\theta)=0,$$

then mu(sigma(theta)-theta)=0.

**Proof.** Set a=sigma(theta)-theta, b=sigma^2(theta)-theta,
c=sigma^3(theta)-theta and d=sigma^4(theta)-theta. The given equation
is f_0=0. Apply sigma successively. It preserves the integer coefficients,
addition and multiplication. The closing equation sigma^5(theta)=theta
identifies the next four resulting residuals with f_1,...,f_4. Apply CF1.
No pairwise-distinctness premise or root-counting hypothesis is required.

**Corollary.** For every s>=1 and q=19^s, every common root theta of
T^(q^5)-T and M_(5,q) satisfies mu(theta^q-theta)=0.

**Proof.** In an algebraic closure use sigma(x)=x^q, an actual Frobenius
endomorphism, and apply CF2. In particular the degree-fifteen difference
case left open in the source cannot occur: every such difference has
minimal polynomial dividing the quintic mu.

#### CF3. The five-dimensional difference field

**Lemma.** The polynomial mu is irreducible over F19. In F19[X]/(mu), write
x for the residue of X. The successive nineteenth powers are

$$\begin{array}{c|l}
i&x^{19^i}\\\hline
0&x\\
1&-3x^4+x^3-9x^2-4x-7\\
2&3x^4-9x^3+x^2-6x+7\\
3&4x^4-6x^3+5x^2+7x-8\\
4&-4x^4-5x^3+3x^2+2x+8\\
5&x.
\end{array} \tag{CF2}$$

**Proof.** Repeated binary exponentiation and division by the displayed
monic mu gives the table. The Euclidean algorithm gives

$$\gcd\bigl(\mu,-3X^4+X^3-9X^2-5X-7\bigr)=1.$$

Thus mu divides X^(19^5)-X and is coprime to X^19-X. Every irreducible
factor consequently has degree dividing five and different from one.
As five is prime and mu has degree five, mu is irreducible. These are
exact polynomial remainder computations of degree at most four, not
enumerations of field elements.

#### CF4. All characteristic-19 extension degrees

**Theorem.** For every s>=1, q=19^s,

$$\boxed{
\gcd(T^{q^5}-T,M_{5,q})=
\begin{cases}
\mu(T^q-T),&s\equiv3\pmod5,\\
1,&s\not\equiv3\pmod5.
\end{cases}} \tag{CF3}$$

In particular Conjecture 4.2 of the cited version 2 holds.

**Proof.** Let theta be a common root and eta=theta^q-theta. CF2 makes
eta a root of mu, so its nineteenth-power orbit has length five by CF3.
The action eta->eta^q depends only on e=s modulo five. Put

$$u_j=\sum_{i=0}^{j-1}\eta^{q^i}\quad(1\le j\le5).$$

The closing condition is u_5=0 and the residual condition is
R(u_1,u_2,u_3,u_4)=0. If e=0, u_5=5eta is nonzero. For e=1,2,3,4,
the trace u_5 vanishes and reduction using CF2 gives the following
residuals, as polynomials in eta of degree at most four:

$$\begin{array}{c|l}
e&R(u_1,u_2,u_3,u_4)\\\hline
1&6\eta^4-6\eta^3+\eta^2+\eta-2\\
2&-3\eta^4+9\eta^3+6\eta^2+7\eta+1\\
3&0\\
4&-4\eta^4+7\eta^3+6\eta^2+4\eta+9.
\end{array} \tag{CF4}$$

Irreducibility of mu implies that none of the three nonzero polynomials
can vanish at eta. Hence a common root is possible only for e=3.

Conversely assume e=3 and take any root theta of mu(T^q-T). Its
eta=theta^q-theta is a root of mu. The same table proves both u_5=0
and R(u_1,...,u_4)=0. The telescoping identities
u_j=theta^(q^j)-theta then prove that theta is a common root.
Thus the common-root sets are exactly those asserted in CF3.

The polynomial T^(q^5)-T is squarefree since its derivative is -1.
The polynomial mu(T^q-T) is also squarefree: its derivative is
-mu'(T^q-T), and mu and mu' are coprime. Both relevant polynomials
are monic, so equality of their root sets gives the stated monic gcd.

#### CF5. Exact count and construction of the degree-five primes

**Corollary.** For q=19^s, s>=1, there are exactly q monic degree-five
Carlitz-Wieferich primes if s=3 modulo five, and none otherwise.

**Proof.** The criterion P|M_(5,q) for a monic irreducible polynomial P
of degree five is the standard Carlitz-Wieferich criterion of Thakur
and Bamunoba-Bergstrom, recorded as Lemma 2.1 in the cited paper.
For s=3 modulo five, the gcd has degree 5q. Every irreducible factor
has degree dividing five because it divides T^(q^5)-T. It has no
linear factor: for theta in F_q, eta=theta^q-theta=0 and mu(0)=-9
is nonzero. All its factors therefore have degree five, and their
number is q. They are distinct by squarefreeness. The other cases
have gcd one by CF4.

**Theorem.** Define the polynomial with prime-field coefficients

$$P_0(T)=T^5-6T^3+3T^2-9T-4\in\mathbb F_{19}[T].$$

For every s=3 modulo five, q=19^s, the complete set of monic degree-five
Carlitz-Wieferich primes over F_q is

$$\boxed{\{P_0(T-a):a\in\mathbb F_q\}.} \tag{CF5}$$

**Proof.** Choose a root eta of mu. Since s is coprime to five, eta has
degree five over F_q and its q-trace is zero. Put

$$\theta_0=\frac15\sum_{j=1}^4 j\eta^{q^j}
=6+8\eta^3-8\eta^4.$$

The first expression gives theta_0^q-theta_0=eta by telescoping: the
numerator difference is 5eta minus the trace. The second expression
follows from the table CF2 with q acting as the third Frobenius power.
Reduction modulo mu verifies P_0(theta_0)=0. The element theta_0 lies
in F_(19^5) and is not in F_q because its q-difference eta is nonzero;
hence it has degree five over F_q. Thus P_0 is its irreducible monic
polynomial and is Carlitz-Wieferich by CF4.

All q translates are distinct: translation by a nonzero gamma changes
the T^4 coefficient by 5gamma. They are irreducible and retain the
Carlitz residual because q-Frobenius differences are unchanged under
translation by F_q. The count already proved makes this the complete set.
For q=19^3 the polynomial in the source is translated to P_0 by replacing
T with T-(6+11c+17c^2), using c^3=8c^2+4c+11. This is a canonical member
of the previously known class, not an additional translation class.
The same P_0 is not Carlitz-Wieferich for the prime-field Carlitz action
q=19. The field defining the Carlitz Frobenius must be kept fixed.

#### CF.6 Sources and boundaries

Primary target: https://arxiv.org/html/2607.15305v2, Conjecture 4.2.
Its version date is 22 July 2026. The companion *Effective determination
of Carlitz-Wieferich primes of given degree* is listed there as in
preparation. The already proved counterexample and the known factor
in Theorem 4.1 are not counted as new results.

The original criterion is from D. S. Thakur, *Fermat versus Wilson
congruences, arithmetic derivatives and zeta values*, Finite Fields and
Their Applications 32 (2015), 192-206; see also A. S. Bamunoba and
J. Bergstrom, *A search for c-Wieferich primes*, International Journal
of Number Theory 17 (2021), 1599-1616, arXiv:2011.11727.

CF1-CF5 concern function-field Carlitz-Wieferich primes. They do not
establish an integer Wall-Sun-Sun prime. The finite five-orbit closure
and the additive Frobenius coordinate are specific arithmetic inputs;
replacing them with an integer Fibonacci congruence requires a separate
proved construction. The reusable method is simultaneous conjugate
closure followed by an explicit low-degree elimination identity, not
an identification of distinct Wieferich problems.

The formal companion proves CF2 with the actual residual equations and
an explicit coefficient certificate. The gcd and all-extension-degree
classification above are ordinary mathematical consequences with the
small polynomial remainders exposed. They are not asserted to have
received Lean kernel certification merely because the certificate has
an authored Lean representation.

<a id="wss-cx"></a>

### CX. Global characteristic support and two additional Carlitz families

This subsection belongs to the same Wieferich lifting-and-elimination problem
family as the integer WSS question and CF1-CF5. Throughout CX, the letter
r denotes the prime 519555805809266011. It is a field characteristic,
not an asserted integer WSS prime. Characteristic five is deliberately
excluded from the final nonconforming degree-five classification.

#### CX.1 A nonzero integer in the orbit ideal

Retain the five literal residual polynomials f_0,...,f_4 from CF, now in
Z[a,b,c,d]. Put tau(a,b,c,d)=(b-a,c-a,d-a,-a). Then tau^5 is the identity
and f_i=tau^i(f_0).

**Theorem CX1.** There is an explicitly specified integer polynomial S of
total degree ten such that

$$\boxed{\sum_{i=0}^{4}\tau^i(S)f_i=D,\qquad
D=4673196650932024062540600
=2^3 3^2 5^2\cdot19\cdot263\cdot r.}$$

There is also an integer polynomial S_3 of degree ten such that

$$\boxed{\sum_{i=0}^{4}\tau^i(S_3)f_i\equiv1\pmod3.}$$

**Proof.** The complete Horner expressions for S and S_3 are supplied on
the proof path of `CarlitzFiveCharacteristic.result`. They have508 and340
nonzero monomials respectively. Expand the five substitutions and multiply
by their quartics. For the first certificate every nonconstant integer
coefficient cancels and the constant coefficient is D. For the second,
every coefficient of the difference from one is divisible by three.
These are polynomial identities, independent of field size or any tested
prime range. The independent verifier parses the authored expressions
and checks their integer coefficients. A successful Groebner command is
not used as a mathematical premise.

**Corollary CX2.** If K is a field of odd prime characteristic p and an
actual ring endomorphism sigma and theta satisfy sigma^5(theta)=theta
and the degree-five residual, then

$$\boxed{p\in\{5,19,263,r\}.}$$

**Proof.** Applying sigma to the original residual yields all five
polynomials f_i=0. CX1 forces D=0 in K, hence p divides D. Its second
certificate excludes p=3. Factoring D leaves the asserted list. The
factor r is prime: a recursive Lucas primality certificate uses

$$r-1=2\cdot3\cdot5\cdot31\cdot71\cdot7868481081467.$$

The witness two has order r-1 modulo r, as verified by the congruence
2^(r-1)=1 and the gcd conditions for each distinct prime factor of r-1.
The recursive primality tree has19 nodes and is checked from the base2.
For the new Lean declaration the output is the exact divisibility
p | 8*25*19*263*r; it does not assume or certify the primality of r.
The full finite prime support is the ordinary corollary using the
separately supplied primality certificate.

#### CX.2 Explicit upper difference polynomials in the two new characteristics

Define the following monic polynomials, each over its indicated prime field:

$$m_{263}(X)=X^5+118X^3-29X^2-57X-11,$$

$$m_r(X)=X^5-126121936908049079X^3
-20709279787633690X^2+49850011469824031X
-48822819797228934.$$

**Theorem CX3.** Every common zero of f_0,...,f_4 in characteristic p,
for p=263 or p=r, satisfies m_p(d)=0.

**Exact finite verification.** In each characteristic there are five
polynomial multipliers V_i of total degree at most eight with

$$\sum_{i=0}^4 V_i f_i=m_p(d).$$

Exact Groebner reduction of m_p(d) by the five displayed residuals gives
zero remainder in both characteristics. An independent quotient-ring
recomputation gives the same two zero remainders, the tables in CX.3, and
the constructions in CX.4. Thus this is an exact finite polynomial
calculation rather than a sampled-root search. CX3-CX6 are ordinary
mathematical results; their calculations are not current Lean endpoints.

The coefficient search itself can be reproduced using the explicit
ansatz: take all 495 monomials in four variables of degree at most eight,
multiply each by each of the five quartics, and compare the 1820 coefficient
positions of degree at most twelve. Solving this 1820-by-2475 linear system
modulo p produces the displayed ideal membership. This is a finite
coefficient space; no enumeration of a finite field or prime candidate
space occurs.

#### CX.3 Irreducibility and all extension-degree cases

**Lemma.** Both m_p are irreducible over F_p. In the degree-five quotient,

$$X^{p^5}=X,\qquad \gcd(m_p,X^p-X)=1.$$

**Proof.** Binary powering and Euclidean division of the displayed monic
polynomials give the two exact remainders. Since five is prime, every
irreducible factor of a divisor of X^(p^5)-X has degree one or five;
the gcd excludes degree one. This proves irreducibility. The verification
bundle gives every arithmetic operation in a standard-library checker.

For e in {1,2,3,4}, in F_p[d]/(m_p), set

$$A_e=-d^{p^e},\quad B_e=-d^{p^e}-d^{p^{2e}},\quad
C_e=-d^{p^e}-d^{p^{2e}}-d^{p^{3e}}.$$

Let R_e=R(A_e,B_e,C_e,d). The coefficient lists below are in ascending
powers of d, with all entries taken modulo p. Empty means the zero
polynomial.

For p=263:

| e | coefficients of R_e |
|---|---|
|1|(183,220,12,4,154)|
|2|(30,211,26,167,232)|
|3|()|
|4|(154,204,206,168,178)|

For p=r:

| e | coefficients of R_e |
|---|---|
|1|(190517489712118051,453954193719581280,337654280384855023,339436209018876665,455577831796691642)|
|2|(508627157208596802,212497064539069456,291781918141666170,234967044749037575,344791609743198488)|
|3|(275489135042958680,277163834281479958,495778609882052580,289423878907630600,131513161327939832)|
|4|()|

**Theorem CX4.** Let p=263 or r, q=p^s, s>=1, and put

$$\nu_p(X)=-m_p(-X),\qquad e_{263}=3,\quad e_r=4.$$

Then

$$\boxed{
\gcd(T^{q^5}-T,M_{5,q})=
\begin{cases}
\nu_p(T^q-T),&s\equiv e_p\pmod5,\\
1,&s\not\equiv e_p\pmod5.
\end{cases}}$$

**Proof.** For a common root theta, let d=theta^(q^4)-theta. CX3 gives
m_p(d)=0. Its degree over F_p is five. The Frobenius action consequently
depends only on e=s mod5. Closedness gives

$$\theta^q-\theta=-d^q,\quad
\theta^{q^2}-\theta=-d^q-d^{q^2},\quad
\theta^{q^3}-\theta=-d^q-d^{q^2}-d^{q^3}.$$

It also gives Tr(d)=0. If e=0, that trace is5d, nonzero because p!=5
and m_p(0)!=0. If e!=0, the trace vanishes since the X^4 coefficient
of m_p is zero. The remainder table and irreducibility now force
exactly e=e_p: all other residuals are nonzero of degree less than five.
The formulas also imply nu_p(theta^q-theta)=0.

Conversely, suppose nu_p(theta^q-theta)=0 and s=e_p modulo five. Write
a=theta^q-theta and d=-a^(q^4). Then d is a root of m_p, a=-d^q,
and the trace of a over five Frobenius steps is zero. Telescoping gives
theta^(q^5)=theta. The same remainder table gives the required residual.
Thus the common-root set is exactly the one asserted. Both polynomials
whose roots are compared are squarefree: the derivative of T^(q^5)-T
is-1, and the derivative of nu_p(T^q-T) is -nu_p'(T^q-T), coprime to
it because nu_p is irreducible and separable. Monicity finishes the gcd.

#### CX.4 Actual prime polynomials and the complete nonconforming classification

Define

$$P_{263}(T)=T^5-25T^3-96T^2+67T-48,$$

$$P_r(T)=T^5-161075390461176250T^3+236246748108143654T^2
-67033555198929295T+76181904805977016.$$

**Theorem CX5.** For p=263 or r and s=e_p modulo five, the entire set
of monic degree-five Carlitz-Wieferich primes in F_(p^s)[T] is

$$\boxed{\{P_p(T-a):a\in\mathbb F_{p^s}\}.}$$

**Proof.** For p=263, a root d of m_p gives

$$\theta_0=42d^4-16d^3+13d^2+115d+123.$$
For p=r use

$$\theta_0=228292315964840347d^4+128383604335500605d^3
-185913959198815567d^2-41306496497157789d
+63808001016856156.$$

Exact reduction gives P_p(theta_0)=0 and theta_0^q-theta_0=-d^q.
The difference is nonzero, and theta_0 lies in F_(p^5), so its degree
over F_q is five when gcd(s,5)=1. Thus P_p is irreducible over each
admissible F_q. CX4 and the residual criterion make it Carlitz-Wieferich.
Alternatively, direct Horner evaluation of the original Carlitz action
verifies rho_(P_p)(1)=1 modulo P_p^2. Translation preserves all q-Frobenius
differences. The q translates are distinct because their T^4 coefficients
differ by5a. CX4 has degree5q and no linear factor, so all factors have
degree five and these q translates exhaust them.

For independent direct verification at all extension degrees, the five
residue tests s=1,...,5 suffice only after proving their periodicity:
if P_p is irreducible over F_p, then in F_p[T]/(P_p^2),

$$T^{p^{s+5}}-T^{p^s}=(T^{p^5}-T)^{p^s}=0\quad(s\ge1).$$

Indeed P_p divides T^(p^5)-T and p^s>=2. Every element of that quotient
is a polynomial in T, so its p^s-Frobenius has the same period five.
This is an exact algebraic reduction, not an extrapolation from ten tests.

**Theorem CX6.** For EVERY odd prime p!=5 and EVERY s>=1, the number
of monic degree-five Carlitz-Wieferich primes over F_(p^s) is

$$\boxed{
\begin{cases}
p^s,&p=19\text{ and }s\equiv3\pmod5,\\
p^s,&p=263\text{ and }s\equiv3\pmod5,\\
p^s,&p=r\text{ and }s\equiv4\pmod5,\\
0,&\text{otherwise}.
\end{cases}}$$

**Proof.** CX2 restricts the characteristics to19,263,r under the
stated domain. CF4-CF5 classify19, and CX4-CX5 classify the other two.
In particular the count is zero at s=1 for every odd prime p!=5.
This closes the degree-five nonconforming prime-field question uniformly
in p, beyond the finite table in Proposition5.2 of the source. It does
not exclude higher-degree nonconforming examples over prime fields,
and it makes no assertion for the conforming characteristic-five case.

#### CX.5 What this does and does not transfer to integer WSS

The integer constant D was derived before choosing a characteristic.
Its prime factors produced the two new candidate characteristics; explicit
Frobenius compatibility then selected the allowed extension classes and
constructed the actual prime polynomials. Both existence and nonexistence
are certified in this fixed degree, without a field-element scan.

This supplies a successful characteristic-independent elimination pattern
inside the unified Wieferich problem family. An integer-WSS transfer would
need a fixed or controlled-complexity integer system genuinely implied by
the ORIGINAL golden lifting condition, together with a nonzero integer
in its elimination ideal. The known finite logarithm polynomial instead
has degree p-1, and the existing golden-unit relations leave q_p free.
There is no proved map from those equations to the five residuals here.
In particular19,263,r are not claimed to be integer WSS primes, and
CX2 cannot be applied to them as an integer-WSS exclusion theorem.

The known nineteen family and its Conjecture4.2 proof are prior results
of this PR. The two new families, all-characteristic obstruction and
prime-field degree-five exclusion form one continuation, not several
independently counted open-problem solutions. Exact-characteristic and
polynomial searches did not locate the new families in the checked
primary literature. The companion paper listed as in preparation in
arXiv:2607.15305v2 could contain related work; priority and external
acceptance remain unconfirmed.


[Return to the problem dossier](../../Problems/wall-sun-sun-golden-unit-lift.md).
