---
slug: carlitz-wieferich-degree-five-exactness
bibkey: niedbala2026carlitz
doi: 10.48550/arXiv.2607.15305
triage: conjecture
motivation_gids:
  - D5/S3/Arith/FunctionField/CarlitzFiveOrbit
---

# Exactness of the degree-five Carlitz-Wieferich factor

## Problem

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

## Definitions

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

## Theorems and proofs

### CF1. A polynomial certificate valid in every characteristic-19 ring

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

### CF2. Closure under all five conjugate equations

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

### CF3. The five-dimensional difference field

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

### CF4. All characteristic-19 extension degrees

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

### CF5. Exact count and construction of the degree-five primes

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

## Sources and boundaries

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
