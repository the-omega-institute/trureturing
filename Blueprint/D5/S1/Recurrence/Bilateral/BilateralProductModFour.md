# The Bilateral Product Family of A381362 and A381363

## Abstract

Hanna's bilateral product family has every positive coefficient equal to two modulo four.

Paul D. Hanna's entries hanna2025a381362 and hanna2025a381363 specify the same bilateral product equation with parameters c=2 and c=3. Both conjecture a(n)=2 modulo four for every positive n. The common normalization is A(0)=1.

The parameters c, k, n, N, K, and d are natural numbers; j is an integer. A and B are integer power series. The operator iota embeds an integer power series into rational Laurent series by mapping its coefficients to the rationals and applying ofPowerSeries. The symbol x denotes iota(X). Laurent powers have integer exponents. Exponents in positiveTerm and negativeTerm are natural, including truncated subtraction c*k-1. The operator natAbs is the natural absolute value. The operation invOfUnit(F,1) uses the unit one for the constant coefficient; all its uses as inverses below have constant coefficient one. The operator mk constructs a power series from its coefficients.

**Definition 1.1 (Integral nonzero-index terms).**

$$\begin{aligned}\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall j: \mathbb{Z}, \operatorname{bilateralTerm}\left(c, A, j\right) = (\operatorname{if} (j = 0) \operatorname{then} 0 \operatorname{else} (\operatorname{if} (0 < j) \operatorname{then} \operatorname{positiveTerm}\left(c, A, \operatorname{natAbs}\left(j\right)\right) \operatorname{else} \operatorname{negativeTerm}\left(c, A, \operatorname{natAbs}\left(j\right)\right)))\\\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall k: \mathbb{N}, \operatorname{positiveTerm}\left(c, A, k\right) = ((X)^{k}) \cdot ((((A)^{k}) \cdot (((A)^{k} + X)^{(c) \cdot (k) - (1)})) \cdot (((X)^{k} + A)^{(c) \cdot (k) - (1)}))\\\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall k: \mathbb{N}, \operatorname{negativeTerm}\left(c, A, k\right) = ((X)^{(c) \cdot ((k)^{2})}) \cdot ((((A)^{(c) \cdot ((k)^{2})}) \cdot ((\operatorname{invOfUnit}\left(1 + (X) \cdot ((A)^{k}), 1\right))^{(c) \cdot (k) + 1})) \cdot ((\operatorname{invOfUnit}\left(1 + ((X)^{k}) \cdot (A), 1\right))^{(c) \cdot (k) + 1}))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.bilateralTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero term is isolated. For j=k>0 the original term contains X^k. For j=-k<0, factoring the inverse powers gives X^(c*k^2) times the displayed integral unit inverses. The negative factorization is also proved as an identity in a field.

**Definition 1.2 (The coefficientwise bilateral remainder).**

$$\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{nonzeroSum}\left(c, A\right) = \operatorname{mk}\left((N: \mathbb{N} \mapsto \sum_{j \in \operatorname{Icc}\left(-(N), N\right)} (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(c, A, j\right)\right)))\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.nonzeroSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At degree N the remainder sums the integral terms over [-N,N]. The following theorem proves independence of every larger window.

**Theorem 1.3 (Every coefficient has a finite window).**

$$\forall c: \mathbb{N}, (2 \le c) \implies (\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies ((\forall j: \mathbb{Z}, ((j < -(N)) \lor (N < j)) \implies (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(c, A, j\right)\right) = 0)) \land (\operatorname{coeff}\left(N, \operatorname{nonzeroSum}\left(c, A\right)\right) = \sum_{j \in \operatorname{Icc}\left(-(K), K\right)} (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(c, A, j\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.finite_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive term has a factor X^k and a negative term has a factor X^(c*k^2). For c at least two, either factor has degree at least k. Thus every index outside [-N,N] vanishes at degree N. Extending the finite sum only adds these zero coefficients.

**Definition 1.4 (Stabilized integral coefficients).**

$$\begin{aligned}G = \operatorname{invOfUnit}\left(1 + X, 1\right)\\\forall c: \mathbb{N}, \operatorname{P}\left(c, 0\right) = 1\\\forall c: \mathbb{N}, \forall d: \mathbb{N}, \operatorname{P}\left(c, d + 1\right) = (2) \cdot (G) - (1) + (2) \cdot ((1 + \operatorname{P}\left(c, d\right)) \cdot (\operatorname{nonzeroSum}\left(c, \operatorname{P}\left(c, d\right)\right)))\\\forall c: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{a}\left(c, n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(c, n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here P is the private approximation sequence and G is the inverse of 1+X. Differences of products, powers, and unit inverses preserve agreement below degree d. Every nonzero-index term supplies another factor X. The remainder has constant coefficient zero, so the displayed iteration improves agreement to degree d+1.

**Definition 1.5 (The generating series).**

$$\forall c: \mathbb{N}, \operatorname{generatingSeries}\left(c\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{a}\left(c, n\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The stabilized coefficients define an integer series for each natural c. The assertions about its equation and uniqueness assume c at least two.

**Theorem 1.6 (The normalized polynomial equation).**

$$\forall c: \mathbb{N}, (2 \le c) \implies ((\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\left(c\right)\right) = 1) \land (((1 + X) \cdot (1 + \operatorname{generatingSeries}\left(c\right))) \cdot (1 - ((2) \cdot (\operatorname{nonzeroSum}\left(c, \operatorname{generatingSeries}\left(c\right)\right)))) = 2))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.polynomial_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stabilization gives a fixed point of the integral iteration. Multiplying by 1+X gives the polynomial equation, and the zero constant coefficient of the remainder gives the normalization.

**Definition 1.7 (The literal bilateral summand).**

$$\begin{aligned}\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{iota}\left(A\right) = \operatorname{ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, \operatorname{map}\left(\operatorname{intCastRingHom}\left(\mathbb{Q}\right), A\right)\right)\\x = \operatorname{iota}\left(X\right)\\\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall j: \mathbb{Z}, \operatorname{laurentTerm}\left(c, A, j\right) = ((((x)^{j}) \cdot ((\operatorname{iota}\left(A\right))^{j})) \cdot (((\operatorname{iota}\left(A\right))^{j} + x)^{(c) \cdot (j) - (1)})) \cdot (((x)^{j} + \operatorname{iota}\left(A\right))^{(c) \cdot (j) - (1)})\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.laurentTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the summand in the two OEIS NAMEs, with c left arbitrary. The zero term is (1+x)^(-1)*(1+iota(A))^(-1). For every nonzero index the field factorization identifies it with iota(bilateralTerm).

**Theorem 1.8 (The defining Laurent-series equation).**

$$\forall c: \mathbb{N}, (2 \le c) \implies ((\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\left(c\right)\right) = 1) \land (\forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies (\sum_{j \in \operatorname{Icc}\left(-(K), K\right)} (\operatorname{coeff}\left(N, \operatorname{laurentTerm}\left(c, \operatorname{generatingSeries}\left(c\right), j\right)\right)) = (\operatorname{if} (N = 0) \operatorname{then} \frac{1}{2} \operatorname{else} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial equation implies that the zero Laurent term plus the embedded nonzero-index remainder is the constant one half. Coefficient comparison and the finite-window theorem give the equality for every N and every K at least N. This is the coefficientwise meaning of the bilateral sum in the NAMEs.

**Theorem 1.9 (Uniqueness for the literal equation).**

$$\forall c: \mathbb{N}, (2 \le c) \implies (\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((\forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies (\sum_{j \in \operatorname{Icc}\left(-(K), K\right)} (\operatorname{coeff}\left(N, \operatorname{laurentTerm}\left(c, B, j\right)\right)) = (\operatorname{if} (N = 0) \operatorname{then} \frac{1}{2} \operatorname{else} 0))) \implies (B = \operatorname{generatingSeries}\left(c\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero Laurent term comes from a rational power series. Equality of every nonnegative coefficient therefore recovers its power-series identity with the remainder. Clearing the two unit denominators gives the integral polynomial equation. Degree contraction then identifies any normalized integer solution with generatingSeries(c).

**Theorem 1.10 (The general coefficient congruence).**

$$\forall c: \mathbb{N}, (2 \le c) \implies (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(c, n\right) \bmod 4 = 2))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_general` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put H=nonzeroSum(c,A) and G=(1+X)^(-1). The fixed-point equation is A=2*G-1+2*(1+A)*H. Setting B=G+(1+A)*H gives 1+A=2*B and then A-(2*G-1)=4*B*H. The coefficient of G at n is (-1)^n. For n>0, twice this coefficient has remainder two modulo four.

**Theorem 1.11 (Hanna's A381362 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(2, n\right) \bmod 4 = 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381362` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381362-bilateral-product-quadratic-mod-four` (proved) by `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381362`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381362-bilateral-product-quadratic-mod-four","declaration_gid":"D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381362","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A381362, bilateral product generating function*. URL: <https://oeis.org/A381362>.

*Commentary.*

The parameter c=2 gives A381362 and satisfies the general theorem's parameter bound. The generating-equation and uniqueness theorems identify these coefficients with the normalized series in hanna2025a381362.

**Theorem 1.12 (Hanna's A381363 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(3, n\right) \bmod 4 = 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381363` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381363-bilateral-product-cubic-mod-four` (proved) by `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381363`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381363-bilateral-product-cubic-mod-four","declaration_gid":"D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381363","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A381363, bilateral product generating function*. URL: <https://oeis.org/A381363>.

*Commentary.*

The parameter c=3 gives A381363 and satisfies the general theorem's parameter bound. The generating-equation and uniqueness theorems identify these coefficients with the normalized series in hanna2025a381363.

## References

- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.a`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.bilateralTerm`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.finite_window`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381362`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381363`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_general`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.laurentTerm`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.nonzeroSum`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.polynomial_form`
