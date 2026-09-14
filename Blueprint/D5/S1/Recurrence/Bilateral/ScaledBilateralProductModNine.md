# The Scaled Bilateral Product Family of A381364 and A381365

## Abstract

Hanna's scaled bilateral product family has every positive coefficient equal to six modulo nine.

Paul D. Hanna's entries hanna2025a381364 and hanna2025a381365 specify the same bilateral product equation with parameters c=1 and c=2. Both conjecture a(n)=6 modulo nine for every positive n. The common normalization is A(0)=1.

The parameters c, k, n, N, K, and d are natural numbers; j is an integer. A and B are integer power series. The operator iota embeds an integer power series into rational Laurent series by mapping its coefficients to the rationals and applying ofPowerSeries. The symbol x denotes iota(X). Laurent powers have integer exponents. Exponents in positiveTerm and negativeTerm are natural, including truncated subtraction c*k-1. The operator natAbs is the natural absolute value. The operation invOfUnit(F,1) uses the unit one for the constant coefficient; on nonzero-index branches its arguments have constant coefficient one. The operator mk constructs a power series from its coefficients. The operator div denotes integer division and mod is integer remainder. Integer casts of natural indices and parameters are implicit in Laurent exponents and coefficients.

**Definition 1.1 (Integral nonzero-index terms).**

$$\begin{aligned}\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall j: \mathbb{Z}, \operatorname{bilateralTerm}\left(c, A, j\right) = (\operatorname{if} (j = 0) \operatorname{then} 0 \operatorname{else} (\operatorname{if} (0 < j) \operatorname{then} \operatorname{positiveTerm}\left(c, A, \operatorname{natAbs}\left(j\right)\right) \operatorname{else} \operatorname{negativeTerm}\left(c, A, \operatorname{natAbs}\left(j\right)\right)))\\\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall k: \mathbb{N}, \operatorname{positiveTerm}\left(c, A, k\right) = ((X)^{k}) \cdot ((((A)^{k}) \cdot (((A)^{k} + (2) \cdot (X))^{(c) \cdot (k) - (1)})) \cdot (((X)^{k} + (2) \cdot (A))^{(c) \cdot (k) - (1)}))\\\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall k: \mathbb{N}, \operatorname{negativeTerm}\left(c, A, k\right) = ((X)^{(c) \cdot ((k)^{2})}) \cdot ((((A)^{(c) \cdot ((k)^{2})}) \cdot ((\operatorname{invOfUnit}\left(1 + ((2) \cdot (X)) \cdot ((A)^{k}), 1\right))^{(c) \cdot (k) + 1})) \cdot ((\operatorname{invOfUnit}\left(1 + ((2) \cdot ((X)^{k})) \cdot (A), 1\right))^{(c) \cdot (k) + 1}))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.bilateralTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero term is isolated. For j=k>0 the original term contains X^k. For j=-k<0, factoring the inverse powers gives X^(c*k^2) times the displayed integral unit inverses. The negative factorization is also proved as an identity in a field.

**Definition 1.2 (The coefficientwise bilateral remainder).**

$$\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{nonzeroSum}\left(c, A\right) = \operatorname{mk}\left((N: \mathbb{N} \mapsto \sum_{j \in \operatorname{Icc}\left(-(N), N\right)} (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(c, A, j\right)\right)))\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.nonzeroSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At degree N the remainder sums the integral terms over [-N,N]. The following theorem proves independence of every larger window.

**Theorem 1.3 (Every coefficient has a finite window).**

$$\forall c: \mathbb{N}, (1 \le c) \implies (\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies ((\forall j: \mathbb{Z}, ((j < -(N)) \lor (N < j)) \implies (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(c, A, j\right)\right) = 0)) \land (\operatorname{coeff}\left(N, \operatorname{nonzeroSum}\left(c, A\right)\right) = \sum_{j \in \operatorname{Icc}\left(-(K), K\right)} (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(c, A, j\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.finite_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive term has a factor X^k and a negative term has a factor X^(c*k^2). For c at least one, either factor has degree at least k. Thus every index outside [-N,N] vanishes at degree N. Extending the finite sum only adds these zero coefficients.

**Definition 1.4 (Stabilized integral coefficients).**

$$\begin{aligned}G = \operatorname{invOfUnit}\left(1 + (2) \cdot (X), 1\right)\\\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{halfSum}\left(c, A\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{div}\left(\operatorname{coeff}\left(n, \operatorname{nonzeroSum}\left(c, A\right)\right), 2\right))\right)\\\forall c: \mathbb{N}, \operatorname{P}\left(c, 0\right) = 1\\\forall c: \mathbb{N}, \forall d: \mathbb{N}, \operatorname{P}\left(c, d + 1\right) = 1 - (((3) \cdot (X)) \cdot (G)) + (3) \cdot ((1 + (2) \cdot (\operatorname{P}\left(c, d\right))) \cdot (\operatorname{halfSum}\left(c, \operatorname{P}\left(c, d\right)\right)))\\\forall c: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{a}\left(c, n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(c, n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here P is the private approximation sequence and G is the inverse of 1+2*X. For c at least one, pairing indices k and -k gives an even remainder: both terms reduce to X^(c*k^2)*A^(c*k^2) modulo two. Thus halfSum is exact coefficientwise division by two. Differences of products, powers, and unit inverses preserve agreement below degree d. Every nonzero-index term supplies another factor X. The remainder has constant coefficient zero, so the displayed iteration improves agreement to degree d+1.

**Definition 1.5 (The generating series).**

$$\forall c: \mathbb{N}, \operatorname{generatingSeries}\left(c\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{a}\left(c, n\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal coefficients define an integer series for each natural c. Stabilization and the assertions about its equation and uniqueness assume c at least one.

**Theorem 1.6 (The normalized polynomial equation).**

$$\forall c: \mathbb{N}, (1 \le c) \implies ((\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\left(c\right)\right) = 1) \land (((1 + (2) \cdot (X)) \cdot (1 + (2) \cdot (\operatorname{generatingSeries}\left(c\right)))) \cdot (1 - ((3) \cdot (\operatorname{nonzeroSum}\left(c, \operatorname{generatingSeries}\left(c\right)\right)))) = 3))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.polynomial_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stabilization gives a fixed point of the integral iteration. Multiplying by 1+2*X and using nonzeroSum=2*halfSum gives the polynomial equation. The zero constant coefficient of the remainder gives the normalization.

**Definition 1.7 (The literal bilateral summand).**

$$\begin{aligned}\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{iota}\left(A\right) = \operatorname{ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, \operatorname{map}\left(\operatorname{intCastRingHom}\left(\mathbb{Q}\right), A\right)\right)\\x = \operatorname{iota}\left(X\right)\\\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall j: \mathbb{Z}, \operatorname{laurentTerm}\left(c, A, j\right) = ((((x)^{j}) \cdot ((\operatorname{iota}\left(A\right))^{j})) \cdot (((\operatorname{iota}\left(A\right))^{j} + (2) \cdot (x))^{(c) \cdot (j) - (1)})) \cdot (((x)^{j} + (2) \cdot (\operatorname{iota}\left(A\right)))^{(c) \cdot (j) - (1)})\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.laurentTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the summand in the two OEIS NAMEs, with c left arbitrary. The zero term is (1+2*x)^(-1)*(1+2*iota(A))^(-1). When c is at least one and constantCoeff(A)=1, the field factorization identifies every nonzero index term with iota(bilateralTerm).

**Theorem 1.8 (The defining Laurent-series equation).**

$$\forall c: \mathbb{N}, (1 \le c) \implies ((\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\left(c\right)\right) = 1) \land (\forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies (\sum_{j \in \operatorname{Icc}\left(-(K), K\right)} (\operatorname{coeff}\left(N, \operatorname{laurentTerm}\left(c, \operatorname{generatingSeries}\left(c\right), j\right)\right)) = (\operatorname{if} (N = 0) \operatorname{then} \frac{1}{3} \operatorname{else} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial equation implies that the zero Laurent term plus the embedded nonzero-index remainder is the constant one third. Coefficient comparison and the finite-window theorem give the equality for every N and every K at least N. This is the coefficientwise meaning of the bilateral sum in the NAMEs.

**Theorem 1.9 (Uniqueness for the literal equation).**

$$\forall c: \mathbb{N}, (1 \le c) \implies (\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((\forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies (\sum_{j \in \operatorname{Icc}\left(-(K), K\right)} (\operatorname{coeff}\left(N, \operatorname{laurentTerm}\left(c, B, j\right)\right)) = (\operatorname{if} (N = 0) \operatorname{then} \frac{1}{3} \operatorname{else} 0))) \implies (B = \operatorname{generatingSeries}\left(c\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero Laurent term comes from a rational power series. Equality of every nonnegative coefficient therefore recovers its power-series identity with the remainder. Clearing the two unit denominators gives the integral polynomial equation. Degree contraction then identifies any normalized integer solution with generatingSeries(c).

**Theorem 1.10 (The general coefficient congruence).**

$$\forall c: \mathbb{N}, (1 \le c) \implies (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(c, n\right) \bmod 9 = 6))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.hanna_conjecture_general` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put A=generatingSeries(c), J=halfSum(c,A), and G=(1+2*X)^(-1). Recovering the polynomial form from the literal generating equation gives A=1-3*X*G+3*(1+2*A)*J. Setting B=-X*G+(1+2*A)*J gives A=1+3*B, hence 1+2*A=3*(1+2*B) and A-(1-3*X*G)=9*(1+2*B)*J. At n=m+1 the coefficient of 1-3*X*G is -3*(-2)^m. Since (-2)^m is one modulo three, this coefficient has remainder six modulo nine.

**Theorem 1.11 (Hanna's A381364 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(1, n\right) \bmod 9 = 6)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.hanna_conjecture_a381364` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381364-scaled-bilateral-product-linear-mod-nine` (proved) by `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.hanna_conjecture_a381364`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381364-scaled-bilateral-product-linear-mod-nine","declaration_gid":"D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.hanna_conjecture_a381364","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A381364, scaled bilateral product generating function*. URL: <https://oeis.org/A381364>.

*Commentary.*

The parameter c=1 gives A381364 and satisfies the general theorem's parameter bound. The generating-equation and uniqueness theorems identify these coefficients with the normalized series in hanna2025a381364.

**Theorem 1.12 (Hanna's A381365 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(2, n\right) \bmod 9 = 6)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.hanna_conjecture_a381365` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381365-scaled-bilateral-product-quadratic-mod-nine` (proved) by `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.hanna_conjecture_a381365`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381365-scaled-bilateral-product-quadratic-mod-nine","declaration_gid":"D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.hanna_conjecture_a381365","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A381365, scaled bilateral product generating function*. URL: <https://oeis.org/A381365>.

*Commentary.*

The parameter c=2 gives A381365 and satisfies the general theorem's parameter bound. The generating-equation and uniqueness theorems identify these coefficients with the normalized series in hanna2025a381365.

## References

- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.a`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.bilateralTerm`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.finite_window`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.hanna_conjecture_a381364`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.hanna_conjecture_a381365`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.hanna_conjecture_general`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.laurentTerm`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.nonzeroSum`
- Truth anchor: `D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.polynomial_form`
- Dependency: [D5/S1/Recurrence/Bilateral/BilateralProductModFour](BilateralProductModFour.md)
