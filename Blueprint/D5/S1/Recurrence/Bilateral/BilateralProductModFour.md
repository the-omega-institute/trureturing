# The Bilateral Product Family of A381362 and A381363

## Abstract

Hanna's bilateral product family has every positive coefficient equal to two modulo four.

**Definition 1.1 (The positive-index integral term).**

$$\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall k: \mathbb{N}, \operatorname{positiveTerm}\left(c, A, k\right) = ((X)^{k}) \cdot ((((A)^{k}) \cdot (((A)^{k} + X)^{(c) \cdot (k) - (1)})) \cdot (((X)^{k} + A)^{(c) \cdot (k) - (1)}))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.positiveTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The term at a positive index k contains X to the power k and the two polynomial factors in the bilateral product.

**Definition 1.2 (The negative-index integral term).**

$$\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall k: \mathbb{N}, \operatorname{negativeTerm}\left(c, A, k\right) = ((X)^{(c) \cdot ((k)^{2})}) \cdot ((((A)^{(c) \cdot ((k)^{2})}) \cdot ((\operatorname{invOfUnit}\left(1 + (X) \cdot ((A)^{k}), 1\right))^{(c) \cdot (k) + 1})) \cdot ((\operatorname{invOfUnit}\left(1 + ((X)^{k}) \cdot (A), 1\right))^{(c) \cdot (k) + 1}))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.negativeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Factoring the negative Laurent powers produces X to the power c*k squared and integral unit inverses.

**Definition 1.3 (Agreement below a degree).**

$$\forall d: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{Agree}\left(d, A, B\right)) \Leftrightarrow (\forall n: \mathbb{N}, (n < d) \implies (\operatorname{coeff}\left(n, A\right) = \operatorname{coeff}\left(n, B\right)))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.Agree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two integer power series agree below d exactly when their coefficients at every n less than d coincide.

**Theorem 1.4 (Agreement is divisibility by a power of X).**

$$\forall d: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{Agree}\left(d, A, B\right)) \Leftrightarrow (\operatorname{Dvd}\left((X)^{d}, A - (B)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement below d is equivalent to divisibility of the difference by X to the power d.

**Theorem 1.5 (A series agrees with itself).**

$$\forall d: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{Agree}\left(d, A, A\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_refl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer power series agrees with itself below every natural degree.

**Theorem 1.6 (Sums preserve agreement).**

$$\forall d: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall G: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{Agree}\left(d, A, B\right)) \implies ((\operatorname{Agree}\left(d, F, G\right)) \implies (\operatorname{Agree}\left(d, A + F, B + G\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding two pairs of series that agree below d preserves agreement below d.

**Theorem 1.7 (Products preserve agreement).**

$$\forall d: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall G: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{Agree}\left(d, A, B\right)) \implies ((\operatorname{Agree}\left(d, F, G\right)) \implies (\operatorname{Agree}\left(d, (A) \cdot (F), (B) \cdot (G)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying two pairs of series that agree below d preserves agreement below d.

**Theorem 1.8 (Natural powers preserve agreement).**

$$\forall d: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall k: \mathbb{N}, (\operatorname{Agree}\left(d, A, B\right)) \implies (\operatorname{Agree}\left(d, (A)^{k}, (B)^{k}\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal coefficients below d remain equal after taking the same natural power.

**Theorem 1.9 (Normalized unit inverses preserve agreement).**

$$\forall d: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(A\right) = 1) \implies ((\operatorname{constantCoeff}\left(B\right) = 1) \implies ((\operatorname{Agree}\left(d, A, B\right)) \implies (\operatorname{Agree}\left(d, \operatorname{invOfUnit}\left(A, 1\right), \operatorname{invOfUnit}\left(B, 1\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two series of constant coefficient one, agreement below d passes to their integral unit inverses.

**Theorem 1.10 (A positive shift improves agreement).**

$$\forall d: \mathbb{N}, \forall k: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (0 < k) \implies ((\operatorname{Agree}\left(d, A, B\right)) \implies (\operatorname{Agree}\left(d + 1, ((X)^{k}) \cdot (A), ((X)^{k}) \cdot (B)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by X to any positive power improves agreement from d to d+1.

**Definition 1.11 (The integral geometric series).**

$$\operatorname{geometric} = \operatorname{invOfUnit}\left(1 + X, 1\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.geometric` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is invOfUnit(1+X,1), the normalized integral inverse of 1+X.

**Theorem 1.12 (The geometric inverse identity).**

$$(\operatorname{geometric}) \cdot (1 + X) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.geometric_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the geometric series by 1+X gives one.

**Theorem 1.13 (The alternating geometric coefficients).**

$$\forall n: \mathbb{N}, \operatorname{coeff}\left(n, \operatorname{geometric}\right) = (-(1))^{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.geometric_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient at every natural n is (-1) to the power n.

**Definition 1.14 (The integral fixed-point operator).**

$$\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{step}\left(c, A\right) = (2) \cdot (\operatorname{geometric}) - (1) + (2) \cdot ((1 + A) \cdot (\operatorname{nonzeroSum}\left(c, A\right)))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural c and integer series A, the step is 2*geometric-1+2*(1+A)*nonzeroSum(c,A).

**Definition 1.15 (The successive integral approximations).**

$$\forall c: \mathbb{N}, (\operatorname{approximation}\left(c, 0\right) = 1) \land (\forall d: \mathbb{N}, \operatorname{approximation}\left(c, d + 1\right) = \operatorname{step}\left(c, \operatorname{approximation}\left(c, d\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.approximation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial approximation is one; each successor is obtained by applying step at the same parameter c.

**Theorem 1.16 (The polynomial equation is the fixed-point equation).**

$$\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (((1 + X) \cdot (1 + A)) \cdot (1 - ((2) \cdot (\operatorname{nonzeroSum}\left(c, A\right)))) = 2) \Leftrightarrow (A = \operatorname{step}\left(c, A\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.equation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c and integer series A, multiplying out the polynomial equation is equivalent to A=step(c,A).

**Definition 1.17 (Embedding integer series into rational Laurent series).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{embed}\left(A\right) = \operatorname{HahnSeries.ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, \operatorname{PowerSeries.map}\left(\operatorname{Int.castRingHom}\left(\mathbb{Q}\right), A\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.embed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map each integer coefficient to the rationals and then apply HahnSeries.ofPowerSeries with integer exponents.

**Theorem 1.18 (The embedding preserves nonnegative coefficients).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall n: \mathbb{N}, \operatorname{HahnSeries.coeff}\left(\operatorname{embed}\left(A\right), \operatorname{Int.ofNat}\left(n\right)\right) = \operatorname{Int.cast}\left(\operatorname{coeff}\left(n, A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.embed_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each natural degree N, the Laurent coefficient is the rational image of the original integer coefficient.

**Theorem 1.19 (The Laurent embedding is injective).**

$$\operatorname{Function.Injective}\left(\operatorname{embed}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.embed_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the embedded Laurent series implies equality of the original integer power series.

**Theorem 1.20 (The embedding preserves a normalized inverse).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(A\right) = 1) \implies (\operatorname{embed}\left(\operatorname{invOfUnit}\left(A, 1\right)\right) = (\operatorname{embed}\left(A\right))^{-(1)})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.embed_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an integer series with constant coefficient one, the embedding sends invOfUnit(A,1) to the inverse of embed(A).

**Theorem 1.21 (Factoring a negative Laurent summand).**

$$\forall F: \operatorname{Type}, \forall field: \operatorname{Field}\left(F\right), \forall x: F, \forall u: F, \forall c: \mathbb{N}, \forall k: \mathbb{N}, (x \ne 0) \implies ((u \ne 0) \implies (((((x)^{-(k)}) \cdot ((u)^{-(k)})) \cdot (((u)^{-(k)} + x)^{-((c) \cdot (k) + 1)})) \cdot (((x)^{-(k)} + u)^{-((c) \cdot (k) + 1)}) = ((x)^{(c) \cdot ((k)^{2})}) \cdot ((((u)^{(c) \cdot ((k)^{2})}) \cdot (((1 + (x) \cdot ((u)^{k}))^{-(1)})^{(c) \cdot (k) + 1})) \cdot (((1 + ((x)^{k}) \cdot (u))^{-(1)})^{(c) \cdot (k) + 1}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.negative_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any field, nonzero x and u satisfy the negative-index factorization for every natural c and k, including k=0.

**Theorem 1.22 (The zero-index Laurent term).**

$$\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{laurentTerm}\left(c, A, 0\right) = ((1 + \operatorname{embed}\left(X\right))^{-(1)}) \cdot ((1 + \operatorname{embed}\left(A\right))^{-(1)})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.laurent_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At index zero the literal summand is the product of the inverses of 1+embed(X) and 1+embed(A).

**Theorem 1.23 (The zero Laurent term comes from a rational power series).**

$$\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(A\right) = 1) \implies (\operatorname{laurentTerm}\left(c, A, 0\right) = \operatorname{HahnSeries.ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, ((1 + X)^{-(1)}) \cdot ((1 + \operatorname{PowerSeries.map}\left(\operatorname{Int.castRingHom}\left(\mathbb{Q}\right), A\right))^{-(1)})\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.zeroTerm_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For constant coefficient A(0)=1, the zero term is the Laurent embedding of (1+X) inverse times (1+map(A)) inverse over the rationals.

**Theorem 1.24 (Laurent embedding preserves an inverse).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(B\right) \ne 0) \implies (\operatorname{HahnSeries}.\operatorname{ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, (B)^{-(1)}\right) = (\operatorname{HahnSeries}.\operatorname{ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, B\right))^{-(1)})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.ofSeries_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a rational power series whose constant coefficient is nonzero, ofPowerSeries sends its power-series inverse to its Laurent-series inverse.

Paul D. Hanna's entries hanna2025a381362 and hanna2025a381363 specify the same bilateral product equation with parameters c=2 and c=3. Both conjecture a(n)=2 modulo four for every positive n. The common normalization is A(0)=1.

The parameters c, k, n, N, K, and d are natural numbers; j is an integer. A and B are integer power series. The operator iota embeds an integer power series into rational Laurent series by mapping its coefficients to the rationals and applying ofPowerSeries. The symbol x denotes iota(X). Laurent powers have integer exponents. Exponents in positiveTerm and negativeTerm are natural, including truncated subtraction c*k-1. The operator natAbs is the natural absolute value. The operation invOfUnit(F,1) uses the unit one for the constant coefficient; all its uses as inverses below have constant coefficient one. The operator mk constructs a power series from its coefficients.

**Definition 1.25 (Integral nonzero-index terms).**

$$\begin{aligned}\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall j: \mathbb{Z}, \operatorname{bilateralTerm}\left(c, A, j\right) = (\operatorname{if} (j = 0) \operatorname{then} 0 \operatorname{else} (\operatorname{if} (0 < j) \operatorname{then} \operatorname{positiveTerm}\left(c, A, \operatorname{natAbs}\left(j\right)\right) \operatorname{else} \operatorname{negativeTerm}\left(c, A, \operatorname{natAbs}\left(j\right)\right)))\\\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall k: \mathbb{N}, \operatorname{positiveTerm}\left(c, A, k\right) = ((X)^{k}) \cdot ((((A)^{k}) \cdot (((A)^{k} + X)^{(c) \cdot (k) - (1)})) \cdot (((X)^{k} + A)^{(c) \cdot (k) - (1)}))\\\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall k: \mathbb{N}, \operatorname{negativeTerm}\left(c, A, k\right) = ((X)^{(c) \cdot ((k)^{2})}) \cdot ((((A)^{(c) \cdot ((k)^{2})}) \cdot ((\operatorname{invOfUnit}\left(1 + (X) \cdot ((A)^{k}), 1\right))^{(c) \cdot (k) + 1})) \cdot ((\operatorname{invOfUnit}\left(1 + ((X)^{k}) \cdot (A), 1\right))^{(c) \cdot (k) + 1}))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.bilateralTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero term is isolated. For j=k>0 the original term contains X^k. For j=-k<0, factoring the inverse powers gives X^(c*k^2) times the displayed integral unit inverses. The negative factorization is also proved as an identity in a field.

**Definition 1.26 (The coefficientwise bilateral remainder).**

$$\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{nonzeroSum}\left(c, A\right) = \operatorname{mk}\left((N: \mathbb{N} \mapsto \sum_{j \in \operatorname{Icc}\left(-(N), N\right)} (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(c, A, j\right)\right)))\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.nonzeroSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At degree N the remainder sums the integral terms over [-N,N]. The following theorem proves independence of every larger window.

**Theorem 1.27 (Every coefficient has a finite window).**

$$\forall c: \mathbb{N}, (2 \le c) \implies (\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies ((\forall j: \mathbb{Z}, ((j < -(N)) \lor (N < j)) \implies (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(c, A, j\right)\right) = 0)) \land (\operatorname{coeff}\left(N, \operatorname{nonzeroSum}\left(c, A\right)\right) = \sum_{j \in \operatorname{Icc}\left(-(K), K\right)} (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(c, A, j\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.finite_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive term has a factor X^k and a negative term has a factor X^(c*k^2). For c at least two, either factor has degree at least k. Thus every index outside [-N,N] vanishes at degree N. Extending the finite sum only adds these zero coefficients.

**Definition 1.28 (Stabilized integral coefficients).**

$$\begin{aligned}G = \operatorname{invOfUnit}\left(1 + X, 1\right)\\\forall c: \mathbb{N}, \operatorname{P}\left(c, 0\right) = 1\\\forall c: \mathbb{N}, \forall d: \mathbb{N}, \operatorname{P}\left(c, d + 1\right) = (2) \cdot (G) - (1) + (2) \cdot ((1 + \operatorname{P}\left(c, d\right)) \cdot (\operatorname{nonzeroSum}\left(c, \operatorname{P}\left(c, d\right)\right)))\\\forall c: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{a}\left(c, n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(c, n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here P is the approximation sequence and G is the inverse of 1+X. Differences of products, powers, and unit inverses preserve agreement below degree d. Every nonzero-index term supplies another factor X. The remainder has constant coefficient zero, so the displayed iteration improves agreement to degree d+1.

**Definition 1.29 (The generating series).**

$$\forall c: \mathbb{N}, \operatorname{generatingSeries}\left(c\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{a}\left(c, n\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The stabilized coefficients define an integer series for each natural c. The assertions about its equation and uniqueness assume c at least two.

**Theorem 1.30 (The normalized polynomial equation).**

$$\forall c: \mathbb{N}, (2 \le c) \implies ((\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\left(c\right)\right) = 1) \land (((1 + X) \cdot (1 + \operatorname{generatingSeries}\left(c\right))) \cdot (1 - ((2) \cdot (\operatorname{nonzeroSum}\left(c, \operatorname{generatingSeries}\left(c\right)\right)))) = 2))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.polynomial_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stabilization gives a fixed point of the integral iteration. Multiplying by 1+X gives the polynomial equation, and the zero constant coefficient of the remainder gives the normalization.

**Definition 1.31 (The literal bilateral summand).**

$$\begin{aligned}\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{iota}\left(A\right) = \operatorname{ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, \operatorname{map}\left(\operatorname{intCastRingHom}\left(\mathbb{Q}\right), A\right)\right)\\x = \operatorname{iota}\left(X\right)\\\forall c: \mathbb{N}, \forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall j: \mathbb{Z}, \operatorname{laurentTerm}\left(c, A, j\right) = ((((x)^{j}) \cdot ((\operatorname{iota}\left(A\right))^{j})) \cdot (((\operatorname{iota}\left(A\right))^{j} + x)^{(c) \cdot (j) - (1)})) \cdot (((x)^{j} + \operatorname{iota}\left(A\right))^{(c) \cdot (j) - (1)})\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralProductModFour.laurentTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the summand in the two OEIS NAMEs, with c left arbitrary. The zero term is (1+x)^(-1)*(1+iota(A))^(-1). For every nonzero index the field factorization identifies it with iota(bilateralTerm).

**Theorem 1.32 (The defining Laurent-series equation).**

$$\forall c: \mathbb{N}, (2 \le c) \implies ((\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\left(c\right)\right) = 1) \land (\forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies (\sum_{j \in \operatorname{Icc}\left(-(K), K\right)} (\operatorname{coeff}\left(N, \operatorname{laurentTerm}\left(c, \operatorname{generatingSeries}\left(c\right), j\right)\right)) = (\operatorname{if} (N = 0) \operatorname{then} \frac{1}{2} \operatorname{else} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial equation implies that the zero Laurent term plus the embedded nonzero-index remainder is the constant one half. Coefficient comparison and the finite-window theorem give the equality for every N and every K at least N. This is the coefficientwise meaning of the bilateral sum in the NAMEs.

**Theorem 1.33 (Uniqueness for the literal equation).**

$$\forall c: \mathbb{N}, (2 \le c) \implies (\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((\forall N: \mathbb{N}, \forall K: \mathbb{N}, (N \le K) \implies (\sum_{j \in \operatorname{Icc}\left(-(K), K\right)} (\operatorname{coeff}\left(N, \operatorname{laurentTerm}\left(c, B, j\right)\right)) = (\operatorname{if} (N = 0) \operatorname{then} \frac{1}{2} \operatorname{else} 0))) \implies (B = \operatorname{generatingSeries}\left(c\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero Laurent term comes from a rational power series. Equality of every nonnegative coefficient therefore recovers its power-series identity with the remainder. Clearing the two unit denominators gives the integral polynomial equation. Degree contraction then identifies any normalized integer solution with generatingSeries(c).

**Theorem 1.34 (The general coefficient congruence).**

$$\forall c: \mathbb{N}, (2 \le c) \implies (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(c, n\right) \bmod 4 = 2))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_general` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put H=nonzeroSum(c,A) and G=(1+X)^(-1). The fixed-point equation is A=2*G-1+2*(1+A)*H. Setting B=G+(1+A)*H gives 1+A=2*B and then A-(2*G-1)=4*B*H. The coefficient of G at n is (-1)^n. For n>0, twice this coefficient has remainder two modulo four.

**Theorem 1.35 (Hanna's A381362 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(2, n\right) \bmod 4 = 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381362` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381362-bilateral-product-quadratic-mod-four` (proved) by `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381362`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381362-bilateral-product-quadratic-mod-four","declaration_gid":"D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381362","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A381362, bilateral product generating function*. URL: <https://oeis.org/A381362>.

*Commentary.*

The parameter c=2 gives A381362 and satisfies the general theorem's parameter bound. The generating-equation and uniqueness theorems identify these coefficients with the normalized series in hanna2025a381362.

**Theorem 1.36 (Hanna's A381363 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(3, n\right) \bmod 4 = 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381363` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381363-bilateral-product-cubic-mod-four` (proved) by `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381363`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381363-bilateral-product-cubic-mod-four","declaration_gid":"D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381363","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A381363, bilateral product generating function*. URL: <https://oeis.org/A381363>.

*Commentary.*

The parameter c=3 gives A381363 and satisfies the general theorem's parameter bound. The generating-equation and uniqueness theorems identify these coefficients with the normalized series in hanna2025a381363.

## References

- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.Agree`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.a`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_add`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_iff`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_inverse`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_mul`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_pow`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_refl`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.agree_shift`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.approximation`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.bilateralTerm`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.embed`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.embed_coeff`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.embed_injective`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.embed_inverse`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.equation_iff`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.finite_window`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.geometric`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.geometric_coeff`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.geometric_spec`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381362`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_a381363`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.hanna_conjecture_general`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.laurentTerm`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.laurent_zero`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.negativeTerm`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.negative_factorization`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.nonzeroSum`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.ofSeries_inverse`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.polynomial_form`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.positiveTerm`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.step`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralProductModFour.zeroTerm_series`
