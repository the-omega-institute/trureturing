# A396808 Odd Exactly at Powers of Two

## Abstract

An Artin-Schreier trace invariant proves the first parity conjecture for OEIS A396808.

**Definition 1.1 (The finite-prefix sequence).**

$$\begin{aligned}a: \mathbb{N} \to \mathbb{Z},\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{ite}\left(n < 2, 1, \operatorname{castZ}\left(n\right) \cdot \operatorname{coeff}\left(n, \operatorname{prefixPolynomial}\left(n\right)^{n + 2}\right) - (\operatorname{castZ}\left(n\right) + 1) \cdot \operatorname{coeff}\left(n, \operatorname{prefixPolynomial}\left(n\right)^{n + 1}\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each n, P_n is the polynomial containing exactly the earlier coefficients. The first two values are one. At every later index, a(n) is n times coefficient n of P_n to power n+2, minus n+1 times coefficient n of P_n to power n+1. This is the triangular finite-prefix rule extracted from the defining equation of OEIS A396808. The symbols mk and coeff below denote PowerSeries.mk and PowerSeries.coeff, with the coefficient index written first; castZ is the natural-to-integer cast. Thus P_n determines a(n), and adjoining a(n) times X to power n produces P_(n+1).

**Definition 1.2 (The finite prefix polynomial).**

$$\begin{aligned}prefixPolynomial: \mathbb{N} \to \mathbb{Z}[X],\\\operatorname{prefixPolynomial}\left(0\right) = 0\\\forall n: \mathbb{N}, \operatorname{prefixPolynomial}\left(n + 1\right) = \operatorname{prefixPolynomial}\left(n\right) + \operatorname{a}\left(n\right) \cdot X^{n}\end{aligned}$$

*Formalization.* `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.prefixPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public prefix polynomial is initialized at zero and extends by the new coefficient a(n) at degree n. Consequently, the coefficient of X to power j in P_n is a(j) when j<n and zero otherwise.

**Theorem 1.3 (The finite prefix is the coefficient sum).**

$$\forall n: \mathbb{N}, \operatorname{prefixPolynomial}\left(n\right) = \sum_{j \in \operatorname{range}\left(n\right)} \operatorname{C}\left(\operatorname{a}\left(j\right)\right) \cdot X^{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.prefixPolynomial_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, prefixPolynomial(n) is exactly the finite sum over j in range(n) of the constant polynomial C(a(j)) times X to power j. Hence the recursive and finite-sum descriptions of P_n agree.

**Theorem 1.4 (The OEIS source equation).**

$$\forall n: \mathbb{N}, (1 < n) \Rightarrow (\operatorname{castZ}\left(n\right) + 1) \cdot \operatorname{coeff}\left(n, \operatorname{mk}\left(a\right)^{n + 1}\right) = \operatorname{castZ}\left(n\right) \cdot \operatorname{coeff}\left(n, \operatorname{mk}\left(a\right)^{n + 2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.source_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n greater than one, the formal power series mk(a) satisfies the coefficient equation in the OEIS name line. The strict-prefix coefficient formula isolates the contribution of a(n) to both powers, and the defining recurrence makes the resulting terms cancel.

**Theorem 1.5 (Uniqueness of the normalized integer solution).**

$$\forall b: (\mathbb{N} \to \mathbb{Z}), ((\operatorname{b}\left(0\right) = 1) \land ((\operatorname{b}\left(1\right) = 1) \land (\forall n: \mathbb{N}, (1 < n) \Rightarrow (\operatorname{castZ}\left(n\right) + 1) \cdot \operatorname{coeff}\left(n, \operatorname{mk}\left(b\right)^{n + 1}\right) = \operatorname{castZ}\left(n\right) \cdot \operatorname{coeff}\left(n, \operatorname{mk}\left(b\right)^{n + 2}\right)))) \Rightarrow b = a$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.normalized_solution_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any integer sequence b with b(0)=b(1)=1 and the same source equation at every n greater than one equals a. The proof recovers the nth coefficient from the strict prefix and then uses strong induction.

**Definition 1.6 (The Artin-Schreier coefficient recursion).**

$$\begin{aligned}artinCoeff: \mathbb{N} \to \operatorname{ZMod}\left(2\right),\\\operatorname{artinCoeff}\left(0\right) = 1\\\forall n: \mathbb{N}, \operatorname{artinCoeff}\left(2 \cdot n\right) = \operatorname{artinCoeff}\left(n\right)\\\forall n: \mathbb{N}, \operatorname{artinCoeff}\left(2 \cdot n + 1\right) = \operatorname{ite}\left(n = 0, 1, 0\right)\end{aligned}$$

*Formalization.* `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.artinCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public ZMod(2)-valued coefficient function starts at one, preserves its value on even indices by halving, and is one at an odd index 2n+1 exactly in the n=0 branch.

**Definition 1.7 (The constant-one Artin-Schreier series).**

$$\begin{aligned}S: \operatorname{ZMod}\left(2\right)[[X]],\\S = \operatorname{mk}\left(artinCoeff\right)\end{aligned}$$

*Formalization.* `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.artinSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient recursion defines S over ZMod(2). It has coefficient one at degree zero and at exactly the powers of two, so S is 1+x+x^2+x^4+x^8+.... Its constant term is one, while S+1 has constant term zero; these are the two roots of Y^2+Y=X.

**Theorem 1.8 (The Artin-Schreier equation).**

$$S^{2} + S = X$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.artinSeries_square_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Frobenius expansion shifts the nonconstant power-of-two support. In characteristic two, adding S cancels every repeated coefficient and leaves X.

**Definition 1.9 (The trace-polynomial recurrence).**

$$\begin{aligned}T: \mathbb{N} \to \operatorname{ZMod}\left(2\right)[X],\\T_{0} = 0\\T_{1} = 1\\\forall m: \mathbb{N}, T_{m + 2} = T_{m + 1} + X \cdot T_{m}\end{aligned}$$

*Formalization.* `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.tracePoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomials T_m over ZMod(2) start at zero and one and satisfy T_(m+2)=T_(m+1)+X*T_m. This is the trace recurrence for the two roots of Y^2+Y=X.

**Theorem 1.10 (Trace as the sum over both roots).**

$$\forall m: \mathbb{N}, \operatorname{coe}\left(T_{m}\right) = S^{m} + (S + 1)^{m}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.tracePoly_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural exponent m, coercing T_m to a formal power series equals S^m+(S+1)^m. Both roots obey the same two-step power recurrence, which proves the identity by two-step induction. Here T_m is viewed as a formal power series through the coefficientwise embedding of polynomials.

**Theorem 1.11 (Trace degree bound).**

$$\forall m: \mathbb{N}, \operatorname{natDegree}\left(T_{m}\right) \le \operatorname{div}\left(m, 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.tracePoly_natDegree_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural degree of T_m is at most the natural-number quotient m div 2. Here div is truncated natural division, equivalently floor(m/2); it is deliberately not rendered as field division.

**Theorem 1.12 (Vanishing between half the exponent and the exponent).**

$$\forall m, n: \mathbb{N}, (\operatorname{div}\left(m, 2\right) < n) \Rightarrow (n < m) \Rightarrow \operatorname{coeff}\left(n, S^{m}\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.coeff_artinSeries_pow_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If floor(m/2)<n<m, coefficient n of S^m is zero. The degree bound kills coefficient n of T_m, while S+1 has zero constant coefficient and therefore its mth power has no coefficient below m. The trace identity then forces coefficient n of S^m to vanish because both other terms have zero nth coefficient.

**Theorem 1.13 (The reduced generating series is the constant-one root).**

$$\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), \operatorname{mk}\left(a\right)\right) = S$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.reducedSeries_eq_artinSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficientwise mapping of the integer series mk(a) through the integer cast into ZMod(2) equals S. Both sides have constant and linear coefficients one and satisfy the mod-two source equation; triangular coefficient induction gives uniqueness. The intCast argument records the ring homomorphism from the integers into ZMod(2).

**Theorem 1.14 (Odd coefficients occur exactly at powers of two).**

$$\forall n: \mathbb{N}, (0 < n) \Rightarrow (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \Leftrightarrow (\exists r: \mathbb{N}, n = 2^{r}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.a396808_first_conjecture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OEIS A396808 states this as its first conjecture. For every positive natural index n, the integer a(n) is odd if and only if n=2^r for some natural exponent r. The reduction theorem identifies its parity with the exact support of the constant-one root.

## References

- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.a`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.a396808_first_conjecture`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.artinCoeff`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.artinSeries`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.artinSeries_square_add`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.coeff_artinSeries_pow_eq_zero`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.normalized_solution_unique`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.prefixPolynomial`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.prefixPolynomial_eq_sum`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.reducedSeries_eq_artinSeries`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.source_equation`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.tracePoly`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.tracePoly_identity`
- Truth anchor: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.tracePoly_natDegree_le`
