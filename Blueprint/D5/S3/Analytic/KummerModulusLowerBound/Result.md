# A quadratic Kummer counterexample

## Abstract

An exact nonreal zero contradicts the universal Kummer modulus lower bound.

**Definition 1.1 (The complex Kummer series).**

$$\forall a \in \mathbb {R},\; \forall b \in \mathbb {R},\; \forall z \in \mathbb {C},\; \operatorname {kummerC}\left(a, b, z\right) = \sum '_{n: \mathbb {N}} (\operatorname {D5.S3.Analytic.KummerRatio.Defs.kummerCoeff}\left(a, b, n\right): \mathbb {C}) \cdot (z)^{n}$$

*Formalization.* `D5/S3/Analytic/KummerModulusLowerBound/Result.kummerC` (`✓ std3`).

*Citation.* R. Garrappa, S. Gerhold, M. Popolizio and T. Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. DOI: [10.1016/j.jmaa.2025.129588](https://doi.org/10.1016/j.jmaa.2025.129588). URL: <https://arxiv.org/abs/2410.11852>.

*Commentary.*

Remark 2(a) identifies M as "a Kummer confluent hypergeometric function": M(a, b, z) = Σ_{n≥0} (a)_n z^n / ((b)_n n!), b ∉ {0, −1, −2, …}. The locator is Remark 2(a) of arXiv:2410.11852v4; the supplied extract does not specify a verified page number. The existing KummerRatio.Defs.kummerCoeff is (a)n/((b)n n!), where (a)n is (ascPochhammer R n).eval a. The complex summands cast these same real coefficients into C. No normalization changes.

**Definition 1.2 (The universal modulus assertion).**

$$claim = \left(\forall alpha \in \mathbb {R},\; \forall beta \in \mathbb {R},\; (0 < alpha) \Rightarrow ((0 < beta) \Rightarrow ((\forall n \in \mathbb {N},\; alpha - beta \ne -(n: \mathbb {R})) \Rightarrow (\forall z \in \mathbb {C},\; \operatorname {D5.S3.Analytic.KummerRatio.Defs.kummer}\left(alpha, alpha - beta, \operatorname {Complex.re}\left(z\right)\right) \le \operatorname {norm}\left(\operatorname {kummerC}\left(alpha, alpha - beta, z\right)\right))))\right)$$

*Formalization.* `D5/S3/Analytic/KummerModulusLowerBound/Result.claim` (`✓ std3`).

*Citation.* R. Garrappa, S. Gerhold, M. Popolizio and T. Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. DOI: [10.1016/j.jmaa.2025.129588](https://doi.org/10.1016/j.jmaa.2025.129588). URL: <https://arxiv.org/abs/2410.11852>.

*Commentary.*

Remark 6 of arXiv:2410.11852v4: “In view of the preceding result and Remark 2, one may ask if for all α, β > 0 one has |M(α, α−β, z)| ≥ M(α, α−β, ℜz), z ∈ ℂ. (2.4) … In particular, (2.4) holds globally for α > 1 ≥ β > 0 … The question whether (2.4) holds globally for all α, β > 0 seems to be still open.” The supplied locator specifies the remark, without a verified page number. Alpha and beta are real and positive; alpha−beta is not a nonpositive integer. The real side is exactly KummerRatio.Defs.kummer alpha (alpha−beta) z.re, and the complex norm is the ordinary complex modulus. The pole exclusion is already part of the definition of M in Remark 2(a).

**Theorem 1.3 (The second parameter avoids poles).**

$$\forall n \in \mathbb {N},\; \frac{-3}{2} \ne -(n: \mathbb {R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerModulusLowerBound/Result.half_ne_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number 3/2 lies strictly between the natural numbers 1 and 2. Thus −3/2 is never a nonpositive integer; result uses this for alpha=1/2 and beta=2.

**Theorem 1.4 (The exact polynomial coefficient).**

$$\forall n \in \mathbb {N},\; \operatorname {D5.S3.Analytic.KummerRatio.Defs.kummerCoeff}\left(\frac{1}{2}, \frac{-3}{2}, n\right) = \frac{1 - \frac{4}{3} \cdot (n: \mathbb {R}) + \frac{4}{3} \cdot (n: \mathbb {R}) \cdot \left((n: \mathbb {R}) - 1\right)}{\operatorname {Nat.factorial}\left(n\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerModulusLowerBound/Result.coeff_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write P_n(x)=(x)_n. Evaluate Mathlib ascPochhammer_mul at −3/2 with lengths (n, 2) and (2, n). The common value P_{n+2}(−3/2) gives P_n(−3/2)(n−3/2)(n−1/2)=(3/4)P_n(1/2). Rational normalization gives (1/2)n=(1−4n/3+4n(n−1)/3)(−3/2)n. The denominator is nonzero because its only possible roots are nonpositive integers. Dividing by the factorial gives the coefficient used by complex_closed.

**Theorem 1.5 (The second factorial moment of the exponential series).**

$$\forall z \in \mathbb {C},\; \operatorname {HasSum}\left(n: \mathbb {N}\mapsto \frac{(n: \mathbb {C}) \cdot \left((n: \mathbb {C}) - 1\right) \cdot (z)^{n}}{\operatorname {Nat.factorial}\left(n\right)}, (z)^{2} \cdot \operatorname {Complex.exp}\left(z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerModulusLowerBound/Result.second_exp_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A shift by one reduces the second factorial moment to ResolvedCountWeakValue.weighted_exp_hasSum, the first weighted exponential series. This supplies the quadratic term in complex_closed.

**Theorem 1.6 (The complex closed form).**

$$\forall z \in \mathbb {C},\; \operatorname {kummerC}\left(\frac{1}{2}, \frac{-3}{2}, z\right) = \operatorname {Complex.exp}\left(z\right) \cdot \left(1 - \frac{4 \cdot z}{3} + \frac{4 \cdot (z)^{2}}{3}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerModulusLowerBound/Result.complex_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combine the exponential series, its first factorial moment and its second factorial moment with coefficients 1, −4/3 and 4/3. The exact coefficient identity identifies their sum with the complex Kummer series. The identity is used both at the nonreal zero and at real arguments.

**Theorem 1.7 (The real closed form).**

$$\forall x \in \mathbb {R},\; \operatorname {D5.S3.Analytic.KummerRatio.Defs.kummer}\left(\frac{1}{2}, \frac{-3}{2}, x\right) = \operatorname {Real.exp}\left(x\right) \cdot \left(1 - \frac{4 \cdot x}{3} + \frac{4 \cdot (x)^{2}}{3}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerModulusLowerBound/Result.real_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real embedding commutes with the infinite sum, powers and exponential. Applying injectivity of that embedding to complex_closed yields the real identity; witness_pos uses it at x=1/2.

**Theorem 1.8 (An exact nonreal zero).**

$$\operatorname {kummerC}\left(\frac{1}{2}, \frac{-3}{2}, (\frac{1}{2}: \mathbb {C}) + (\frac{\operatorname {Real.sqrt}\left(2\right)}{2}: \mathbb {C}) \cdot \operatorname {Complex.I}\left(\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerModulusLowerBound/Result.witness_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At z=1/2+(sqrt 2/2)i, the quadratic 1−4z/3+4z²/3 vanishes exactly, since (sqrt 2)²=2. Therefore the complex series has norm zero.

**Theorem 1.9 (The positive real-axis value).**

$$0 < \operatorname {D5.S3.Analytic.KummerRatio.Defs.kummer}\left(\frac{1}{2}, \frac{-3}{2}, \frac{1}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerModulusLowerBound/Result.witness_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At x=1/2, the quadratic is 2/3. Hence the real series is (2/3)exp(1/2)>0, contradicting the proposed bound at the complex zero.

**Theorem 1.10 (A negative answer to the universal question).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerModulusLowerBound/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/garrappa-gerhold-popolizio-simon-2025-kummer-modulus` (refuted) by `D5/S3/Analytic/KummerModulusLowerBound/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"garrappa-gerhold-popolizio-simon-2025-kummer-modulus","declaration_gid":"D5/S3/Analytic/KummerModulusLowerBound/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Garrappa, S. Gerhold, M. Popolizio and T. Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. DOI: [10.1016/j.jmaa.2025.129588](https://doi.org/10.1016/j.jmaa.2025.129588). URL: <https://arxiv.org/abs/2410.11852>.

*Commentary.*

Take alpha=1/2, beta=2 and z=1/2+(sqrt 2/2)i. Both parameters are positive, and alpha−beta=−3/2 avoids every excluded pole. The real-axis value is strictly positive, while the complex norm is zero. Thus the universal assertion in Remark 6 is false. The paper's range alpha>1≥beta>0 is not contradicted. A classification of all parameter pairs satisfying the modulus inequality remains outside this conclusion.

## References

- Truth anchor: `D5/S3/Analytic/KummerModulusLowerBound/Result.claim`
- Truth anchor: `D5/S3/Analytic/KummerModulusLowerBound/Result.coeff_eq`
- Truth anchor: `D5/S3/Analytic/KummerModulusLowerBound/Result.complex_closed`
- Truth anchor: `D5/S3/Analytic/KummerModulusLowerBound/Result.half_ne_nat`
- Truth anchor: `D5/S3/Analytic/KummerModulusLowerBound/Result.kummerC`
- Truth anchor: `D5/S3/Analytic/KummerModulusLowerBound/Result.real_closed`
- Truth anchor: `D5/S3/Analytic/KummerModulusLowerBound/Result.result`
- Truth anchor: `D5/S3/Analytic/KummerModulusLowerBound/Result.second_exp_hasSum`
- Truth anchor: `D5/S3/Analytic/KummerModulusLowerBound/Result.witness_pos`
- Truth anchor: `D5/S3/Analytic/KummerModulusLowerBound/Result.witness_zero`
- Dependency: [D5/S3/Analytic/KummerRatio/Defs](../KummerRatio/Defs.md)
- Dependency: [D5/S3/Quantum/ResolvedCountWeakValue](../../Quantum/ResolvedCountWeakValue.md)
