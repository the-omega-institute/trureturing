# A counterexample to the sum-condition lower bound

## Abstract

A convergent hypergeometric series contradicts the sum-condition Luke lower bound.

**Definition 1.1 (The generalized hypergeometric summand).**

$$\forall q \in \mathbb {N},\; \forall a \in \operatorname {Fin}\left(q\right) \to \mathbb {R},\; \forall b \in \operatorname {Fin}\left(q\right) \to \mathbb {R},\; \forall sigma \in \mathbb {R},\; \forall z \in \mathbb {R},\; \forall n \in \mathbb {N},\; \operatorname {hyperTerm}\left(sigma, a, b, z, n\right) = \frac{\operatorname {Polynomial.eval}\left(sigma, \operatorname {ascPochhammer}\left(\mathbb {R}, n\right)\right) \cdot \operatorname {D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.pochRatio}\left(a, b, n\right)}{\operatorname {Nat.factorial}\left(n\right)} \cdot (z)^{n}$$

*Formalization.* `D5/S3/Analytic/KarpSitnikLuke/Result.hyperTerm` (`✓ std3`).

*Citation.* D. Karp and S. M. Sitnik (2009). *Inequalities and monotonicity of ratios for generalized hypergeometric function*. DOI: [10.1016/j.jat.2008.10.002](https://doi.org/10.1016/j.jat.2008.10.002). URL: <https://arxiv.org/abs/math/0703084>.

*Commentary.*

Equation (1), printed page 1 of arXiv:math/0703084v2, defines the generalized hypergeometric series by the product of upper rising factorials divided by the product of lower rising factorials and n!, multiplied by z^n. The upper list here is sigma followed by a, and the lower list is b. The existing pochRatio is precisely the quotient of the products for a and b. Mathlib's (ascPochhammer R n).eval t equals the source's (t)n=t(t+1)...(t+n−1), with value one at n=0. Thus hyperTerm is the source's summand, with no Gamma normalization factor.

**Definition 1.2 (The power-series value).**

$$\forall q \in \mathbb {N},\; \forall a \in \operatorname {Fin}\left(q\right) \to \mathbb {R},\; \forall b \in \operatorname {Fin}\left(q\right) \to \mathbb {R},\; \forall sigma \in \mathbb {R},\; \forall z \in \mathbb {R},\; \operatorname {hyper}\left(sigma, a, b, z\right) = \sum '_{n: \mathbb {N}} \operatorname {hyperTerm}\left(sigma, a, b, z, n\right)$$

*Formalization.* `D5/S3/Analytic/KarpSitnikLuke/Result.hyper` (`✓ std3`).

*Citation.* D. Karp and S. M. Sitnik (2009). *Inequalities and monotonicity of ratios for generalized hypergeometric function*. DOI: [10.1016/j.jat.2008.10.002](https://doi.org/10.1016/j.jat.2008.10.002). URL: <https://arxiv.org/abs/math/0703084>.

*Commentary.*

The real tsum interprets equation (1) inside its convergence disk. Printed page 1 states: “The series converges for |z| < 1 and can be analytically continued onto the entire complex plane cut along [1, ∞].” Summability is an explicit assumption of the assertion below, and is proved for the counterexample.

**Definition 1.3 (The sum-condition assertion inside the disk).**

$$claim = \left(\forall q \in \mathbb {N},\; \forall a \in \operatorname {Fin}\left(q\right) \to \mathbb {R},\; \forall b \in \operatorname {Fin}\left(q\right) \to \mathbb {R},\; \forall sigma \in \mathbb {R},\; \forall x \in \mathbb {R},\; (\forall i \in \operatorname {Fin}\left(q\right),\; 0 < a\left(i\right)) \Rightarrow ((\forall i \in \operatorname {Fin}\left(q\right),\; 0 < b\left(i\right)) \Rightarrow ((0 < \sum_{i: \operatorname {Fin}\left(q\right)} (b\left(i\right) - a\left(i\right))) \Rightarrow ((0 < sigma) \Rightarrow ((-1 < x) \Rightarrow ((x < 1) \Rightarrow ((0 < 1 + x \cdot (\prod_{i: \operatorname {Fin}\left(q\right)} \frac{a\left(i\right)}{b\left(i\right)})) \Rightarrow ((\operatorname {Summable}\left(n: \mathbb {N}\mapsto \operatorname {hyperTerm}\left(sigma, a, b, -x, n\right)\right)) \Rightarrow (\frac{1}{(1 + x \cdot (\prod_{i: \operatorname {Fin}\left(q\right)} \frac{a\left(i\right)}{b\left(i\right)}))^{sigma}} < \operatorname {hyper}\left(sigma, a, b, -x\right)))))))))\right)$$

*Formalization.* `D5/S3/Analytic/KarpSitnikLuke/Result.claim` (`✓ std3`).

*Citation.* D. Karp and S. M. Sitnik (2009). *Inequalities and monotonicity of ratios for generalized hypergeometric function*. DOI: [10.1016/j.jat.2008.10.002](https://doi.org/10.1016/j.jat.2008.10.002). URL: <https://arxiv.org/abs/math/0703084>.

*Commentary.*

Theorem 3, printed page 6, equation (23), with the displayed formula joined to its sentence: “For bₖ > aₖ > 0, k = 1, . . . , q, x > −1 and σ ≥ 1 the inequality 1/(1 + x ∏ᵢ₌₁ᵠ (aᵢ/bᵢ))^σ < _{q+1}F_q(σ, (a_q); (b_q); −x) holds true.”

Conjecture 1, printed page 14: “Theorem 3 is true for all σ > 0 and ∑ᵢ₌₁ᵠ (bᵢ − aᵢ) > 0.”

All a and b entries are positive; the conjecture replaces the componentwise inequalities by positivity of the sum of b−a. The assertion is restricted to −1<x<1, the power-series disk at z=−x, and assumes summability and a positive real-power base. These restrictions give a weaker assertion than the paper's x>−1 assertion via analytic continuation. Refuting this weaker assertion therefore refutes the paper's Conjecture 1. For q=0 the positive-sum assumption is impossible; including it adds no cases. Real powers use Real.rpow.

**Definition 1.4 (Positive magnitudes of the witness summands).**

$$\forall n \in \mathbb {N},\; \operatorname {u}\left(n\right) = \frac{\operatorname {Nat.factorial}\left(n\right)}{\operatorname {Polynomial.eval}\left(\frac{1}{10}, \operatorname {ascPochhammer}\left(\mathbb {R}, n\right)\right) \cdot \left(n + 1\right)} \cdot (\frac{1}{10})^{n}$$

*Formalization.* `D5/S3/Analytic/KarpSitnikLuke/Result.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The magnitudes are n!/((1/10)n(n+1)) times (1/10)^n. Natural indices in real expressions are coerced to real numbers.

**Theorem 1.5 (Nonnegative magnitudes).**

$$\forall n \in \mathbb {N},\; 0 \le \operatorname {u}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/Result.u_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rising factorial at 1/10 and the factorial are positive, and the power is nonnegative.

**Theorem 1.6 (The exact successive-term ratio).**

$$\forall n \in \mathbb {N},\; \operatorname {u}\left(n + 1\right) = \frac{(n + 1)^{2}}{10 \cdot \left(n + \frac{1}{10}\right) \cdot \left(n + 2\right)} \cdot \operatorname {u}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/Result.u_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorial and rising-factorial recurrences give u(n+1)/u(n)=(n+1)^2/(10(n+1/10)(n+2)).

**Theorem 1.7 (A uniform geometric comparison).**

$$\forall n \in \mathbb {N},\; \operatorname {u}\left(n + 1\right) \le \frac{1}{2} \cdot \operatorname {u}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/Result.u_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n the ratio is at most one half: the denominator comparison reduces to 4n^2+(17/2)n≥0. In particular the magnitudes decrease from the first term onward.

**Theorem 1.8 (Absolute convergence of the magnitudes).**

$$\operatorname {Summable}\left(u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/Result.u_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ratio bound one half implies summability by the geometric comparison test.

**Theorem 1.9 (The exact witness summands).**

$$\forall n \in \mathbb {N},\; \operatorname {hyperTerm}\left(1, \operatorname {Function.const}\left(\operatorname {Fin}\left(2\right), 1\right), ![\frac{1}{10}, 2], -\frac{1}{10}, n\right) = (-1)^{n} \cdot \operatorname {u}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/Result.term_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At q=2, sigma=1, a=(1,1), b=(1/10,2) and z=−1/10, the identities (1)n=n! and (2)n=(n+1)! cancel the factorial weights. The resulting term is (−1)^n u(n).

**Theorem 1.10 (Convergence at the counterexample).**

$$\operatorname {Summable}\left(n: \mathbb {N}\mapsto \operatorname {hyperTerm}\left(1, \operatorname {Function.const}\left(\operatorname {Fin}\left(2\right), 1\right), ![\frac{1}{10}, 2], -\frac{1}{10}, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/Result.witness_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact summand identity and summability of the magnitudes imply convergence of the alternating hypergeometric series.

**Theorem 1.11 (The hypergeometric value is below two thirds).**

$$\operatorname {hyper}\left(1, \operatorname {Function.const}\left(\operatorname {Fin}\left(2\right), 1\right), ![\frac{1}{10}, 2], -\frac{1}{10}\right) < \frac{2}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/Result.witness_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The antitone alternating-series upper bound uses indices zero, one and two: 1−1/2+2/33=37/66<2/3. Summability identifies the limit with the real tsum.

**Theorem 1.12 (Refutation of the conjectured extension).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/karp-sitnik-2009-luke-lower-bound` (refuted) by `D5/S3/Analytic/KarpSitnikLuke/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karp-sitnik-2009-luke-lower-bound","declaration_gid":"D5/S3/Analytic/KarpSitnikLuke/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Karp and S. M. Sitnik (2009). *Inequalities and monotonicity of ratios for generalized hypergeometric function*. DOI: [10.1016/j.jat.2008.10.002](https://doi.org/10.1016/j.jat.2008.10.002). URL: <https://arxiv.org/abs/math/0703084>.

*Commentary.*

Take q=2, sigma=1, a=(1,1), b=(1/10,2), x=1/10. The parameters are positive, the sum of b−a is 1/10, and the product of a/b is 5. The real-power base is 3/2, so the proposed lower bound is 2/3. The convergent series value is at most 37/66, contradicting the strict lower-bound assertion. This counterexample uses sigma=1 and violates the componentwise condition b1>a1. It does not contradict Theorem 3 under that theorem's original hypotheses, and does not address the componentwise case 0<sigma<1 or Conjecture 2.

## References

- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.claim`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.hyper`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.hyperTerm`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.result`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.term_eq`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.u`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.u_half`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.u_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.u_step`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.u_summable`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.witness_summable`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/Result.witness_upper`
- Dependency: [D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult](../HypergeometricShiftTuran/TwoBlockResult.md)
