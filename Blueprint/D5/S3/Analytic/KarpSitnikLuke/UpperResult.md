# A counterexample to the sum-condition upper bound

## Abstract

An alternating lower bracket contradicts the sum-condition Luke upper bound.

**Definition 1.1 (The Gamma product).**

$$\forall q \in \mathbb {N},\; \forall a \in \operatorname {Fin}\left(q\right) \to \mathbb {R},\; \forall b \in \operatorname {Fin}\left(q\right) \to \mathbb {R},\; \forall sigma \in \mathbb {R},\; \operatorname {gammaProduct}\left(sigma, a, b\right) = \prod_{i: \operatorname {Fin}\left(q\right)} \frac{\operatorname {Real.Gamma}\left(a\left(i\right)\right) \cdot \operatorname {Real.Gamma}\left(b\left(i\right) - sigma\right)}{\operatorname {Real.Gamma}\left(b\left(i\right)\right) \cdot \operatorname {Real.Gamma}\left(a\left(i\right) - sigma\right)}$$

*Formalization.* `D5/S3/Analytic/KarpSitnikLuke/UpperResult.gammaProduct` (`✓ std3`).

*Citation.* D. Karp and S. M. Sitnik (2009). *Inequalities and monotonicity of ratios for generalized hypergeometric function*. DOI: [10.1016/j.jat.2008.10.002](https://doi.org/10.1016/j.jat.2008.10.002). URL: <https://arxiv.org/abs/math/0703084>.

*Commentary.*

Conjecture 2, printed page 14 of arXiv:math/0703084v2, equation (38), uses the product of Gamma(a_i)Gamma(b_i−sigma)/(Gamma(b_i)Gamma(a_i−sigma)). Gamma is Mathlib's real Gamma function, and the finite product has indices in Fin q.

**Definition 1.2 (The conjectured upper bound inside the disk).**

$$claim = \left(\forall q \in \mathbb {N},\; \forall a \in \operatorname {Fin}\left(q\right) \to \mathbb {R},\; \forall b \in \operatorname {Fin}\left(q\right) \to \mathbb {R},\; \forall sigma \in \mathbb {R},\; \forall x \in \mathbb {R},\; (\forall i \in \operatorname {Fin}\left(q\right),\; 0 < a\left(i\right)) \Rightarrow ((\forall i \in \operatorname {Fin}\left(q\right),\; 0 < b\left(i\right)) \Rightarrow ((0 < \sum_{i: \operatorname {Fin}\left(q\right)} (b\left(i\right) - a\left(i\right))) \Rightarrow ((0 < sigma) \Rightarrow ((\forall i \in \operatorname {Fin}\left(q\right),\; sigma \le a\left(i\right)) \Rightarrow ((0 < x) \Rightarrow ((x < 1) \Rightarrow ((\operatorname {Summable}\left(n: \mathbb {N}\mapsto \operatorname {hyperTerm}\left(sigma, a, b, -x, n\right)\right)) \Rightarrow ((0 < \operatorname {gammaProduct}\left(sigma, a, b\right)) \Rightarrow (\operatorname {hyper}\left(sigma, a, b, -x\right) < \frac{1}{(1 + x \cdot (\operatorname {gammaProduct}\left(sigma, a, b\right))^{\frac{1}{sigma}})^{sigma}})))))))))\right)$$

*Formalization.* `D5/S3/Analytic/KarpSitnikLuke/UpperResult.claim` (`✓ std3`).

*Citation.* D. Karp and S. M. Sitnik (2009). *Inequalities and monotonicity of ratios for generalized hypergeometric function*. DOI: [10.1016/j.jat.2008.10.002](https://doi.org/10.1016/j.jat.2008.10.002). URL: <https://arxiv.org/abs/math/0703084>.

*Commentary.*

Conjecture 2, printed page 14, in linear notation: “For 0 < σ ≤ min(a₁, a₂, . . . , a_q), ∑ᵢ₌₁ᵠ (bᵢ − aᵢ) > 0 and x > 0: _{q+1}F_q(σ, (a_q); (b_q); −x) < 1/[1 + x ∏ᵢ₌₁ᵠ Γ(aᵢ)Γ(bᵢ−σ)/(Γ(bᵢ)Γ(aᵢ−σ))]^σ. (38)”

The preceding sentence reads verbatim: “The asymptotic formula (16) and numerical experiments suggest the following”. Formula (16), printed page 5, with its preceding condition: “It follows that for σ < min(a₁, a₂, . . . , a_q) we will have”

Formula (16): “_{q+1}F_q(σ, (a_q); (b_q); −z) = Γ[(a_q)−σ, (b_q) / (a_q), (b_q)−σ] z^{−σ} + o(z^{−σ}), z → ∞.”

The extracted layout places a sigma next to the Gamma product. Separately, Gamma of parameter lists in (16) denotes the product quotient, so the asymptotic coefficient is the reciprocal of gammaProduct. The asymptotically precise reading is 1/(1+x K^(1/sigma))^sigma, with K=gammaProduct: the inner exponent 1/sigma makes its leading coefficient agree with (16). The counterexample has sigma=1, where this reading and the quoted display without that inner exponent coincide.

The existing Result.hyperTerm and Result.hyper encode equation (1): (sigma)n times the product of (a_i)n/(b_i)n, divided by n!, times z^n, and its real infinite sum. They use the existing TwoBlockResult.pochRatio and Mathlib's rising factorial, so the upper-bound assertion refers to the same function as the lower-bound assertion.

All a and b entries are positive, their denominator-minus-numerator sum is positive, and 0<sigma≤a_i for every i. Each additional hypothesis weakens the paper's universal assertion: x<1 restricts the domain to the power-series disk, summability restricts to convergent defining series, and gammaProduct>0 restricts the parameter set. With x>0 and gammaProduct>0 the base of the outer real power is positive. Refuting this weaker assertion refutes Conjecture 2. For q=0 the positive-sum assumption is impossible. Powers are Real.rpow.

**Definition 1.3 (Magnitudes of the witness terms).**

$$\forall n \in \mathbb {N},\; \operatorname {u}\left(n\right) = \operatorname {D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.pochRatio}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(2\right), 2\right), ![\frac{3}{2}, 3], n\right) \cdot (\frac{1}{2})^{n}$$

*Formalization.* `D5/S3/Analytic/KarpSitnikLuke/UpperResult.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a=(2,2) and b=(3/2,3), u(n)=(2)n²/((3/2)n(3)n) times (1/2)^n. These are the magnitudes at z=−1/2 and sigma=1. Natural indices in real expressions are coerced to real numbers.

**Theorem 1.4 (Nonnegative magnitudes).**

$$\forall n \in \mathbb {N},\; 0 \le \operatorname {u}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/UpperResult.u_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All rising factorials in the ratio are positive and the power is nonnegative.

**Theorem 1.5 (The exact successive-term ratio).**

$$\forall n \in \mathbb {N},\; \operatorname {u}\left(n + 1\right) = \frac{(n + 2)^{2}}{2 \cdot \left(n + \frac{3}{2}\right) \cdot \left(n + 3\right)} \cdot \operatorname {u}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/UpperResult.u_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rising-factorial recurrence gives the multiplier (n+2)²/(2(n+3/2)(n+3)).

**Theorem 1.6 (A uniform ratio bound).**

$$\forall n \in \mathbb {N},\; \operatorname {u}\left(n + 1\right) \le \frac{1}{2} \cdot \operatorname {u}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/UpperResult.u_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inequality (n+2)²≤(n+3/2)(n+3) holds for every natural n, since their difference is (n+1)/2. Thus the successive magnitudes decrease by at least a factor of one half.

**Theorem 1.7 (Summable magnitudes).**

$$\operatorname {Summable}\left(u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/UpperResult.u_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform ratio bound implies summability by geometric comparison.

**Theorem 1.8 (The exact alternating summands).**

$$\forall n \in \mathbb {N},\; \operatorname {hyperTerm}\left(1, \operatorname {Function.const}\left(\operatorname {Fin}\left(2\right), 2\right), ![\frac{3}{2}, 3], -\frac{1}{2}, n\right) = (-1)^{n} \cdot \operatorname {u}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/UpperResult.term_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity (1)n=n! cancels the factorial in hyperTerm at sigma=1. The remaining term is (−1)^n u(n).

**Theorem 1.9 (Convergence at the counterexample).**

$$\operatorname {Summable}\left(n: \mathbb {N}\mapsto \operatorname {hyperTerm}\left(1, \operatorname {Function.const}\left(\operatorname {Fin}\left(2\right), 2\right), ![\frac{3}{2}, 3], -\frac{1}{2}, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/UpperResult.witness_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summability of u and the exact summand identity prove convergence of the hypergeometric series at −1/2.

**Theorem 1.10 (The value exceeds two thirds).**

$$\frac{2}{3} < \operatorname {hyper}\left(1, \operatorname {Function.const}\left(\operatorname {Fin}\left(2\right), 2\right), ![\frac{3}{2}, 3], -\frac{1}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/UpperResult.witness_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six-term alternating lower bracket is 1−4/9+1/5−16/175+8/189−32/1617=249826/363825>2/3. The antitone alternating-series theorem compares this bracket with the real infinite sum.

**Theorem 1.11 (The Gamma product equals one).**

$$\operatorname {gammaProduct}\left(1, \operatorname {Function.const}\left(\operatorname {Fin}\left(2\right), 2\right), ![\frac{3}{2}, 3]\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/UpperResult.witness_gamma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gamma(2)=Gamma(1)=1, Gamma(3)=2 and Gamma(3/2)=(1/2)Gamma(1/2). Positivity of Gamma(1/2) permits cancellation. The two factors are 2 and 1/2, whose product is one.

**Theorem 1.12 (Refutation of the upper bound).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpSitnikLuke/UpperResult.result` (`✓ std3`). ∎

*Resolves.* `Problems/karp-sitnik-2009-luke-upper-bound` (refuted) by `D5/S3/Analytic/KarpSitnikLuke/UpperResult.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karp-sitnik-2009-luke-upper-bound","declaration_gid":"D5/S3/Analytic/KarpSitnikLuke/UpperResult.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Karp and S. M. Sitnik (2009). *Inequalities and monotonicity of ratios for generalized hypergeometric function*. DOI: [10.1016/j.jat.2008.10.002](https://doi.org/10.1016/j.jat.2008.10.002). URL: <https://arxiv.org/abs/math/0703084>.

*Commentary.*

Take q=2, sigma=1, a=(2,2), b=(3/2,3), x=1/2. All parameters are positive, the sum of b−a is 1/2, and sigma≤a_i. The defining series converges. The Gamma product is one and the proposed upper expression is 2/3, whereas the function exceeds 2/3. This refutes the sum-condition extension. It leaves the componentwise case b_k>a_k open.

## References

- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.claim`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.gammaProduct`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.result`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.term_eq`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.u`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.u_half`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.u_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.u_step`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.u_summable`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.witness_gamma`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.witness_lower`
- Truth anchor: `D5/S3/Analytic/KarpSitnikLuke/UpperResult.witness_summable`
- Dependency: [D5/S3/Analytic/KarpSitnikLuke/Result](Result.md)
