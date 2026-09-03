# Golden Germ Third Normalized Factor Majorant

## Abstract

The third normalized golden germ factors admit a summable uniform prime majorant and a locally uniformly convergent product.

**Theorem 1.1 (The third normalized factors satisfy a locally uniform M-test).**

$$\begin{aligned}\forall sigma\in \mathbb{R}, \frac{1}{\varphi^{5}} < sigma \Rightarrow\\\forall s\in \mathbb{C}, \forall p\in \operatorname{Primes}(\mathbb{N}), \operatorname{x}(s, p) := p^{-s \times \varphi^{2}}, \forall s\in \mathbb{C}, \forall p\in \operatorname{Primes}(\mathbb{N}), \operatorname{y}(s, p) := p^{-s \times \varphi^{3}},\\\forall s\in \mathbb{C}, \forall p\in \operatorname{Primes}(\mathbb{N}), \operatorname{Kp}(s, p) := (1 - \operatorname{y}(s, p)^{2})^{-1} \times (1 - \operatorname{x}(s, p)^{2} \times \operatorname{y}(s, p)) \times (1 - \operatorname{y}(s, p)) \times (1 + \operatorname{x}(s, p))^{-1} \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)},\\\operatorname{f}(p, s) := \operatorname{Kp}(s, p) - 1, \operatorname{G3}(s) := \prod_{p\in \operatorname{Primes}(\mathbb{N})}\operatorname{Kp}(s, p),\\(\exists u: \operatorname{Primes}(\mathbb{N}) \to \mathbb{R}, \operatorname{Summable}(u) \land \forall p\in \operatorname{Primes}(\mathbb{N}), \forall s\in \mathbb{C}, sigma \leq \Re(s) \Rightarrow \left\lVert \operatorname{f}(p, s) \right\rVert \leq \operatorname{u}(p)) \land\\(\forall p\in \operatorname{Primes}(\mathbb{N}), \operatorname{DifferentiableOn}(\mathbb{C}, \operatorname{f}(p), \{s\in \mathbb{C} \mid sigma < \Re(s)\})) \land\\\operatorname{HasProdLocallyUniformlyOn}((p, s) \mapsto 1 + \operatorname{f}(p, s), G3, \{s\in \mathbb{C} \mid sigma < \Re(s)\}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorMajorant.golden_germ_third_normalized_factor_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real sigma strictly above one over phi to the fifth, the six retained modes and the remaining local tail are bounded by one prime-summable real family uniformly on the closed half-plane with real part at least sigma.

The same estimates keep both inverse factors away from zero. Consequently every deviation is differentiable on the open half-plane and the finite prime products converge there locally uniformly to the canonical infinite product.

This theorem supplies convergence and regularity infrastructure. It asserts no product nonvanishing, no boundary convergence, no all-order extraction, O-5, or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorMajorant.golden_germ_third_normalized_factor_majorant`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization](../EulerGerm/GoldenGermThirdOrderFactorization.md)
- Dependency: [D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor](../EulerGerm/LocalFactorZeroDivisor.md)
