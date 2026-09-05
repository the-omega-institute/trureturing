# Golden Germ Third-Order Window Zero Criterion

## Abstract

The frozen third-order golden residual vanishes exactly at a local-factor zero, and RH classifies the continued germ's zeros in the open golden window.

**Theorem 1.1 (RH puts every residual-surviving window zero on the pulled-back line).**

$$\begin{aligned}\forall s\in \mathbb{C}, p\in \operatorname{Primes}\left(\mathbb{N}\right),\\\operatorname{x}\left(s, p\right) := p^{-s \times \varphi^{2}}, \operatorname{y}\left(s, p\right) := p^{-s \times \varphi^{3}}, \operatorname{Kp}\left(s, p\right) := (1 - \operatorname{y}\left(s, p\right)^{2})^{-1} \times (1 - \operatorname{x}\left(s, p\right)^{2} \times \operatorname{y}\left(s, p\right)) \times (1 - \operatorname{y}\left(s, p\right)) \times (1 + \operatorname{x}\left(s, p\right))^{-1} \times \operatorname{germLocalFactor}\left(s, p\right),\\\forall s\in \mathbb{C}, \operatorname{G3}\left(s\right) := \prod_{p\in \operatorname{Primes}\left(\mathbb{N}\right)}\operatorname{Kp}\left(s, p\right),\\RiemannHypothesis \Rightarrow \left(\forall continuedGerm \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\} \to \mathbb{C},\; \left(\left(\forall s \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\},\; \frac{1}{\varphi^{2}} < \Re{s} \Rightarrow continuedGerm\left(s\right) = \prod_{p\in \operatorname{Primes}\left(\mathbb{N}\right)}\operatorname{germLocalFactor}\left(s, p\right)\right) \land \left(\forall s \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\},\; continuedGerm\left(s\right) = \operatorname{riemannZeta}\left(\varphi^{2} \cdot s\right) \cdot \operatorname{riemannZeta}\left(\varphi^{3} \cdot s\right) \cdot \operatorname{riemannZeta}\left(2 \cdot \varphi^{2} \cdot s\right)^{-1} \cdot \operatorname{riemannZeta}\left(2 \cdot \varphi^{3} \cdot s\right)^{-1} \cdot \operatorname{riemannZeta}\left(\left(2 \cdot \varphi^{2} + \varphi^{3}\right) \cdot s\right) \cdot \operatorname{G3}\left(s\right)\right)\right) \Rightarrow \left(\forall s \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\},\; \frac{1}{2 \cdot \varphi^{3}} < \Re{s} \Rightarrow \left(\Re{s} < \frac{1}{\varphi^{2}} \Rightarrow \left(continuedGerm\left(s\right) = 0 \Rightarrow \left(\operatorname{G3}\left(s\right) \ne 0 \Rightarrow \Re{s} = \frac{1}{2 \cdot \varphi^{2}}\right)\right)\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GoldenGermThirdOrderWindowZeroCriterion.golden_continued_germ_window_zero_on_line_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed Kp is the frozen normalized third-order local factor and G3 is its prime product. Under RH, a zero of the continued germ in the open window has real part one over twice phi squared whenever G3 survives there.

The agreement and five-zeta factorization premises are the two clauses of the frozen third-order continuation theorem. This is a conditional zero-confinement result, not a proof of RH.

**Theorem 1.2 (Third-order residual zeros are exactly local-factor zeros).**

$$\begin{aligned}\forall s\in \mathbb{C}, p\in \operatorname{Primes}\left(\mathbb{N}\right),\\\operatorname{x}\left(s, p\right) := p^{-s \times \varphi^{2}}, \operatorname{y}\left(s, p\right) := p^{-s \times \varphi^{3}}, \operatorname{Kp}\left(s, p\right) := (1 - \operatorname{y}\left(s, p\right)^{2})^{-1} \times (1 - \operatorname{x}\left(s, p\right)^{2} \times \operatorname{y}\left(s, p\right)) \times (1 - \operatorname{y}\left(s, p\right)) \times (1 + \operatorname{x}\left(s, p\right))^{-1} \times \operatorname{germLocalFactor}\left(s, p\right),\\\forall s\in \mathbb{C}, \operatorname{G3}\left(s\right) := \prod_{p\in \operatorname{Primes}\left(\mathbb{N}\right)}\operatorname{Kp}\left(s, p\right),\\\forall s \in \mathbb{C},\; \frac{1}{\varphi^{5}} < \Re{s} \Rightarrow \left(\operatorname{G3}\left(s\right) = 0 \Leftrightarrow \left(\exists p \in \operatorname{Primes}\left(\mathbb{N}\right),\; \operatorname{germLocalFactor}\left(s, p\right) = 0\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GoldenGermThirdOrderWindowZeroCriterion.golden_third_residual_eq_zero_iff_exists_local_factor_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above the phi-fifth boundary, the norm-summable deviation of Kp from one makes the infinite product nonzero whenever every canonical local factor is nonzero. Conversely, one zero factor forces the product G3 to vanish.

Thus G3's zero set in this half-plane is exactly the union of the local-factor zero sets. The equivalence does not itself assert the existence of such a zero.

**Theorem 1.3 (RH identifies the continued germ's complete open-window zero set).**

$$\begin{aligned}\forall s\in \mathbb{C}, p\in \operatorname{Primes}\left(\mathbb{N}\right),\\\operatorname{x}\left(s, p\right) := p^{-s \times \varphi^{2}}, \operatorname{y}\left(s, p\right) := p^{-s \times \varphi^{3}}, \operatorname{Kp}\left(s, p\right) := (1 - \operatorname{y}\left(s, p\right)^{2})^{-1} \times (1 - \operatorname{x}\left(s, p\right)^{2} \times \operatorname{y}\left(s, p\right)) \times (1 - \operatorname{y}\left(s, p\right)) \times (1 + \operatorname{x}\left(s, p\right))^{-1} \times \operatorname{germLocalFactor}\left(s, p\right),\\\forall s\in \mathbb{C}, \operatorname{G3}\left(s\right) := \prod_{p\in \operatorname{Primes}\left(\mathbb{N}\right)}\operatorname{Kp}\left(s, p\right),\\RiemannHypothesis \Rightarrow \left(\forall continuedGerm \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\} \to \mathbb{C},\; \left(\forall s \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\},\; continuedGerm\left(s\right) = \operatorname{riemannZeta}\left(\varphi^{2} \cdot s\right) \cdot \operatorname{riemannZeta}\left(\varphi^{3} \cdot s\right) \cdot \operatorname{riemannZeta}\left(2 \cdot \varphi^{2} \cdot s\right)^{-1} \cdot \operatorname{riemannZeta}\left(2 \cdot \varphi^{3} \cdot s\right)^{-1} \cdot \operatorname{riemannZeta}\left(\left(2 \cdot \varphi^{2} + \varphi^{3}\right) \cdot s\right) \cdot \operatorname{G3}\left(s\right)\right) \Rightarrow \left(\forall s \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\},\; \frac{1}{2 \cdot \varphi^{3}} < \Re{s} \Rightarrow \left(\Re{s} < \frac{1}{\varphi^{2}} \Rightarrow \left(continuedGerm\left(s\right) = 0 \Leftrightarrow \left(\left(\operatorname{riemannZeta}\left(\varphi^{2} \cdot s\right) = 0 \land \Re{s} = \frac{1}{2 \cdot \varphi^{2}}\right) \lor \left(\exists p \in \operatorname{Primes}\left(\mathbb{N}\right),\; \operatorname{germLocalFactor}\left(s, p\right) = 0\right)\right)\right)\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GoldenGermThirdOrderWindowZeroCriterion.golden_continued_germ_window_zero_iff_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH, a continued germ satisfying the frozen third-order formula vanishes in the open window exactly when either the phi-squared zeta pullback vanishes on its pulled-back critical line or some canonical local factor vanishes.

This classification is not an RH proof path. The numerical local-factor zeros for p = 2 and p = 3 make the naive claim that window zeros lie on the line if and only if RH false.

## References

- Truth anchor: `D5/S3/Analytic/GermWindow/GoldenGermThirdOrderWindowZeroCriterion.golden_continued_germ_window_zero_iff_of_rh`
- Truth anchor: `D5/S3/Analytic/GermWindow/GoldenGermThirdOrderWindowZeroCriterion.golden_continued_germ_window_zero_on_line_of_rh`
- Truth anchor: `D5/S3/Analytic/GermWindow/GoldenGermThirdOrderWindowZeroCriterion.golden_third_residual_eq_zero_iff_exists_local_factor_zero`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization](../EulerGerm/GoldenGermThirdOrderFactorization.md)
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermWindowZeroCriterion](../EulerGerm/GoldenGermWindowZeroCriterion.md)
