# Golden Germ Window Line Dichotomy

## Abstract

Under RH, the continued third-order golden germ has a sharp on-line and off-line zero dichotomy inside the open golden window.

**Theorem 1.1 (On-line germ zeros come from the zeta pullback or p = 2, 3).**

$$\begin{aligned}\forall s\in \mathbb{C}, p\in \operatorname{Primes}\left(\mathbb{N}\right),\\\operatorname{x}\left(s, p\right) := p^{-s \times \varphi^{2}}, \operatorname{y}\left(s, p\right) := p^{-s \times \varphi^{3}}, \operatorname{Kp}\left(s, p\right) := (1 - \operatorname{y}\left(s, p\right)^{2})^{-1} \times (1 - \operatorname{x}\left(s, p\right)^{2} \times \operatorname{y}\left(s, p\right)) \times (1 - \operatorname{y}\left(s, p\right)) \times (1 + \operatorname{x}\left(s, p\right))^{-1} \times \operatorname{germLocalFactor}\left(s, p\right),\\\forall s\in \mathbb{C}, \operatorname{G3}\left(s\right) := \prod_{p\in \operatorname{Primes}\left(\mathbb{N}\right)}\operatorname{Kp}\left(s, p\right),\\RiemannHypothesis \Rightarrow \left(\forall continuedGerm \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\} \to \mathbb{C},\; \left(\forall s \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\},\; continuedGerm\left(s\right) = \operatorname{riemannZeta}\left(\varphi^{2} \cdot s\right) \cdot \operatorname{riemannZeta}\left(\varphi^{3} \cdot s\right) \cdot \operatorname{riemannZeta}\left(2 \cdot \varphi^{2} \cdot s\right)^{-1} \cdot \operatorname{riemannZeta}\left(2 \cdot \varphi^{3} \cdot s\right)^{-1} \cdot \operatorname{riemannZeta}\left(\left(2 \cdot \varphi^{2} + \varphi^{3}\right) \cdot s\right) \cdot \operatorname{G3}\left(s\right)\right) \Rightarrow \left(\forall s \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\},\; \Re{s} = \frac{1}{2 \cdot \varphi^{2}} \Rightarrow \left(continuedGerm\left(s\right) = 0 \Leftrightarrow \left(\operatorname{riemannZeta}\left(\varphi^{2} \cdot s\right) = 0 \lor \left(\operatorname{germLocalFactor}\left(s, 2\right) = 0 \lor \operatorname{germLocalFactor}\left(s, 3\right) = 0\right)\right)\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GoldenGermWindowLineDichotomy.golden_continued_germ_line_zero_iff_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the pulled-back critical line, the frozen open-window classification and the critical-line nonvanishing theorem exclude every local factor at primes at least five. The remaining alternatives are the phi-squared zeta pullback and the local factors at p = 2 or p = 3.

Whether either small-prime local factor actually vanishes is a numerical question: this theorem neither asserts nor excludes such zeros. The result assumes RH and is not an RH proof path.

**Theorem 1.2 (Off-line window zeros are exactly local-factor zeros).**

$$\begin{aligned}\forall s\in \mathbb{C}, p\in \operatorname{Primes}\left(\mathbb{N}\right),\\\operatorname{x}\left(s, p\right) := p^{-s \times \varphi^{2}}, \operatorname{y}\left(s, p\right) := p^{-s \times \varphi^{3}}, \operatorname{Kp}\left(s, p\right) := (1 - \operatorname{y}\left(s, p\right)^{2})^{-1} \times (1 - \operatorname{x}\left(s, p\right)^{2} \times \operatorname{y}\left(s, p\right)) \times (1 - \operatorname{y}\left(s, p\right)) \times (1 + \operatorname{x}\left(s, p\right))^{-1} \times \operatorname{germLocalFactor}\left(s, p\right),\\\forall s\in \mathbb{C}, \operatorname{G3}\left(s\right) := \prod_{p\in \operatorname{Primes}\left(\mathbb{N}\right)}\operatorname{Kp}\left(s, p\right),\\RiemannHypothesis \Rightarrow \left(\forall continuedGerm \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\} \to \mathbb{C},\; \left(\forall s \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\},\; continuedGerm\left(s\right) = \operatorname{riemannZeta}\left(\varphi^{2} \cdot s\right) \cdot \operatorname{riemannZeta}\left(\varphi^{3} \cdot s\right) \cdot \operatorname{riemannZeta}\left(2 \cdot \varphi^{2} \cdot s\right)^{-1} \cdot \operatorname{riemannZeta}\left(2 \cdot \varphi^{3} \cdot s\right)^{-1} \cdot \operatorname{riemannZeta}\left(\left(2 \cdot \varphi^{2} + \varphi^{3}\right) \cdot s\right) \cdot \operatorname{G3}\left(s\right)\right) \Rightarrow \left(\forall s \in \left\{\frac{1}{\varphi^{5}} < \Re{s} \mid s \in \mathbb{C}\right\},\; \frac{1}{2 \cdot \varphi^{3}} < \Re{s} \Rightarrow \left(\Re{s} < \frac{1}{\varphi^{2}} \Rightarrow \left(\Re{s} \ne \frac{1}{2 \cdot \varphi^{2}} \Rightarrow \left(continuedGerm\left(s\right) = 0 \Leftrightarrow \left(\exists p \in \operatorname{Primes}\left(\mathbb{N}\right),\; \operatorname{germLocalFactor}\left(s, p\right) = 0\right)\right)\right)\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GoldenGermWindowLineDichotomy.golden_continued_germ_off_line_zero_iff_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Away from the pulled-back critical line, the zeta-zero branch of the frozen window criterion is impossible. Thus a continued germ zero in the open window is exactly a zero of some canonical golden local factor.

This is a conditional consequence of RH and the frozen third-order factorization. It supplies no converse and is not a route to proving RH.

## References

- Truth anchor: `D5/S3/Analytic/GermWindow/GoldenGermWindowLineDichotomy.golden_continued_germ_line_zero_iff_of_rh`
- Truth anchor: `D5/S3/Analytic/GermWindow/GoldenGermWindowLineDichotomy.golden_continued_germ_off_line_zero_iff_of_rh`
- Dependency: [D5/S3/Analytic/EulerGerm/LocalFactorCriticalLineNonvanishing](../EulerGerm/LocalFactorCriticalLineNonvanishing.md)
- Dependency: [D5/S3/Analytic/GermWindow/GoldenGermThirdOrderWindowZeroCriterion](GoldenGermThirdOrderWindowZeroCriterion.md)
