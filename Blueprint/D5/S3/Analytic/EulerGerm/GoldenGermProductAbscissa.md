# Golden Germ Product Abscissa

## Abstract

The explicit golden exponent gives a prime-local Euler product whose exact absolute-convergence boundary is one over phi squared.

**Theorem 1.1 (The golden germ product has its exact abscissa).**

$$(\forall v\in\mathbb{N}, \operatorname{o5Beta}(v) = \sqrt{5} \times v + \frac{1}{\varphi} - \operatorname{fract}((v+1) \times \varphi)) \land \operatorname{o5Beta}(1) = \varphi^{2} \land \operatorname{o5Beta}(2) = \varphi^{3} \land (\forall sigma\in\mathbb{R}, \operatorname{Summable}((p,v)\mapsto e^{-sigma \times \operatorname{goldenSpectrum}(p, v)}) \Leftrightarrow \frac{1}{\varphi^{2}} < sigma) \land (\forall s\in\mathbb{C}, \frac{1}{\varphi^{2}} < \Re(s) \Rightarrow \operatorname{HasProd}(p\mapsto \sum_{v\ge0}p^{-s \times \operatorname{o5Beta}(v)}, \prod_{p \text{prime}}\sum_{v\ge0}p^{-s \times \operatorname{o5Beta}(v)})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/GoldenGermProductAbscissa.golden_germ_product_abscissa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponent is the canonical golden exponent already used by the Euler-germ family. Its first two positive values isolate the prime term and the faster tail.

The convergence equivalence includes divergence at the boundary. Above that boundary the canonical prime-local factors have the displayed infinite product.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/GoldenGermProductAbscissa.golden_germ_product_abscissa`
