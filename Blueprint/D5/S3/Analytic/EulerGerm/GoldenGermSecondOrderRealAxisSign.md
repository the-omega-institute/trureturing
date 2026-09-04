# Golden Germ Second-Order Real-Axis Sign

## Abstract

The explicit second-order golden germ continuation is real and strictly negative between the structural and golden boundaries.

**Theorem 1.1 (The second-order continuation is negative between its two boundaries).**

$$\begin{aligned}\forall s\in \mathbb{C}, \operatorname{H}(s) := \prod_{p\in \operatorname{Primes}(\mathbb{N})}(1 - p^{-s \times \varphi^{3}}) \times (1 + p^{-s \times \varphi^{2}})^{-1} \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)},\\\forall s\in \mathbb{C}, \operatorname{F2}(s) := \operatorname{riemannZeta}(\varphi^{2} \times s) \times \operatorname{riemannZeta}(\varphi^{3} \times s) \times (\operatorname{riemannZeta}(2 \times \varphi^{2} \times s))^{-1} \times \operatorname{H}(s),\\\forall sigma\in \mathbb{R}, \frac{1}{\varphi^{3}} < sigma < \frac{1}{\varphi^{2}} \Rightarrow \operatorname{Im}(\operatorname{F2}(sigma)) = 0 \land \Re(\operatorname{F2}(sigma)) < 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderRealAxisSign.golden_germ_second_order_real_axis_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the next real-axis sign step in the golden Euler germ extraction ladder of OACTC parts 580 and 581. It advances the open interval between one over phi cubed and one over phi squared by determining the sign of the explicit second-order continuation throughout that interval.

Every real second-normalized Euler factor is strictly positive: the cubed mode lies below one, the inverse squared-mode factor is positive, and the local germ series is a convergent sum of positive terms. Frozen deviation summability carries this positivity through the multipliable infinite product.

For the remaining factors, the paired Dirichlet eta series proves that zeta is negative on the real interval from zero to one. The cubed and doubled-squared zeta arguments exceed one and therefore contribute positive real factors.

The theorem is confined to the strict real interval and to the displayed second-order continuation. It does not establish O-5 or RH, a complex zero-free region, or any all-order extraction statement.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderRealAxisSign.golden_germ_second_order_real_axis_negative`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermRealAxisPositivity](GoldenGermRealAxisPositivity.md)
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization](GoldenGermSecondOrderFactorization.md)
- Dependency: [D5/S3/Analytic/Isolation/GoldenAuxiliaryZetaNonzero](../Isolation/GoldenAuxiliaryZetaNonzero.md)
- Dependency: [D5/S3/Analytic/Regularity/GoldenGermSecondNormalizedFactorRegularity](../Regularity/GoldenGermSecondNormalizedFactorRegularity.md)
