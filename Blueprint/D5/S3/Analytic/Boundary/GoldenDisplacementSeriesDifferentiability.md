# Golden Displacement Series Differentiability

## Abstract

The golden displacement sum is differentiable at every point of its exact convergence region.

**Theorem 1.1 (The displacement sum is differentiable on its convergence region).**

$$\operatorname{DifferentiableOn}(\mathbb{R}, p : \mathbb{R} \times \mathbb{R} \mapsto \sum_{n=0}^{\infty} \operatorname{dTerm}(p.1, p.2, n), \left\{p : \mathbb{R} \times \mathbb{R} \mid \operatorname{Summable}(\operatorname{dTerm}(p.1, p.2))\right\})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/GoldenDisplacementSeriesDifferentiability.golden_displacement_series_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a parameter pair in the convergence region, the two strict affine constraints give a positive margin delta. Lowering both coordinates by twice that margin produces another parameter pair in the region. The term family evaluated at this lower pair is summable.

The index-zero term is identically zero and its derivative is the zero map. At every positive index, differentiating the two real-power factors gives two linear-map summands with coefficients containing log(nS(n)) and log(n). The proof uses log(x) <= x^delta/delta and the coordinatewise exponent inequalities on the open quadrant above the intermediate parameter pair. The norm of each derivative summand is bounded by dTerm at the lower pair divided by delta. At index one both logarithms are zero, consistently with dTerm(s,w,1) being constant.

Consequently, the sequence whose nth value is (2/delta) times dTerm at the lower parameter pair is summable and bounds the norm of the nth Frechet derivative throughout that open quadrant. Pinned Mathlib's local preconnected-domain theorem for derivatives of infinite sums therefore gives a Frechet derivative at the original parameter pair.

The theorem records differentiability only on the exact summability region. It does not publish a formula for the derivative, claim higher smoothness, or assert one derivative majorant valid up to the region's boundary.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/GoldenDisplacementSeriesDifferentiability.golden_displacement_series_differentiableOn`
