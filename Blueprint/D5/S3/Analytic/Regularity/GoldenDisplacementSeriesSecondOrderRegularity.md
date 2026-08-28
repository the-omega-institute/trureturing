# Golden Displacement Series Second-Order Regularity

## Abstract

The golden displacement sum is twice continuously differentiable at every point of its exact convergence region.

**Theorem 1.1 (The displacement sum has second-order regularity on its convergence region).**

$$\operatorname{ContDiffOn}(\mathbb{R}, 2, p : \mathbb{R} \times \mathbb{R} \mapsto \sum_{n=0}^{\infty} \operatorname{dTerm}(p.1, p.2, n), \left\{p : \mathbb{R} \times \mathbb{R} \mid \operatorname{Summable}(\operatorname{dTerm}(p.1, p.2))\right\})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Regularity/GoldenDisplacementSeriesSecondOrderRegularity.golden_displacement_series_contDiffOn_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a parameter pair in the convergence region, the two strict affine constraints give a positive margin delta. The proof lowers both coordinates by three times that margin to obtain a new parameter pair. This lower pair is a point, while the family whose nth value is dTerm at that point is summable. The proof works on the open quadrant above the intermediate pair obtained by lowering both coordinates by delta.

For a positive index, the term is rewritten as the exponential of a continuous linear functional whose coefficients are -log(nS(n)) and -log(n). Its first derivative is exponential times that functional; its second derivative is the corresponding iterated continuous linear map. At index zero, the term and both displayed derivative families are zero. At index one, nS(1) = 1 and both logarithms vanish, so the first- and second-derivative terms are also zero. Order zero is handled by the identity between the exponential presentation and dTerm, which transfers the original parameter pair's summability to the exponential family and supplies the base-point hypothesis of the first local termwise-differentiation step.

On the open quadrant, coordinatewise real-power monotonicity gives non-strict inequalities. Applying log(x) <= x^delta/delta once bounds the norm of the nth first-derivative continuous linear map by (2/delta) times the nth value of the summable corner-term family. Applying it twice and using (a+b)^2 <= 2a^2+2b^2 bounds the norm of the nth second-derivative continuous linear map by (4/delta^2) times that same corner-term family.

The local preconnected-domain theorem for derivatives of infinite sums constructs the first two Frechet derivatives. The second-derivative family is continuous term by term, and continuousOn_tsum makes its sum continuous on the quadrant. These facts give ContDiffAt of order two at the original point, hence ContDiffOn of order two on the exact summability region.

The theorem does not claim ContDiffOn of top order, ContDiffOn of every finite order, real analyticity, complex analyticity or continuation, or a published Hessian formula. It also does not provide one derivative majorant valid near the convergence-region boundary, and it does not assert strict termwise decrease.

## References

- Truth anchor: `D5/S3/Analytic/Regularity/GoldenDisplacementSeriesSecondOrderRegularity.golden_displacement_series_contDiffOn_two`
