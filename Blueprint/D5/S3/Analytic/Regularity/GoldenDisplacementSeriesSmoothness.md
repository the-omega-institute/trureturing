# Golden Displacement Series Smoothness

## Abstract

The golden displacement sum is smooth at every point of its exact convergence region.

**Theorem 1.1 (The displacement sum is smooth on its convergence region).**

$$\operatorname{ContDiffOn}(\mathbb{R}, \infty, p : \mathbb{R} \times \mathbb{R} \mapsto \sum_{n=0}^{\infty} \operatorname{dTerm}(p.1, p.2, n), \left\{p : \mathbb{R} \times \mathbb{R} \mid \operatorname{Summable}(\operatorname{dTerm}(p.1, p.2))\right\})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Regularity/GoldenDisplacementSeriesSmoothness.golden_displacement_series_contDiffOn_infty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses contDiffOn_infty to fix a finite order k and then works at an arbitrary parameter pair in the convergence region. The two strict affine constraints provide a positive delta. The proof lowers both coordinates by (k+1) times delta to obtain a corner point whose dTerm family is summable, and it works on the open quadrant above the point obtained by lowering both coordinates by delta. Because delta carries the factor 1/(k+1), that corner and its summable dTerm family are the same at every order; what depends on k is delta, the open quadrant, and the scalar factors (2/delta)^j.

For a positive index n, the term is exp composed with a continuous linear functional ell(n), with coefficients -log(nS(n)) and -log(n). ContinuousLinearMap.iteratedFDeriv_comp_right expresses its jth Frechet derivative as the jth one-variable derivative of exp composed with ell(n) in every argument. The norm comparison for that composition, norm_iteratedFDeriv_eq_norm_iteratedDeriv, and Real.iter_deriv_exp give a bound by dTerm at the variable point times the jth power of the norm of ell(n).

The real logarithm estimate log(x) <= x^delta/delta is used only for natural bases at least one. Nonnegativity of log at those bases converts the logarithm to its norm, and natural-power monotonicity raises the resulting nonnegative inequality. Coordinatewise real-power monotonicity gives non-strict bounds on the quadrant. Since j <= k, the j powers of both bases are absorbed by the gap between the quadrant and the corner. The norm of the nth jth-derivative continuous multilinear map is at most (2/delta)^j times the nth value of the summable corner-term family.

At index zero, the summand and every iterated derivative used by the proof are zero. At index one, dTerm is one, nS(1) is one, and both logarithms vanish; hence every positive-order derivative term is zero, while the order-zero bound compares the constant term with the corner term, also one. At order zero, continuousOn_tsum uses the summable corner-term family directly and does not infer continuity from pointwise summability.

A private localized finite-order sum lemma supplies the missing multivariable local form of Mathlib's global smooth-series theorem. Its zero case is continuousOn_tsum. In the successor case, hasFDerivAt_tsum_of_isPreconnected identifies the derivative of the sum, norm_iteratedFDeriv_fderiv shifts the derivative bounds by one order, and the induction hypothesis applies to the family of Frechet derivatives. Local congruence identifies that derivative series with fderiv of the original sum. This proves every finite order at the chosen point, and contDiffOn_infty yields smoothness on the exact region.

The theorem does not claim real analyticity of order omega, complex analyticity or continuation, a published formula for any iterated derivative or Hessian, one derivative majorant valid for every order, a majorant uniform near the convergence-region boundary, or strict termwise decrease.

## References

- Truth anchor: `D5/S3/Analytic/Regularity/GoldenDisplacementSeriesSmoothness.golden_displacement_series_contDiffOn_infty`
