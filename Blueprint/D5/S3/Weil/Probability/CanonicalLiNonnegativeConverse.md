# CanonicalLiNonnegativeConverse

## Abstract

Prove the A006 reverse implication at the original derivative-defined canonical Li coefficients.

**Theorem 1.1 (All positive-index canonical coefficients are nonnegative implies RH).**

$$\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow 0 \le \operatorname{canonicalLiCoefficient}\left(n\right)\right) \Rightarrow \mathit{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse.canonical_li_nonnegative_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Philippe Flajolet and Robert Sedgewick (2009). *Analytic Combinatorics*. URL: <https://algo.inria.fr/flajolet/Publications/book.pdf>.

*Commentary.*

The only premise is nonnegativity of canonicalLiCoefficient n for every natural n at least one. The conclusion is standard Mathlib RiemannHypothesis. The canonical derivative definition and the n+1 series shift are retained.

The positive-boundary proof follows Theorem IV.6 and item IV.13. A genuine continuation at a finite positive radius gives convergence of the recentered series past the original boundary. Scalar uniqueness and nonnegative double summation imply original-series convergence there, contradicting the radius. The finite-subset identity is proved using map_add_univ; the inconsistent later exponents on printed p.242 are not copied.

At real x in [0,1), the original xi argument (1-x) inverse is at least one and cannot be a strict-strip zero. Thus the actual generator is analytic there. Frozen analytic continuation uniqueness identifies the series along the real segment. The resulting convergence at every NNReal r<1, including zero, feeds the frozen canonical_li_disk_summability_implies_rh theorem.

The Li specialization is repository assembly with the cited Pringsheim argument acknowledged. This is A006 reverse only. A007 reverse may later consume it; forward positivity, strictness and the fixed-lambda1 A013 bound remain unchanged.

**Theorem 1.2 (A finite positive radius is singular for nonnegative coefficients).**

$$\forall a \in \mathbb{N} \to \mathbb{R},\; \left(\forall n \in \mathbb{N},\; 0 \le a\left(n\right)\right) \Rightarrow \left(\forall R \in \mathit{NNReal},\; 0 < R \Rightarrow \left((\operatorname{FormalMultilinearSeries.ofScalars}\left(\mathbb{C}, (\mathit{fun} n: \mathbb{N} \mapsto (a\left(n\right): \mathbb{C}))\right)).\mathit{radius} = (R: \mathit{ENNReal}) \Rightarrow \left(\forall g \in \mathbb{C} \to \mathbb{C},\; \operatorname{AnalyticAt}\left(\mathbb{C}, g, (R: \mathbb{C})\right) \Rightarrow \left(\left(\exists e \in \mathbb{R},\; 0 < e \land \left(\forall x \in \mathbb{R},\; (R: \mathbb{R}) - e < x \Rightarrow \left(x < (R: \mathbb{R}) \Rightarrow \left(0 \le x \Rightarrow g\left((x: \mathbb{C})\right) = \sum'_{n} (a\left(n\right): \mathbb{C}) \cdot (x: \mathbb{C})^{n}\right)\right)\right)\right) \Rightarrow \mathit{False}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse.nonnegative_series_positive_boundary_obstruction` (`✓ std3`). ∎

*Citation.* Philippe Flajolet and Robert Sedgewick (2009). *Analytic Combinatorics*. URL: <https://algo.inria.fr/flajolet/Publications/book.pdf>.

*Commentary.*

For nonnegative real coefficients, an analytic complex function cannot agree with their power-series sum on a left interval at a finite positive radius. Theorem IV.6 and item IV.13, printed pages 240–242, give the Pringsheim argument. The displayed radius belongs to the scalar multilinear series with the real coefficients embedded in C. The real interval includes the condition x at least zero.

## References

- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse.canonical_li_nonnegative_implies_rh`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse.nonnegative_series_positive_boundary_obstruction`
- Dependency: [D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup](../../Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup.md)
- Dependency: [D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree](CanonicalLiGrowthZeroFree.md)
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)
- Dependency: [D5/S3/Zeros/Endpoints/CanonicalLiLocalExpansion](../../Zeros/Endpoints/CanonicalLiLocalExpansion.md)
