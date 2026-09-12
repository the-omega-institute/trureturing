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

The private positive-boundary proof follows Theorem IV.6 and item IV.13. A genuine continuation at a finite positive radius gives convergence of the recentered series past the original boundary. Scalar uniqueness and nonnegative double summation imply original-series convergence there, contradicting the radius. The finite-subset identity is proved using map_add_univ; the inconsistent later exponents on printed p.242 are not copied.

At real x in [0,1), the original xi argument (1-x) inverse is at least one and cannot be a strict-strip zero. Thus the actual generator is analytic there. Frozen analytic continuation uniqueness identifies the series along the real segment. The resulting convergence at every NNReal r<1, including zero, feeds the frozen canonical_li_disk_summability_implies_rh theorem.

The Li specialization is repository assembly with the cited Pringsheim argument acknowledged. This is A006 reverse only. A007 reverse may later consume it; forward positivity, strictness and the fixed-lambda1 A013 bound remain unchanged. No full equivalence atom, independent review, admission, freeze, coverage or publication is claimed by this document.

## References

- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse.canonical_li_nonnegative_implies_rh`
- Dependency: [D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree](CanonicalLiGrowthZeroFree.md)
