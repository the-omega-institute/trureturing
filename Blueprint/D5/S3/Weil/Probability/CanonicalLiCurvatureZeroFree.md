# CanonicalLiCurvatureZeroFree

## Abstract

The actual canonical Li curvature has a direct finite-matrix-to-growth-to-zero-freeness implication.

**Definition 1.1 (Actual normalized second differences).**

$$\forall n \in \mathbb{Z},\; \left(n = 0 \Rightarrow \operatorname{canonicalLiCurvature}\left(n\right) = 1\right) \land \left(n \ne 0 \Rightarrow \operatorname{canonicalLiCurvature}\left(n\right) = \frac{\operatorname{canonicalLiCoefficient}\left(\operatorname{natAbs}\left(n\right) + 1\right) - 2 \cdot \operatorname{canonicalLiCoefficient}\left(\operatorname{natAbs}\left(n\right)\right) + \operatorname{canonicalLiCoefficient}\left(\operatorname{NatSub}\left(\operatorname{natAbs}\left(n\right), 1\right)\right)}{2 \cdot \operatorname{canonicalLiCoefficient}\left(1\right)}\right)$$

*Formalization.* `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.canonicalLiCurvature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The curvature is explicitly derived from the existing real canonical coefficients, embedded in Complex, with value one at zero and an even integer extension. NatSub is truncated natural subtraction and natAbs is the natural absolute value of an integer.

**Theorem 1.2 (Normalization at the origin).**

$$\operatorname{canonicalLiCurvature}\left(0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.canonical_li_curvature_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Toeplitz diagonal normalization is fixed by the definition.

**Theorem 1.3 (Two finite inductions control every coefficient).**

$$\forall L \in \mathbb{N}\to\mathbb{R},\; \forall a \in \mathbb{R},\; \operatorname{L}\left(0\right) = 0 \Rightarrow \left(\left|\operatorname{L}\left(1\right)\right| \le a \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left|\operatorname{L}\left(n + 1\right) - 2 \cdot \operatorname{L}\left(n\right) + \operatorname{L}\left(\operatorname{NatSub}\left(n, 1\right)\right)\right| \le 2 \cdot a\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \left|\operatorname{L}\left(n\right)\right| \le a \cdot n^{2}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.quadratic_of_bounded_second_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bounded second differences first give a linear bound on increments, then an absolute quadratic bound on the original sequence. Coefficient positivity is unnecessary.

**Theorem 1.4 (A uniform arithmetic difference condition suffices).**

$$\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left|\operatorname{canonicalLiCoefficient}\left(n + 1\right) - 2 \cdot \operatorname{canonicalLiCoefficient}\left(n\right) + \operatorname{canonicalLiCoefficient}\left(\operatorname{NatSub}\left(n, 1\right)\right)\right| \le 2 \cdot \operatorname{canonicalLiCoefficient}\left(1\right)\right) \Rightarrow \mathit{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.canonical_li_second_difference_bound_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical initial values and the proved scalar induction supply the all-index growth bound consumed by actual xi analytic continuation.

**Theorem 1.5 (Extract the bound from the original finite matrix).**

$$\left(\forall N \in \mathbb{N},\; \operatorname{PosSemidef}\left(\operatorname{toeplitzMatrix}\left(\mathit{canonicalLiCurvature}, N\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left|\operatorname{canonicalLiCoefficient}\left(n + 1\right) - 2 \cdot \operatorname{canonicalLiCoefficient}\left(n\right) + \operatorname{canonicalLiCoefficient}\left(\operatorname{NatSub}\left(n, 1\right)\right)\right| \le 2 \cdot \operatorname{canonicalLiCoefficient}\left(1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.canonical_curvature_second_difference_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compress to indices zero and n and test the plus and minus vectors. Positivity of the canonical first coefficient justifies the normalized denominator.

**Theorem 1.6 (Canonical curvature positivity implies actual RH).**

$$\left(\forall N \in \mathbb{N},\; \operatorname{PosSemidef}\left(\operatorname{toeplitzMatrix}\left(\mathit{canonicalLiCurvature}, N\right)\right)\right) \Rightarrow \mathit{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.canonical_curvature_posSemidef_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sole arithmetic premise is positivity at every original Toeplitz order. No supplied Li criterion, arbitrary recurrence, representing measure or zero-measure identity is used.

**Theorem 1.7 (A finite-order obstruction under failure of RH).**

$$\left(\neg \mathit{RiemannHypothesis}\right) \Rightarrow \left(\exists N \in \mathbb{N},\; \neg \operatorname{PosSemidef}\left(\operatorname{toeplitzMatrix}\left(\mathit{canonicalLiCurvature}, N\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.not_rh_forces_canonical_curvature_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The contrapositive guarantees a failing finite matrix order without supplying a cutoff or turning finite successful tests into a proof.

## References

- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.canonicalLiCurvature`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.canonical_curvature_posSemidef_implies_rh`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.canonical_curvature_second_difference_bound`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.canonical_li_curvature_zero`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.canonical_li_second_difference_bound_implies_rh`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.not_rh_forces_canonical_curvature_failure`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.quadratic_of_bounded_second_difference`
- Dependency: [D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree](CanonicalLiGrowthZeroFree.md)
- Dependency: [D5/S3/Weil/TestFunctions/LiCurvatureCriterion](../TestFunctions/LiCurvatureCriterion.md)
