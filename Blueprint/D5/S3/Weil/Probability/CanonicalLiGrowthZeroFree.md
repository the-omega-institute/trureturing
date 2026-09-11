# CanonicalLiGrowthZeroFree

## Abstract

Use the merged derivative-defined canonical Li sequence to prove actual xi zero-freeness from an all-index growth condition.

**Definition 1.1 (The actual canonical coefficient sum).**

$$\forall z \in \mathbb{C},\; \operatorname{canonicalLiSeries}\left(z\right) = \sum_{n=0}^{\infty}\operatorname{canonicalLiCoefficient}\left(n + 1\right) \cdot z^{n}$$

*Formalization.* `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonicalLiSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficients are imported from CanonicalLiLocalExpansion. Their definition and indexing are unchanged.

**Definition 1.2 (The actual xi function in disk coordinates).**

$$\forall z \in \mathbb{C},\; \operatorname{canonicalXiDisk}\left(z\right) = \operatorname{xiReading}\left(\frac{1}{1 - z}\right)$$

*Formalization.* `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonicalXiDisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is precisely xiReading composed with the standard inverse Mobius coordinate.

**Theorem 1.3 (Disk analyticity without a zero-location premise).**

$$\operatorname{AnalyticOnNhd}\left(\mathbb{C}, \mathit{canonicalXiDisk}, \operatorname{ball}\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_xi_disk_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire original xiReading and the nonvanishing coordinate denominator prove analyticity on the entire unit disk.

**Theorem 1.4 (Consume the existing canonical local expansion).**

$$(\forall^{f} z \in \mathcal{N}(0), \operatorname{deriv}\left(\mathit{canonicalXiDisk}, z\right) = \operatorname{canonicalLiSeries}\left(z\right) \cdot \operatorname{canonicalXiDisk}\left(z\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_xi_disk_local_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual derivative chain rule and the merged all-order local series give F'=GF near zero, using only xi(1)=1/2 to justify local cancellation.

**Theorem 1.5 (Global disk equation and no zeros).**

$$\left(\forall r \in \mathbb{R}_{\geq0},\; r < 1 \Rightarrow \operatorname{Summable}\left((n:\mathbb{N}\mapsto\left|\operatorname{canonicalLiCoefficient}\left(n + 1\right)\right| \cdot r^{n})\right)\right) \Rightarrow \left(\operatorname{AnalyticOnNhd}\left(\mathbb{C}, \mathit{canonicalLiSeries}, \operatorname{ball}\left(0, 1\right)\right) \land \left(\left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{deriv}\left(\mathit{canonicalXiDisk}, z\right) = \operatorname{canonicalLiSeries}\left(z\right) \cdot \operatorname{canonicalXiDisk}\left(z\right)\right) \land \left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{canonicalXiDisk}\left(z\right) \ne 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_li_summable_disk_zero_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absolute convergence at every smaller radius makes the same scalar sum analytic. The local equation extends and analytic orders exclude every disk zero.

**Theorem 1.6 (Bare disk to whole half-plane).**

$$\left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{canonicalXiDisk}\left(z\right) \ne 0\right) \Rightarrow \left(\forall s \in \mathbb{C},\; \frac{1}{2} < \operatorname{Re}\left(s\right) \Rightarrow \operatorname{xiReading}\left(s\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.xi_disk_zero_free_right_half_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Re(s)>1/2, set z=1-s inverse. The norm-square inequality puts z in the open disk and the inverse map returns s. No Li premise occurs.

**Theorem 1.7 (Bare disk converse to standard RH).**

$$\left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{canonicalXiDisk}\left(z\right) \ne 0\right) \Rightarrow \mathit{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.xi_disk_zero_free_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The half-plane transfer feeds ActualZeroGeometry.rh_iff_xi_right_half_plane. Both existing summability consumers below use this bare bridge after disk nonvanishing.

**Theorem 1.8 (Actual open right-half-plane nonvanishing).**

$$\left(\forall r \in \mathbb{R}_{\geq0},\; r < 1 \Rightarrow \operatorname{Summable}\left((n:\mathbb{N}\mapsto\left|\operatorname{canonicalLiCoefficient}\left(n + 1\right)\right| \cdot r^{n})\right)\right) \Rightarrow \left(\forall s \in \mathbb{C},\; \frac{1}{2} < \operatorname{Re}\left(s\right) \Rightarrow \operatorname{xiReading}\left(s\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_li_summable_right_half_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse Mobius point lies in the unit disk precisely in the direction needed. Its round trip recovers the original complex argument.

**Theorem 1.9 (The standard RiemannHypothesis conclusion).**

$$\left(\forall r \in \mathbb{R}_{\geq0},\; r < 1 \Rightarrow \operatorname{Summable}\left((n:\mathbb{N}\mapsto\left|\operatorname{canonicalLiCoefficient}\left(n + 1\right)\right| \cdot r^{n})\right)\right) \Rightarrow \mathit{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_li_disk_summability_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Existing actual xi-zero identification and right-half-strip reduction connect the no-zero result to Mathlib RiemannHypothesis. No supplied Li criterion is used.

**Theorem 1.10 (An explicit all-index growth condition suffices).**

$$\forall C \in \mathbb{R},\; \left(\forall n \in \mathbb{N},\; \left|\operatorname{canonicalLiCoefficient}\left(n\right)\right| \le C \cdot n^{2}\right) \Rightarrow \mathit{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_li_quadratic_growth_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An absolute quadratic bound on every actual canonical coefficient supplies the required disk convergence. The arithmetic bound itself is not proved here.

**Theorem 1.11 (Consumer for the prior probability envelope).**

$$\left(\forall n \in \mathbb{N},\; 0 \le \operatorname{canonicalLiCoefficient}\left(n\right) \land \operatorname{canonicalLiCoefficient}\left(n\right) \le \operatorname{canonicalLiCoefficient}\left(1\right) \cdot n^{2}\right) \Rightarrow \mathit{RiemannHypothesis}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_li_probability_envelope_implies_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input is the earlier probability route's exact output shape with its sequence identified as canonicalLiCoefficient. No candidate probability modules are copied into this branch.

**Theorem 1.12 (Every quadratic bound must fail under a failed RH).**

$$\left(\neg \mathit{RiemannHypothesis}\right) \Rightarrow \left(\forall C \in \mathbb{R},\; \exists n \in \mathbb{N},\; C \cdot n^{2} < \left|\operatorname{canonicalLiCoefficient}\left(n\right)\right|\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.not_rh_forces_quadratic_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The contrapositive produces an index exceeding any proposed absolute quadratic bound. It gives no finite cutoff for finding such an index.

## References

- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonicalLiSeries`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonicalXiDisk`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_li_disk_summability_implies_rh`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_li_probability_envelope_implies_rh`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_li_quadratic_growth_implies_rh`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_li_summable_disk_zero_free`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_li_summable_right_half_plane`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_xi_disk_analytic`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.canonical_xi_disk_local_equation`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.not_rh_forces_quadratic_escape`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.xi_disk_zero_free_implies_rh`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.xi_disk_zero_free_right_half_plane`
- Dependency: [D5/S3/Weil/Probability/AnalyticLogarithmicContinuation](AnalyticLogarithmicContinuation.md)
- Dependency: [D5/S3/Zeros/ActualZeroGeometry](../../Zeros/ActualZeroGeometry.md)
- Dependency: [D5/S3/Zeros/Endpoints/CanonicalLiLocalExpansion](../../Zeros/Endpoints/CanonicalLiLocalExpansion.md)
