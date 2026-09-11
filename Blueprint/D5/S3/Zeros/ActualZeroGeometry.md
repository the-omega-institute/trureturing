# Actual zero geometry

## Abstract

Dictionaries for actual xi zeros and standard Mathlib RiemannHypothesis; no assertion of RH.

**Theorem 1.1 (A001: the nontrivial-zero dictionary).**

$$\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(\mathit{rho}\right) \Rightarrow \operatorname{Re}\left(\mathit{rho}\right) = \frac{1}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ActualZeroGeometry.rh_iff_nontrivial_zeros_on_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

IsNontrivialZero means riemannZeta(rho)=0 and 0<Re(rho)<1. RH is Mathlib's full predicate: for every complex s, riemannZeta(s)=0, exclusion of s=-2(n+1) for every natural n, and s!=1 imply Re(s)=1/2.

**Theorem 1.2 (A002: all complex center coordinates).**

$$\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall z \in \mathbb{C},\; \operatorname{xiReading}\left(\frac{1}{2} + i \cdot z\right) = 0 \Rightarrow \operatorname{Im}\left(z\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ActualZeroGeometry.rh_iff_xi_central_zeros_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate convention is plus i, with inverse -i(rho-1/2). The frozen inverse laws and actual xi-zero correspondence supply both directions.

**Theorem 1.3 (A003: the entire open right half-plane).**

$$\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall s \in \mathbb{C},\; \frac{1}{2} < \operatorname{Re}\left(s\right) \Rightarrow \operatorname{xiReading}\left(s\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ActualZeroGeometry.rh_iff_xi_right_half_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain includes s=1. Growth's bare disk converse consumes this dictionary before its existing summability-to-RH theorem.

**Theorem 1.4 (The guarded Cayley adapter).**

$$\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(\mathit{rho}\right) \Rightarrow 1 - \frac{1}{\mathit{rho}} = \operatorname{cayleyRatio}\left(\mathit{rho}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ActualZeroGeometry.nontrivial_zero_cayley_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strip positivity proves rho is nonzero before division is simplified. The equality is not asserted at an arbitrary complex zero denominator.

**Theorem 1.5 (A004: the actual unit-norm condition).**

$$\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(\mathit{rho}\right) \Rightarrow \left\lVert 1 - \frac{1}{\mathit{rho}} \right\rVert = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ActualZeroGeometry.rh_iff_nontrivial_zero_cayley_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen Cayley locus theorem supplies both directions. These dictionaries are prerequisites of the source package in DiskEquivalence; that conjunction alone grants no admission.

## References

- Truth anchor: `D5/S3/Zeros/ActualZeroGeometry.nontrivial_zero_cayley_eq`
- Truth anchor: `D5/S3/Zeros/ActualZeroGeometry.rh_iff_nontrivial_zero_cayley_norm`
- Truth anchor: `D5/S3/Zeros/ActualZeroGeometry.rh_iff_nontrivial_zeros_on_line`
- Truth anchor: `D5/S3/Zeros/ActualZeroGeometry.rh_iff_xi_central_zeros_real`
- Truth anchor: `D5/S3/Zeros/ActualZeroGeometry.rh_iff_xi_right_half_plane`
- Dependency: [D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup](../Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup.md)
- Dependency: [D5/S3/Midline/CayleyCriticalLine](../Midline/CayleyCriticalLine.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../Weil/ZetaBridge/RightHalfStripRiemannReduction.md)
- Dependency: [D5/S3/Zeros/Symmetry/CriticalCenterCoordinate](Symmetry/CriticalCenterCoordinate.md)
