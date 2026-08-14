# Zero Symmetry Action

## Abstract

A supplied zero enumeration transports reflection and conjugation to commuting index actions.

**Theorem 1.1 (Zero reflection and conjugation commute).**

$$\forall Z: \operatorname{ZeroData},\ \operatorname{Commute}(Z.reflection, Z.conjugation).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ZeroSymmetryAction.zero_symmetries_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every supplied ZeroData value, the reflection and conjugation permutations commute. The proof compares their enumerated zeros and uses duplicate-freeness; it constructs no zero enumeration and assumes no critical-line statement.

**Theorem 1.2 (A mirror index is fixed exactly on the critical line).**

$$\forall Z: \operatorname{ZeroData},\ \forall n\in \mathbb{N},\ Z.conjugation(Z.reflection(n)) \Leftrightarrow \Re(Z.zero(n)) = \operatorname{criticalAbscissa}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ZeroSymmetryAction.mirror_index_fixed_iff_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each index of a supplied ZeroData value, conjugation after reflection fixes the index exactly when the indexed zero has critical real part. The forward direction lifts index equality to mirror fixedness and applies the repository's fixed-point theorem; the reverse direction uses enumeration injectivity.

**Theorem 1.3 (All nontrivial zeros are critical exactly when mirror indices are fixed).**

$$\forall Z: \operatorname{ZeroData},\ (\forall \rho\in \mathbb{C},\ \operatorname{IsNontrivialZero}(\rho) \Rightarrow \Re(\rho) = \operatorname{criticalAbscissa}) \Leftrightarrow \forall n\in \mathbb{N},\ Z.conjugation(Z.reflection(n)) = n.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/ZeroSymmetryAction.all_nontrivial_zeros_critical_iff_mirror_indices_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditional on a supplied duplicate-free exhaustive ZeroData enumeration, every classical nontrivial zero lies on the critical line exactly when every conjugate-reflection index is fixed. Exhaustiveness transports the indexwise equivalence to arbitrary nontrivial zeros. The theorem constructs no ZeroData inhabitant and therefore makes no unconditional Riemann hypothesis claim.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/ZeroSymmetryAction.all_nontrivial_zeros_critical_iff_mirror_indices_fixed`
- Truth anchor: `D5/S3/Zeros/Symmetry/ZeroSymmetryAction.mirror_index_fixed_iff_critical`
- Truth anchor: `D5/S3/Zeros/Symmetry/ZeroSymmetryAction.zero_symmetries_commute`
- Dependency: [D5/S3/Weil/ReflectionLedger](../../Weil/ReflectionLedger.md)
