# Quotient CUT Normal Form

## Abstract

A decidable kernel supplies a computable quotient whose projection is a canonical CUT.

**Definition 1.1 (Kernel setoid).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.toSetoid`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.toSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel equivalence proof equips its relation with the canonical Setoid interface.

**Definition 1.2 (Canonical quotient CUT).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.quotientCut`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.quotientCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each state is sent to its equivalence class under the kernel relation.

**Definition 1.3 (Decidable quotient equality).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.instDecidableEqQuotient`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.instDecidableEqQuotient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equality of quotient representatives is decided by the underlying kernel decision.

**Theorem 1.4 (Quotient CUT kernel normal form).**

$$\forall K: \operatorname{DecidableKernel}\left(X\right), \forall x, y: X, \operatorname{relation}\left(K, x, y\right) \iff \operatorname{quotientCut}\left(K, x\right) = \operatorname{quotientCut}\left(K, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.quotient_cut_kernel_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib quotient equality identifies precisely the pairs related by the source kernel.

**Theorem 1.5 (The CUT constructor recovers the kernel).**

$$\forall K: \operatorname{DecidableKernel}\left(X\right), \forall x, y: X, \operatorname{relation}\left(\operatorname{cutKernel}\left(\operatorname{quotientCut}\left(K\right)\right), x, y\right) \iff \operatorname{relation}\left(K, x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.cutKernel_quotientCut_relation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The decidable quotient equality makes the generic CUT constructor available without changing the relation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.cutKernel_quotientCut_relation_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.instDecidableEqQuotient`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.quotientCut`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.quotient_cut_kernel_normal_form`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm.toSetoid`
- Dependency: [D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel](PrimitiveKernel.md)
