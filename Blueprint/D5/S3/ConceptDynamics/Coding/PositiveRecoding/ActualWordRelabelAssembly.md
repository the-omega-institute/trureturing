# Assemble actual dictionary weights over typed words

## Abstract

Assemble actual dictionary weights over typed words.

path_append_weight proves additivity for dependent finite kernel-ladder paths, including the equality transports in append. dictionary_residue proceeds through the relabel, positive and composition constructors of the original endpoint-typed Word. It uses the actual relabel comparison, both positive-leaf chart corrections and additive concatenation.

The path theorem ranges over Based objects X,Y,Z and arbitrary lengths n,m. The dictionary theorem ranges over every Presentation pair F,H, Word F H and every d with NeZero d and 3 ∣ d. No original-h specialization is introduced and no endpoint correction is erased.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Theorem 1.1 (path_append_weight).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordRelabelAssembly.path_append_weight`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordRelabelAssembly.path_append_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weight is additive under actual path concatenation.

**Remark 1.2 (dictionary_residue).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordRelabelAssembly.dictionary_residue`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordRelabelAssembly.dictionary_residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual matrix dictionary weight is the same P1 localized cochain. Both positive-leaf charts and every relabel-leaf phase are retained.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordRelabelAssembly.dictionary_residue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordRelabelAssembly.path_append_weight`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts](ActualRelabelCharts.md)
