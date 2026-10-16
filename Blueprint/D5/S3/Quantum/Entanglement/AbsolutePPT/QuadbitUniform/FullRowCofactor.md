# Ordered full-row cofactors

## Abstract

Ordered full-row cofactors.

**Theorem 1.1 (Ordered full-row cofactors).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/FullRowCofactor.cofactor_candidate_ordered_full`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/FullRowCofactor.cofactor_candidate_ordered_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B be a real m-by-n matrix whose columns span the whole m-dimensional row space. A nonzero vector satisfying exact cofactorCandidates membership, including all original kernel equations, is a positive multiple of one orientation of an ordered full-row cofactor. The original nonnegative kernel equations are preserved for every row. A nonzero deleted minor supplies independent columns; extending these columns to a basis and sorting their indices gives a support of size m+1. Distinct indices remain distinct even when column values agree. The cofactor cross identity fixes the orientation and positive scale, including zero coordinates.

These statements concern real scalar spectra and finite cofactor certificates. Connecting the boundary inequalities to a physical APPT model, constructing an attaining state, and determining a purity supremum require additional results.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/FullRowCofactor.cofactor_candidate_ordered_full`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCofactor](../NonnegativeKernelCofactor.md)
