# Dominance after erasing an index

## Abstract

Dominance after erasing an index.

**Theorem 1.1 (Dominance after erasing an index).**

Lean statement: `D5/S3/Combinatorics/Scarf/Dominance.isDominant_erase_iff_M_set_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Scarf/Dominance.isDominant_erase_iff_M_set_empty` (`✓ std3`). ∎

*Citation.* Math_XMUM (2025). *Brouwer fixed-point theorem via Scarf's lemma*. URL: <https://github.com/math-xmum/Brouwer/tree/f9dc162170e8711f78059a87edcd38ffc44a1bfb>.

*Commentary.*

For finite T with an indexed family of linear orders and a nonempty door (tau,D), each i in D preserves dominance after erasure exactly when it lies in a collision pair of coordinate minima and M_i is empty. Each minimum is taken directly in its corresponding indexed linear order. The quantified pair and the empty-set condition are both required.

Coordinate minima cover every dominant cell. The one-unit deficit supplies a collision pair; an erasure away from that pair leaves a noninjective image with insufficient cardinality. Emptiness of M_i gives the reverse dominance implication.

The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Scarf/Dominance.isDominant_erase_iff_M_set_empty`
