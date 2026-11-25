# Sparse masks for the regular order-ninety lift list

## Abstract

Sparse masks for the regular order-ninety lift list

**Definition 1.1 (Thirty-two supports and their transverse masks).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.records`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.records` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The census of regular twelve-plus-three majority blocks gives the listed supports. Each record stores its axis and three-direction mask.

**Theorem 1.2 (Exclusion of every listed support).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.listed_support_not_universal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.listed_support_not_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed local tests are evaluated by the Lean kernel. Every listed support fails universal weighted sharpness under any coherent switching. The exhaustion of the signed orbit census is a separate mathematical obligation.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.listed_support_not_universal`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.records`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate](Q9SparseMaskCertificate.md)
