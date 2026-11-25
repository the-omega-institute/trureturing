# Sparse masks for the regular order-ninety lift list

## Abstract

Sparse masks for the regular order-ninety lift list

**Definition 1.1 (Thirty-two supports and their transverse masks).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.records`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.records` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input consists of thirty-two literal supports from the regular twelve-plus-three lift list. Each record stores its axis and three-direction mask.

**Theorem 1.2 (Exclusion of every listed support).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.listed_support_not_universal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.listed_support_not_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed local tests are evaluated by the Lean kernel. Every listed support fails universal weighted sharpness under any coherent switching.

**Definition 1.3 (Survival of a listed candidate under universal weighted sharpness).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim asks whether there exists a record in the literal list, a coherent switching of its support and a retained parity for which every real coordinate weighting admits a nonzero vector in the kernel of the signed boundary matrix.

**Theorem 1.4 (Refutation of survival in the regular lift list).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel-checked tests and their soundness exclude the proposed witness for any record, switching and retained parity. This settles the candidate-survival obligation for the thirty-two enumerated inputs. Exhaustion of the signed orbit census and the bridge from arbitrary components to this list remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.listed_support_not_universal`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.records`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData.result`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate](Q9SparseMaskCertificate.md)
