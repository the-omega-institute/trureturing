# Full signed original current Borcherds identity

## Abstract

Full signed original current Borcherds identity

**Theorem 1.1 (The corrected seed at every signed half-mode).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_current_minus_one_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_current_minus_one_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The literal Corr multiplication seed at mode one half extends by physical split crossings. Each adjacent crossing consumes the original current commutator; signed integer induction crosses only finitely many modes. The original fields and source states are unchanged.

**Theorem 1.2 (The forward discrepancy recurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.discrepancy_forward`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.discrepancy_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The discrepancy at order n+1 is the difference of discrepancies at order n, evaluated at the adjacent half-mode and with cover exponent decreased by two. Each side is the original pointwise current residue. The proof uses finite Pascal telescoping and preserves the signed integer phase of the second right term.

**Theorem 1.3 (Every nonnegative current product order).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_nonnegative_current_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_nonnegative_current_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The original current commutator gives product order zero. The finite forward discrepancy recurrence then proves the actual identity at every nonnegative order, with arbitrary signed half-mode, cover exponent, original second source and actual tensor target.

**Theorem 1.4 (The physical translation discrepancy recurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.discrepancy_backward`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.discrepancy_backward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Original source translation covariance and the physical derivative of Ytw give the backward discrepancy recurrence. Its coefficient is (E+2j+3)/2. Source, first-right and second-right supports justify every distribution and reindexing before the signed generalized-binomial cancellation.

**Theorem 1.5 (Every integer current product order).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_signed_current_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_signed_current_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The original current commutator starts the nonnegative induction. The genuinely corrected minus-one seed starts the negative induction; the backward recurrence divides only by its nonzero integer order. The resulting exact pointwise finite residues agree for arbitrary integer product order, signed half-mode and cover exponent, arbitrary original second source, and actual tensor target, assuming only lattice data and invertibility of its Gram determinant.

This is the current-generator twisted Borcherds identity, not arbitrary-first-source twisted Jacobi. No positivity, inverse-Gram choice, vacuum target, occupation cutoff or assumed seed/module law is used. Full string-theoretic and AdS/CFT bridges remain outside this result.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_current_minus_one_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_nonnegative_current_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_signed_current_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.discrepancy_backward`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.discrepancy_forward`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds](LatticeHalfFockCurrentBorcherds.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeedConstruction](LatticeHalfFockCurrentSeedConstruction.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](LatticeHalfFockOriginalTranslation.md)
