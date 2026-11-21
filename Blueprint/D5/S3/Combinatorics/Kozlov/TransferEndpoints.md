# The transfer matrices at the first and last states

## Abstract

The two count formulas become first-to-last entries of matrix powers. The endpoint row and column come from the singleton degree and the full simplex.

**Definition 1.1 (The first transfer state).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.firstState`

*Formalization.* `D5/S3/Combinatorics/Kozlov/TransferEndpoints.firstState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

This is state zero of the nonempty state set.

**Definition 1.2 (The terminal transfer state).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.lastState`

*Formalization.* `D5/S3/Combinatorics/Kozlov/TransferEndpoints.lastState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

This is the state whose zero-based index is n-1.

**Theorem 1.3 (Entries below the diagonal vanish).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_below`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The successor must fill all degrees through the preceding top. Its own top therefore cannot be smaller.

**Theorem 1.4 (Diagonal entries are one).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The successor must fill through its own top and vanish above it. This gives the unique skeleton at that state.

**Theorem 1.5 (The first row gives the initial counts).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_first_row`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_first_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

All carrier vectors already have full degree zero and one, so every state-j vector can follow the first state.

**Theorem 1.6 (The last column is all ones).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_last_column`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_last_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The full simplex is the unique terminal-state vector and it is an admissible successor from every state.

**Theorem 1.7 (Selecting the first row by a coordinate vector).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.first_vecMul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.first_vecMul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Multiplying by the first-state unit row picks the initial row.

**Theorem 1.8 (Selecting the last column by a coordinate vector).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.last_mulVec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.last_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Multiplying by the last-state unit column gives the all-ones column.

**Theorem 1.9 (The endpoint matrix power identity).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_sandwich`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Replace the two boundary vectors by the selected row and column and reassociate multiplication, adding two factors of the transfer matrix.

**Definition 1.10 (The proper transfer matrix).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.properTransfer`

*Formalization.* `D5/S3/Combinatorics/Kozlov/TransferEndpoints.properTransfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the actual proper f-vectors as the rank-one carrier.

**Definition 1.11 (The lattice transfer matrix).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.latticeTransfer`

*Formalization.* `D5/S3/Combinatorics/Kozlov/TransferEndpoints.latticeTransfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the natural rank-one lattice vectors as the carrier.

**Theorem 1.12 (The proper count as one matrix entry).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.proper_count_as_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.proper_count_as_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The count at rank r+1 equals the first-to-last entry of the proper transfer matrix to power r+2.

**Theorem 1.13 (The lattice count as one matrix entry).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.lattice_count_as_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.lattice_count_as_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The count at rank r+1 equals the first-to-last entry of the lattice transfer matrix to power r+2.

**Theorem 1.14 (The proper transfer is upper unitriangular).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.properTransfer_unitriangular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.properTransfer_unitriangular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Proper f-vectors are bounded and fixed, and the full skeleton of each positive cutoff is proper. These facts give the triangular vanishing and diagonal identities.

**Theorem 1.15 (The lattice transfer is upper unitriangular).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.latticeTransfer_unitriangular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.latticeTransfer_unitriangular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Rank-one lattice vectors are bounded and fixed and contain the full skeleton of each positive cutoff. Apply the same two entry identities to this carrier.

**Theorem 1.16 (The one-state case).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.firstState_eq_lastState_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferEndpoints.firstState_eq_lastState_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The first index is zero and the last is n-1, which agree exactly when n is one.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.firstState`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.firstState_eq_lastState_iff`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.first_vecMul`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.lastState`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.last_mulVec`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.latticeTransfer`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.latticeTransfer_unitriangular`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.lattice_count_as_entry`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.properTransfer`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.properTransfer_unitriangular`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.proper_count_as_entry`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_below`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_diag`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_first_row`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_last_column`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferEndpoints.transfer_sandwich`
- Dependency: [D5/S3/Combinatorics/Kozlov/LatticeCount](LatticeCount.md)
