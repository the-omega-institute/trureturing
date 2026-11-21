# Counting chains with a finite transfer matrix

## Abstract

A finite set of states and an admissibility test for adjacent elements give a transfer matrix. Its powers count chains of every positive length.

**Definition 1.1 (Numbers of elements by state).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferCount.uG`

*Formalization.* `D5/S3/Combinatorics/Kozlov/TransferCount.uG` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Count the elements of the finite carrier with the specified state.

**Definition 1.2 (Numbers of successive elements by state).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferCount.TG`

*Formalization.* `D5/S3/Combinatorics/Kozlov/TransferCount.TG` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The entry from i to j counts admissible successor elements with state j given the preceding state i.

**Definition 1.3 (Admissible positive-length sequences).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferCount.ChainG`

*Formalization.* `D5/S3/Combinatorics/Kozlov/TransferCount.ChainG` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Each element after the first satisfies the transition condition at the preceding element's state.

**Definition 1.4 (The finite family of chains).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferCount.chainG`

*Formalization.* `D5/S3/Combinatorics/Kozlov/TransferCount.chainG` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Filter the finite family of tuples of carrier elements by the transition test.

**Definition 1.5 (The number of chains ending at a state).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG`

*Formalization.* `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Filter the chain family by the state of its final element and count the survivors.

**Theorem 1.6 (Adding a final element to a chain).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferCount.chainG_snoc_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferCount.chainG_snoc_iff` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Retain all earlier tests and check the new transition from the previous last element.

**Theorem 1.7 (Single-element chains).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG_zero` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A length-one chain whose terminal state is k is exactly a carrier element in state k.

**Theorem 1.8 (The last-step counting recurrence).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG_succ` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Decompose a longer chain into its prefix and final element. Partition prefixes by terminal state and sum their counts times the corresponding successor multiplicities.

**Theorem 1.9 (State-by-state matrix powers).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG_eq` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The recurrence multiplies the previous row vector by the transition matrix. Start with the length-one count and induct on the number of transitions.

**Theorem 1.10 (Count all terminal states).**

Lean statement: `D5/S3/Combinatorics/Kozlov/TransferCount.card_chainG`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/TransferCount.card_chainG` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Partition the chains by their terminal state and sum the matrix row against the all-ones vector.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferCount.ChainG`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferCount.TG`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferCount.card_chainG`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferCount.chainG`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferCount.chainG_snoc_iff`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG_eq`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG_succ`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferCount.chainTopG_zero`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/TransferCount.uG`
