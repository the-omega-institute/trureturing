# Counting distinct proper sums by their unique chained representatives

## Abstract

For bounded vectors the last member of a chained tuple is recovered by clipping the sum at the coordinate capacities. This gives uniqueness and turns the transfer count into a count of distinct sums.

**Definition 1.1 (Coordinate capacities).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.cap`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ChainedCount.cap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The full layer at a face size has the corresponding binomial coefficient as capacity.

**Theorem 1.2 (Capacities are positive throughout the coordinate space).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.cap_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.cap_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Each index lies at or below n, where the binomial coefficient is positive.

**Definition 1.3 (The singleton coordinate).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.firstDegree`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ChainedCount.firstDegree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

When n is positive the degree-one coordinate belongs to Fin of size n+1.

**Definition 1.4 (Vectors bounded by the full layers).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.Bounded`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ChainedCount.Bounded` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Every coordinate is at most the corresponding capacity.

**Definition 1.5 (The first two coordinates are full).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.Fixed`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ChainedCount.Fixed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the full capacities in degrees zero and one.

**Definition 1.6 (The f-vector of a full skeleton).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.skeleton`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ChainedCount.skeleton` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Fill all coordinates through the given cutoff and put zero above it.

**Theorem 1.7 (Positive skeletons are proper f-vectors).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.skeleton_mem_SnF`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.skeleton_mem_SnF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Realize the vector by the downset of all subsets up to the given size. A positive cutoff includes every singleton.

**Theorem 1.8 (Proper f-vectors are capacity bounded).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.SnF_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.SnF_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Every layer lies inside the family of all subsets of that size.

**Theorem 1.9 (Proper f-vectors are full in degrees zero and one).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.SnF_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.SnF_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the absence of missing faces in those two degrees.

**Theorem 1.10 (Positive coordinates are bounded above by the top).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.le_top_of_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.le_top_of_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A positive coordinate belongs to the nonempty finite support over which the top is the maximum.

**Theorem 1.11 (Coordinates above the top vanish).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.vanish_of_top_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.vanish_of_top_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Positive occupancy would contradict the maximum's bound.

**Theorem 1.12 (A deficiency bounds the first missing degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.indeg_le_of_lt_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.indeg_le_of_lt_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The deficient coordinate belongs to the set whose minimum defines the first missing degree.

**Theorem 1.13 (Earlier bounded coordinates are full).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.full_below_indeg`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.full_below_indeg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A below-capacity coordinate would force the minimum to be no higher than that coordinate.

**Theorem 1.14 (Fullness through a degree characterizes the first deficit).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.lt_indeg_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.lt_indeg_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Read the minimum of the deficient degrees or use the sentinel when that set is empty.

**Theorem 1.15 (The cutoff is the top of a full skeleton).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.top_skeleton`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.top_skeleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The cutoff is occupied by positivity of the binomial capacity and every later degree is zero.

**Theorem 1.16 (Unique representation by bounded chained tuples).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.chained_sum_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.chained_sum_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

At each coordinate the final summand is the lesser of the total and the capacity. A deficit in that summand forces all previous summands to vanish in that coordinate. Peel off the last summand and induct on tuple length.

**Definition 1.17 (State indexed by the top degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.topState`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ChainedCount.topState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Represent top degrees one through n by states zero through n-1.

**Theorem 1.18 (Recover the top from its state).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.topState_val`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.topState_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The singleton and upper bound on occupied degrees place the top in one through n. The state index is shifted down by one.

**Definition 1.19 (Chaining as a transition condition).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.cond`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ChainedCount.cond` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A candidate successor has first missing degree strictly greater than the top degree of the preceding state.

**Theorem 1.20 (Transition chains and chained tuples).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.chainG_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.chainG_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

For fixed vectors the top-state index recovers the top degree, so the adjacent tests coincide.

**Definition 1.21 (The finite set of actual proper f-vectors).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.properVectors`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ChainedCount.properVectors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Enumerate the images of finite downsets satisfying properness.

**Theorem 1.22 (The finite carrier realizes the literal vector set).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.mem_properVectors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.mem_properVectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The finset image has precisely the f-vectors of the proper families.

**Definition 1.23 (The transfer on f-vector top states).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.transfer`

*Formalization.* `D5/S3/Combinatorics/Kozlov/ChainedCount.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Count successor vectors by the state and first-missing-degree transition condition.

**Theorem 1.24 (Cardinality of an image of chained tuples).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.card_of_chained_image`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.card_of_chained_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Identify the admissible tuples with finite transfer chains and apply injectivity of the coordinate sum on that domain.

**Theorem 1.25 (The literal proper-sum count by transfer).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.proper_count_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.proper_count_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The chained subset has the full proper sumset as image by unconditional surjectivity. Its boundedness and fixed coordinates allow the chain cardinality formula.

**Theorem 1.26 (The top-degree face forces a full simplex).**

Lean statement: `D5/S3/Combinatorics/Kozlov/ChainedCount.SnF_terminal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/ChainedCount.SnF_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

On an n-element ground set a face of size n is the whole ground set. Downward closure makes every subset a face.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.Bounded`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.Fixed`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.SnF_bounded`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.SnF_fixed`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.SnF_terminal`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.cap`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.cap_pos`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.card_of_chained_image`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.chainG_iff`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.chained_sum_injective`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.cond`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.firstDegree`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.full_below_indeg`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.indeg_le_of_lt_cap`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.le_top_of_pos`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.lt_indeg_iff`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.mem_properVectors`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.properVectors`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.proper_count_transfer`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.skeleton`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.skeleton_mem_SnF`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.topState`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.topState_val`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.top_skeleton`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.transfer`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/ChainedCount.vanish_of_top_lt`
- Dependency: [D5/S3/Combinatorics/Kozlov/ProperSumset](ProperSumset.md)
- Dependency: [D5/S3/Combinatorics/Kozlov/TransferCount](TransferCount.md)
