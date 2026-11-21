# Position-first lex segments and shadow nesting

## Abstract

Position-first compression fills earlier components before later ones. Its upper shadow has the same position-first shape at the next degree.

**Definition 1.1 (The shape of a left-filled allocation).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.GreedyShape`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexPositionShadow.GreedyShape` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

After a component has less than its capacity, every later component has size zero.

**Lemma 1.2 (The greedy allocation is left-filled).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.greedyShape_greedy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.greedyShape_greedy` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

If the first component is underfull the residual is zero. Otherwise recurse on that residual.

**Lemma 1.3 (A left-filled allocation is determined by its total).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.eq_greedy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.eq_greedy` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

At each position its size is the lesser of the remaining total and that component's capacity.

**Lemma 1.4 (Greedy allocations grow componentwise).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.greedy_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.greedy_mono` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Both the head allocation and its residual are monotone in the requested total. Induct on the list.

**Definition 1.5 (Capacity of a component suffix).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.tailCap`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexPositionShadow.tailCap` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Discard the prescribed number of initial components and sum the remaining capacities.

**Lemma 1.6 (The full capacity).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.tailCap_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.tailCap_zero` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Discarding zero components leaves the entire capacity sum.

**Lemma 1.7 (The empty component costs zero).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.costZ_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.costZ_zero` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Its shadow has size zero in either degree case.

**Lemma 1.8 (A shadow fits in the next layer).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.sig_le_choose_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.sig_le_choose_succ` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the recursive count and compare with the full layer.

**Lemma 1.9 (Capacity at the successor degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.capZ_succ_of_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.capZ_succ_of_nonneg` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

For a nonnegative degree the successor capacity is the corresponding successor binomial coefficient.

**Lemma 1.10 (The shadow fits in the successor capacity).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.costZ_le_capZ_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.costZ_le_capZ_succ` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the shadow bound for nonnegative degrees and the empty component otherwise.

**Lemma 1.11 (A full nonnegative component has full shadow).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.costZ_capZ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.costZ_capZ` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Apply the full-layer identity to the integer degree.

**Lemma 1.12 (A positive total cost has a positive component).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.cost_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.cost_pos` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The summed nonnegative costs are positive only when a component contributes.

**Lemma 1.13 (Shadow sizes are still left-filled).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.greedyShape_shadow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.greedyShape_shadow` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A full nonnegative component shadows to full capacity. The ordered degrees and zero-cost tails preserve the greedy shape, including negative and terminal degrees.

**Definition 1.14 (Position-first segments of a specified mass).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.IsLexFSeg`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexPositionShadow.IsLexFSeg` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use lex-initial components with the sizes obtained by greedy allocation for the degree list and total.

**Theorem 1.15 (Existence of position-first segments).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.exists_isLexFSeg`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.exists_isLexFSeg` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Realize each greedy size by an initial segment in that degree.

**Lemma 1.16 (Total cardinality of a position-first segment).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.card_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.card_sum` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Its allocated sizes sum to the minimum of its requested mass and the full capacity.

**Lemma 1.17 (Read the segment at its attained mass).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.resize`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.resize` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The same greedy sizes are recovered when the requested mass is replaced by their total.

**Lemma 1.18 (Initial segments are nested by size).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexInit_subset_of_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexInit_subset_of_card_le` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

If a face of the smaller initial segment were missing from the larger one, initiality forces the reverse inclusion and a cardinality contradiction.

**Lemma 1.19 (Compare the components of two lex lists).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.forall2_subset_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.forall2_subset_of_le` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Match components at equal degrees and apply nesting to each cardinality comparison.

**Theorem 1.20 (Position-first nesting).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.forall2_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.forall2_subset` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Greedy monotonicity supplies the componentwise inequalities and initiality supplies inclusion.

**Definition 1.21 (Position-first initial families).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.IsLexFInitial`

*Formalization.* `D5/S3/Combinatorics/Kozlov/LexPositionShadow.IsLexFInitial` (`✓ std3`).

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Each component is lex-initial and a nonempty later component forces all earlier components to be full.

**Lemma 1.22 (Peel off the first component).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexFInitial_cons_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexFInitial_cons_iff` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The head is initial, the tail is position-first initial, and a nonempty tail requires a full head.

**Lemma 1.23 (Nonempty components and list indexing).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.exists_getD_nonempty_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.exists_getD_nonempty_iff` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

A nonempty indexed component belongs to an actual list position and conversely.

**Lemma 1.24 (A component attains capacity exactly when full).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.full_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.full_iff` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Apply uniform-layer inclusion and finite cardinality. Negative degrees have only the empty component.

**Lemma 1.25 (Position-first initiality as a cardinal allocation rule).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexFInitial_iff_shape`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexFInitial_iff_shape` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Use the initiality criterion at the head to equate fullness with capacity and recurse along the list.

**Theorem 1.26 (Characterize position-first segments by their total).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexFInitial_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexFInitial_iff` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Identify a left-filled size list with the greedy allocation at its actual total.

**Lemma 1.27 (Move one initial component to the successor degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.component_lexInit_upShadow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.component_lexInit_upShadow` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

The shadow of a nonnegative lex segment has the specified size and is initial. The empty negative component also remains admissible.

**Lemma 1.28 (Size of a shadow component).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.shadow_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.shadow_card` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Apply the recursive shadow cardinality to each component of the position-first segment.

**Lemma 1.29 (Total upper-shadow size).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.shadow_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.shadow_sum` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Sum the component cardinalities to read the total as the greedy shadow cost.

**Theorem 1.30 (The position-first shadow).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.lem_lexF_shadow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.lem_lexF_shadow` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

Combine component initiality with the left-filled shape of the shadow sizes.

**Theorem 1.31 (Shadow nesting in the next degree).**

Lean statement: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.lem_lexF_shadow_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Kozlov/LexPositionShadow.lem_lexF_shadow_subset` (`✓ std3`). ∎

*Citation.* Jan Snellman (2026). *Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope*. DOI: [10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110). URL: <https://arxiv.org/pdf/2611.26110v1#page=52>.

*Commentary.*

If the shadow's mass is bounded by the next segment size, compare the position-first allocations and use nesting componentwise.

## References

- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.GreedyShape`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.IsLexFInitial`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.IsLexFSeg`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.capZ_succ_of_nonneg`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.card_sum`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.component_lexInit_upShadow`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.costZ_capZ`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.costZ_le_capZ_succ`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.costZ_zero`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.cost_pos`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.eq_greedy`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.exists_getD_nonempty_iff`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.exists_isLexFSeg`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.forall2_subset`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.forall2_subset_of_le`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.full_iff`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.greedyShape_greedy`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.greedyShape_shadow`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.greedy_mono`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexFInitial_cons_iff`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexFInitial_iff`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexFInitial_iff_shape`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.isLexInit_subset_of_card_le`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.lem_lexF_shadow`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.lem_lexF_shadow_subset`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.resize`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.shadow_card`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.shadow_sum`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.sig_le_choose_succ`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.tailCap`
- Truth anchor: `D5/S3/Combinatorics/Kozlov/LexPositionShadow.tailCap_zero`
- Dependency: [D5/S3/Combinatorics/Kozlov/LexFamilyShadow](LexFamilyShadow.md)
