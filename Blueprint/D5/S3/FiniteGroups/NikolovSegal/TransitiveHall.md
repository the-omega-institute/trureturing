# Hall interval selection on actual permutation cycles

## Abstract

Degree counts, actual periodic orbits and simultaneous Hall choices give consecutive good generator intervals.

**Theorem 1.1 (finite degree matching).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_degree_matching`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_degree_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite sets W and M, a positive q and neighbor sets t(w), assume every m belongs to at most q neighbor sets and every t(w) has at least q members. There is an injective choice f from W to M with f(w) in t(w). Counting incidence fibers establishes the Hall inequalities.

**Theorem 1.2 (finite cycle incidence matching).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_cycle_incidence_matching`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_cycle_incidence_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite cycle-incidence assumptions give an injective choice of a generator and cycle for every representative. Cycle sizes at most q bound one incidence degree; sufficiently many good generators supply the other degree. The conclusion keeps membership and the actual cycle label.

**Definition 1.3 (ConsecutiveInterval).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.ConsecutiveInterval`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.ConsecutiveInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A subset X of Fin m is consecutive when every index between two members also belongs to X. No commutativity of the group products is assumed.

**Theorem 1.4 (consecutive block family).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.consecutive_block_family`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.consecutive_block_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive q, D and M with M times D times (q plus D) at most m, construct M times D pairwise disjoint consecutive blocks, each with q plus D indices, in increasing generator order.

**Definition 1.5 (fixedChoice).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.fixedChoice`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.fixedChoice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a representative and a generator block, fixedChoice retains the indices declared good at that representative.

**Definition 1.6 (badChoice).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.badChoice`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.badChoice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a representative and a generator block, badChoice retains the complementary indices, where good fails.

**Definition 1.7 (prefixPiece).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.prefixPiece`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.prefixPiece` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected prefix piece is the consecutive portion determined by a good block and the bad-index prefix count. Its defining filters retain both generator membership and the required prefix condition.

**Theorem 1.8 (finite cover pigeonhole).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_cover_pigeonhole`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_cover_pigeonhole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a finite set has at least M times D members and is covered by D subsets, with M and D positive, one covering subset has at least M members. The count is made on the common finite set.

**Theorem 1.9 (lemma10 3 repeated matching).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_repeated_matching`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_repeated_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the explicit cycle, good-incidence and disjoint-block hypotheses, repeated Hall choices select the required number of generator-cycle pairs for every representative while retaining their independence across representatives.

**Theorem 1.10 (lemma10 3 interval selection).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the supplied disjoint consecutive blocks and cycle-incidence bounds, select a prefix piece and M good indices at every representative. The selected piece is consecutive, and simultaneous choices preserve independence of the selected generator-cycle pairs.

**Theorem 1.11 (lemma10 3 interval selection from bound).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection_from_bound`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection_from_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerical length bound and positive q, D and M provide the block family used by interval selection. All cycle and bad-choice hypotheses remain explicit; the conclusion retains M selected indices, the fixed interval and simultaneous cycle independence.

**Theorem 1.12 (lemma10 3 interval selection actual).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection_actual`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the actual periodic orbits of the permutations rather than abstract cycle sets. Positive q and good q-periodicity supply the minimal-period and cycle-cardinality laws. The bound of fewer than D bad indices at each injectively chosen representative and the length bound produce M good indices in a consecutive fixed prefix piece, with distinct actual cycles whenever selected pairs share a generator.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Lemma 10.3 and equations (45)-(50), printed pages 228-231. The scalar PRODUCT premise is the input of Part II, Theorem 1.2, equivalent to Part I, Theorem 1.10; Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. These are adaptations and proofs of conditional consequences of published mathematics, with no originality claim. Uniform scalar existence, genuine type-II reconstruction, mixed representative bounds, uniform width, restricted Burnside bounds and unconditional strong completeness remain unproved.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.ConsecutiveInterval`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.badChoice`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.consecutive_block_family`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_cover_pigeonhole`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_cycle_incidence_matching`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.finite_degree_matching`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.fixedChoice`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection_actual`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_interval_selection_from_bound`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.lemma10_3_repeated_matching`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TransitiveHall.prefixPiece`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TransitiveCoverage](TransitiveCoverage.md)
