# AdaptiveMergeRepair

## Abstract

LegalPair requires distinct a,b in A and a+b outside A union {0}. GoodOrder A w requires w to permute exactly A.toList and every nonempty proper contiguous interval to be nonzero. GoodCompression uses precisely the compressed alphabet (A minus {a,b}) union {a+b}. The source extracts the unique merged occurrence, derives all side membership and disjointness facts from the actual permutation, uses the original SeparatedPrefixReflection.expansion_inventory at t = length(L) to obtain the prescribed adjacent expansion permutation of A, and applies the generic collision theorem. The compressedAlphabet and GoodCompression names transparently use the original compressed and Omega definitions; GoodOrder uses the same original interval condition. The permutation specialization uses the original expansion theorem. No desired ordering, strict cone or separated excursion is assumed in a premise.

**Theorem 1.1 (The obstruction applies to every actual compressed permutation).**

Lean statement: `D5/S3/FiniteGroups/AdaptiveMergeRepair.failed_expansions_force_fork`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/AdaptiveMergeRepair.failed_expansions_force_fork` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

LegalPair requires distinct a,b in A and a+b outside A union {0}. GoodOrder A w requires w to permute exactly A.toList and every nonempty proper contiguous interval to be nonzero. GoodCompression uses precisely the compressed alphabet (A minus {a,b}) union {a+b}. The source extracts the unique merged occurrence, derives all side membership and disjointness facts from the actual permutation, uses the original SeparatedPrefixReflection.expansion_inventory at t = length(L) to obtain the prescribed adjacent expansion permutation of A, and applies the generic collision theorem. The compressedAlphabet and GoodCompression names transparently use the original compressed and Omega definitions; GoodOrder uses the same original interval condition. The permutation specialization uses the original expansion theorem. No desired ordering, strict cone or separated excursion is assumed in a premise.

**Theorem 1.2 (An edge outside the static fork graph lifts every Good compressed order).**

Lean statement: `D5/S3/FiniteGroups/AdaptiveMergeRepair.outside_fork_lifts_every_order`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/AdaptiveMergeRepair.outside_fork_lifts_every_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any legal pair outside ForkEdge and every actual Good compressed order L,(a+b),R, at least one of the actual words L,a,b,R and L,b,a,R is a Good permutation of A. This universal order statement follows by excluding the signed obstruction; it does not assert that ForkEdge edges always fail.

**Theorem 1.3 (Conditional adaptive lifting under the exact smaller-set existence hypothesis).**

Lean statement: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_repair_under_H`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_repair_under_H` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H says only that every legal compression has some actual Good order. If at least one legal pair lies outside ForkEdge, H supplies a compressed order and the local theorem lifts one orientation. AdaptiveLifting retains the legal pair, its actual compressed permutation and an actual expanded Good permutation. There is no Good(A), expandable-order, desired inventory, connectedness or monotone-improvement premise.

**Theorem 1.4 (Adaptive failure confines every legal edge to the fork graph).**

Lean statement: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_failure_forces_fork_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_failure_forces_fork_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly H, failure of AdaptiveLifting implies every legal pair is a ForkEdge. This is a necessary obstruction and not an equivalence: static fork witnesses need not obstruct all compressed orders.

**Theorem 1.5 (The crossing exclusion yields the full conditional repair).**

Lean statement: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_no_singleton_crossing`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_no_singleton_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under H and existence of a legal pair, absence of singleton-region crossings among nonempty proper zero-sum subsets implies adaptive lifting. All three hypotheses are explicit. This theorem composes the collision, proper-subset and graph arguments without strengthening H.

**Theorem 1.6 (Laminarity repairs lifting under H and a legal edge).**

Lean statement: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_laminar`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_laminar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under H and nonempty legal edges, laminarity of the nonempty proper zero-sum family suffices. The laminarity assumption is visible and is not inferred for arbitrary alphabets.

**Theorem 1.7 (The structural classification supplies only legal-pair existence).**

Lean statement: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_laminar_nonsubgroup`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_laminar_nonsubgroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonzero alphabet A of cardinality at least three, assume insert 0 A is not the carrier of an additive subgroup. The original public restricted_pair_sum_classification theorem supplies a legal pair by contraposition. Its translation-action subgroup alternative connects the additive word obstruction to the stabilizer structure of the finite carrier. Under H and laminarity the conditional repair follows. No private finite classification proof is copied. This is the sole actual consumer of that structural supplier in this unit.

**Theorem 1.8 (A common block partition gives the second conditional repair).**

Lean statement: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_partition_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_partition_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under H and nonempty legal edges, assume all nonempty proper zero-sum subsets are unions of a common partition of A into blocks of size at least two. The block-region theorem excludes singleton crossings, hence excludes forks and gives an actual adaptive lift. No block representation is asserted automatically for arbitrary A.

The unrestricted adaptive principle and original arbitrary-subset parent remain OPEN. Under H and existence of a legal pair for an arbitrary finite nonzero alphabet of size at least three, it remains OPEN whether some actual Good compressed order has a Good adjacent expansion; a complete checked counterexample would refute that principle. Static legal-edge inclusion in ForkEdge does not decide it. The published IntegerStrongOrdering theorem is reused in a transient exact-telescope check; no new integer ordering theorem is retained and concrete ZMod Good is not generalized. No literature novelty claim follows from repository search. Four-slot Reg registration is unfinished; see https://github.com/the-omega-institute/trureturing/issues/21061 for exact targets and missing source-binding evidence.

## References

- Truth anchor: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_failure_forces_fork_inclusion`
- Truth anchor: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_laminar`
- Truth anchor: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_laminar_nonsubgroup`
- Truth anchor: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_no_singleton_crossing`
- Truth anchor: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_of_partition_blocks`
- Truth anchor: `D5/S3/FiniteGroups/AdaptiveMergeRepair.adaptive_repair_under_H`
- Truth anchor: `D5/S3/FiniteGroups/AdaptiveMergeRepair.failed_expansions_force_fork`
- Truth anchor: `D5/S3/FiniteGroups/AdaptiveMergeRepair.outside_fork_lifts_every_order`
- Dependency: [D5/S1/Words/Sequenceability/AdaptiveMergeZeroCrossing](../../S1/Words/Sequenceability/AdaptiveMergeZeroCrossing.md)
- Dependency: [D5/S3/FiniteGroups/RestrictedPairSumClassification](RestrictedPairSumClassification.md)
