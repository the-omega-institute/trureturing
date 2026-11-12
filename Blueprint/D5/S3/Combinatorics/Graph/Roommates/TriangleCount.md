# Exact exclusive-triangle profile removal

## Abstract

Exact exclusive-triangle profile removal

**Definition 1.1 (Interval reflection).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.reflectWord`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.reflectWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reflection reverses the three interval positions and negates every signed offset. The certificate transport retains all integer-target injectivity constraints, including exterior targets, reciprocity and nonblocking. Zero remains single with rank four.

**Definition 1.2 (Sixteen ranking words).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.forbiddenWord`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.forbiddenWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index is one orientation bit and three independent Boolean choices. In the forward orientation, positions zero, one and two respectively prefer signed offsets (1,2), (1,-1) and (-2,-1), in that order, to both exterior offsets. Each Boolean chooses the order of the bottom two offsets. Reflection gives the other orientation. The sixteen ranking words are distinct.

**Theorem 1.3 (Every listed profile is impossible).**

$$\forall (s:\operatorname{TriangleIndex}\left(\right)), \neg \exists (d:\operatorname{Assignments}\left(\right)), \operatorname{Certificate}\left(\operatorname{forbiddenWord}\left(s\right), d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.forbidden_not_certified` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

TriangleIndex abbreviates Bool times (Fin 3 to Bool), and Assignments abbreviates Fin 3 to the integers. The forward case directly applies the saved exclusive_triangle_not_certified theorem. The reverse case transports a hypothetical certificate through reflection and applies the same theorem. No matching witness is enumerated; exterior partners and singles remain allowed.

**Definition 1.4 (Removed profiles).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.forbiddenProfiles`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.forbiddenProfiles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set is the image of forbiddenWord over its complete sixteen-element index type.

**Theorem 1.5 (Exact removal cardinality).**

$$\operatorname{card}\left(\operatorname{forbiddenProfiles}\left(\right)\right) = 16$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.forbidden_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rank of offset 1 at the middle position recovers the orientation: it is zero forward and one after reflection. After undoing reflection, ranks at coordinates 2, 1 and 0 of positions 0, 1 and 2 respectively recover the three exterior-order bits. This word-level injection proves that precisely sixteen ranking profiles are removed, without enumerating all pairs of profiles.

**Theorem 1.6 (Three-site count bound).**

$$\operatorname{count}\left(3\right) \le 13808$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.count_three_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map sends each existentially certified word to its underlying ranking word in the complement of the sixteen forbidden profiles. It is injective on words. The whole space has 24 cubed = 13824 elements; complement cardinality gives 13824 minus 16 = 13808. This bind-only numeric reduction is consumed by GrowthTransfer.result to obtain strict exponential growth below 24. It has no standalone first-freeze or external-problem credit. Supplier model credit remains The Formal Conjectures Authors under Apache-2.0; this module imports the saved certificate development without changing the supplier model.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.count_three_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.forbiddenProfiles`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.forbiddenWord`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.forbidden_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.forbidden_not_certified`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/TriangleCount.reflectWord`
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/OpenCertificates](OpenCertificates.md)
