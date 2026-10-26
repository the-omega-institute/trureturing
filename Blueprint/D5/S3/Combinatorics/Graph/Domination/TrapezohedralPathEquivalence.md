# From actual graph subsets to actual path subsets

## Abstract

The complete labelled-subset count is obtained through inverse ordered-path maps.

Fix n>=3 and the deleted cyclic edge j. The ordered path map is t -> t+(j+1) in Fin n. It sends the first path label to j+1 and the last to j. Every path edge is exactly a remaining cyclic edge, in either orientation. The native Mathlib vertex-cover/complement theorem is reused; minimality is transported by order reversal of inclusion. An endpoint belongs to the cover exactly when the corresponding endpoint is absent from its independent complement.

**Definition 1.1 (Both inverse label maps).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralPathEquivalence.coverPathEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TrapezohedralPathEquivalence.coverPathEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each n>=3, CoverData n is equivalent to Fin n times the subtype of actual finite subsets in restrictedFamily n. Encode selects exactly the natural labels t.val whose ordered cyclic label is outside C. Decode declares i in C exactly when the value of the inverse ordered label is absent from I. The two inverse equations are proved on every cover and every bounded subset; the edge label j is retained. No path-count hypothesis is assumed.

**Theorem 1.2 (Every actual labelled subset is counted once).**

$$\forall (n : \mathbb{N}), \operatorname{actualCount}\left(n\right) = 2 \cdot n \cdot \operatorname{restrictedCount}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TrapezohedralPathEquivalence.actual_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Bool apex tag contributes two, the retained opposite rim label contributes n, and the inverse path correspondence contributes restrictedCount n. The source count is Nat.card of the type of actual vertex subsets satisfying closed domination, minimality among all proper dominating subsets, and induced connectivity. It is defined as zero for n<3, so the equality is for every natural n. Rotations and apex exchange are explicit bijections used for counting labels, not quotients.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralPathEquivalence.actual_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TrapezohedralPathEquivalence.coverPathEquiv`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/PathEndpointCount](PathEndpointCount.md)
- Dependency: [D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover](TrapezohedralTaggedCover.md)
