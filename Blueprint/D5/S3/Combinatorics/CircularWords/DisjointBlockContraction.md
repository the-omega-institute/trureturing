# Original-label circular run contraction

## Abstract

Original-label circular run contraction

The carrier has decidable equality. The primed lists are separate original internal orders; coeCycle identifies rotation only, and Perm compares with the displayed finite set list.

Let A be a finite set of distinct original labels and S a nonempty proper subset. An arc is an oriented circle represented by an ordering of S followed by an ordering of its complement. Rotation preserves orientation; reversal is not identified.

**Theorem 1.1 (A proper circular run has a unique incoming boundary).**

$$\forall alpha \in \mathrm{Type},\; \forall A \in \mathrm{Finset}\left(alpha\right),\; \forall S \in \mathrm{Finset}\left(alpha\right),\; \forall u \in \mathrm{List}\left(alpha\right),\; \forall v \in \mathrm{List}\left(alpha\right),\; \forall uprime \in \mathrm{List}\left(alpha\right),\; \forall vprime \in \mathrm{List}\left(alpha\right),\; ((S \subseteq A) \land ((\mathrm{Nonempty}\left(S\right)) \land ((\mathrm{Nonempty}\left(\mathrm{sdiff}\left(A, S\right)\right)) \land ((\mathrm{Perm}\left(u, \mathrm{toList}\left(S\right)\right)) \land ((\mathrm{Perm}\left(v, \mathrm{toList}\left(\mathrm{sdiff}\left(A, S\right)\right)\right)) \land ((\mathrm{Perm}\left(uprime, \mathrm{toList}\left(S\right)\right)) \land ((\mathrm{Perm}\left(vprime, \mathrm{toList}\left(\mathrm{sdiff}\left(A, S\right)\right)\right)) \land (\mathrm{coeCycle}\left(\mathrm{append}\left(u, v\right)\right) = \mathrm{coeCycle}\left(\mathrm{append}\left(uprime, vprime\right)\right))))))))) \Rightarrow ((u = uprime) \land (v = vprime))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/DisjointBlockContraction.two_block_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two such representatives of the same circle are equal. The first label of each lies in S and the last lies outside S. A nonzero rotation starting in the complement has the wrong first label; one starting strictly inside the S run has the wrong last label. Hence the incoming boundary fixes the representative. The resulting twoBlockEquiv gives mutually inverse actual two-block expansion and boundary cutting, and arc_card counts S.card! times (A minus S).card! circles.

Expansion also replaces every marker in one common marker circle by its full original-label run. Restricting expanded labels commutes with expansion; the retained original marker and the recorded internal order give the contraction interface. The simultaneous pair intersection formula and the quantitative Good-order estimate use this expansion on the same oriented circle.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/DisjointBlockContraction.two_block_injective`
- Dependency: [D5/S3/Combinatorics/CircularWords/CircularDeletionTransport](CircularDeletionTransport.md)
