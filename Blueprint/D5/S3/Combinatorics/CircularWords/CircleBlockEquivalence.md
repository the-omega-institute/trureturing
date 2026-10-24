# Actual circular run contraction

## Abstract

Actual circular run contraction

**Theorem 1.1 (Actual circular run contraction).**

$$\forall alpha \in \mathrm{Type},\; \forall A \in \mathrm{Finset}\left(alpha\right),\; \forall S \in \mathrm{Finset}\left(alpha\right),\; \forall a \in alpha,\; \forall z \in \mathrm{BlockDomain}\left(A, S, a\right),\; ((S \subseteq A) \land ((\mathrm{Nonempty}\left(S\right)) \land ((\mathrm{Nonempty}\left(\mathrm{sdiff}\left(A, S\right)\right)) \land (a \in S)))) \Rightarrow (\mathrm{value}\left(\mathrm{blockEquiv}\left(A, S, a, z\right)\right) = \mathrm{inflate}\left(a, \mathrm{first}\left(z\right), \mathrm{value}\left(\mathrm{second}\left(z\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/CircleBlockEquivalence.blockEquiv_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier has decidable equality. BlockDomain(A,S,a) is the product of orders(S) and circles(insert(a,sdiff(A,S))). First and second are its actual ordered-run and circle components. Proof arguments of blockEquiv are suppressed in this presentation.

Keep one original label of a nonempty proper run as its marker. Cutting at the unique incoming boundary records its internal order and the complementary order. Anchoring the contracted circle at the marker gives the inverse map. Expansion replaces that marker by the entire recorded run in its original orientation.

Restriction deletes the other labels of this run. It recovers the contracted circle, and expansion preserves and reflects every prescribed arc disjoint from the contracted run. This is the common-circle interface used by the simultaneous contraction, rather than separate cuts chosen for different events.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/CircleBlockEquivalence.blockEquiv_expand`
- Dependency: [D5/S3/Combinatorics/CircularWords/CircularOrderCount](CircularOrderCount.md)
- Dependency: [D5/S3/Combinatorics/CircularWords/CyclicInsertionGap](CyclicInsertionGap.md)
