# Simultaneous opposite-pair block intersections

## Abstract

Simultaneous opposite-pair block intersections

**Theorem 1.1 (Simultaneous opposite-pair block intersections).**

$$\forall alpha \in \mathrm{Type},\; \forall A \in \mathrm{Finset}\left(alpha\right),\; \forall F \in \mathrm{Finset}\left(\mathrm{Finset}\left(alpha\right)\right),\; ((\mathrm{DisjointPairFamily}\left(A, F\right)) \land (2 \cdot \mathrm{card}\left(F\right) < \mathrm{card}\left(A\right))) \Rightarrow (\mathrm{card}\left(\mathrm{JointInventory}\left(A, F\right)\right) = 2^{\mathrm{card}\left(F\right)} \cdot \mathrm{factorial}\left(\mathrm{card}\left(A\right) - \mathrm{card}\left(F\right) - 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/SimultaneousPairContraction.joint_pair_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier has decidable equality. DisjointPairFamily(A,F) means that every member of F is a two-element subset of A and distinct members are disjoint. JointInventory(A,F) consists of actual cycles satisfying Joint A F.

A joint event consists of actual oriented circles realizing every prescribed disjoint run. The jointStepEquiv contracts one run while preserving every remaining event on that same circle. Its two inverse maps use the recorded original internal order and actual marker expansion.

Iterating this equivalence for p disjoint two-label blocks gives 2^p times (n-p-1)! circles when 2p<n. The paired quantitative consumer uses p=0,1,2,3 with n=2r and r at least twelve. Distinct original labels and the free rotation fibers supply the normalization; event independence is neither assumed nor asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/SimultaneousPairContraction.joint_pair_card`
- Dependency: [D5/S3/Combinatorics/CircularWords/CircleBlockEquivalence](CircleBlockEquivalence.md)
