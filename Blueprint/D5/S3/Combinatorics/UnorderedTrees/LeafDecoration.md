# Reconstructing a rooted tree from its leaf fibres

## Abstract

Internal subtrees with matching original leaf fibres determine an actual rooted isomorphism.

**Theorem 1.1 (Restriction and extension of rooted isomorphisms).**

$$\operatorname{Nonempty}\left(\operatorname{Iso}\left(T, S\right)\right) \iff \exists e: \operatorname{Iso}\left(\operatorname{P}\left(T\right), \operatorname{P}\left(S\right)\right), \forall p \in \operatorname{P}\left(T\right), \lvert \operatorname{L}\left(T, p\right)\rvert = \lvert \operatorname{L}\left(S, \operatorname{e}\left(p\right)\right)\rvert$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.iso_iff_fibres` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T and S be finite rooted parent trees with internal roots. The pruned tree P retains the actual internal vertices. The fibre L(T,p) comprises the original leaf children of the internal vertex p.

An actual isomorphism preserves child edges and the internal predicate. It therefore restricts to an isomorphism of the pruned trees and to a bijection on each leaf fibre. Conversely, every original vertex is either internal or a leaf over its unique internal parent. Combining the given isomorphism with the chosen bijections of the finite fibres preserves each parent edge and the root.

Inflation attaches the desired number of fresh leaves at each skeleton vertex. Positive multiplicities at the skeleton tips make every skeleton vertex internal after inflation. Pruning then recovers the skeleton and the fibre sizes are the prescribed multiplicities.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.iso_iff_fibres`
- Dependency: [D5/S3/Combinatorics/UnorderedTrees/OneFork](OneFork.md)
