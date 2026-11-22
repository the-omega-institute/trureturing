# The order of maximum Boolean antichains

## Abstract

Maximum Boolean antichains carry the next smaller Tamari order.

**Definition 1.1 (Families of a prescribed cardinality).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.MaximumFamilies`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.MaximumFamilies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An element consists of a set C in a complete lattice, a proof of IsBooleanFamily(C), and the equality of its cardinality with the prescribed n.

**Definition 1.2 (Inclusion of generated lower sets).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.maximumFamiliesOrder`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.maximumFamiliesOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A family is below another when the lower set it generates is included in the other generated lower set. The maximal elements recover the generating antichain.

**Definition 1.3 (The lattice on the rotation order).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.tamariCompleteLattice`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.tamariCompleteLattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport the bracket infimum back along treeBracketOrderIso. Its partial order is the contextual rotation order.

**Definition 1.4 (The next smaller Tamari order).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.maximumTamariOrderIso`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.maximumTamariOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Classify maximum families as laminar interval arrays. Comparing their left endpoints gives the order. Reflecting the arrays gives the dual bracket order, and mirroring the trees reverses it again.

**Theorem 1.5 (The maximum in Tamari rank n + 1).**

$$\forall n \in \mathbb{N},\; \operatorname{IsGreatest}\left(\{k \in \mathbb{N} \mid \exists C \in \operatorname{Set}\left(\operatorname{Trees}\left(n + 1\right)\right),\; \operatorname{IsBooleanFamily}\left(C\right) \land \operatorname{ncard}\left(C\right) = k\}, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.maximumTamari_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the bracket cardinality bound and the attaining family along the tree bracket order isomorphism.

**Theorem 1.6 (Tamari atom bound).**

$$\forall n \in \mathbb{N},\; \operatorname{NatCard}\left(\{x \mid x \in \operatorname{Trees}\left(n + 1\right) \land \operatorname{IsAtom}\left(x\right)\}\right) \le n$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.tamari_atom_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An atom of the bracket order must be a single one-step increase from the identity bracket. In rank n + 1 there are at most n available coordinates.

**Theorem 1.7 (Two distinct Tamari coatoms).**

$$\forall n \in \mathbb{N},\; 2 \le n \Rightarrow (\exists a \in \operatorname{Trees}\left(n + 1\right),\; \exists b \in \operatorname{Trees}\left(n + 1\right),\; \operatorname{IsCoatom}\left(a\right) \land \left(\operatorname{IsCoatom}\left(b\right) \land a \ne b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.tamari_two_coatoms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At n ≥ 2 the bracket coatoms from two different right endpoints transport to distinct coatoms in Trees(n + 1).

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.MaximumFamilies`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.maximumFamiliesOrder`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.maximumTamariOrderIso`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.maximumTamari_card`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.tamariCompleteLattice`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.tamari_atom_card_le`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.tamari_two_coatoms`
- Dependency: [D5/S3/Combinatorics/Lattices/Tamari/BooleanRows](BooleanRows.md)
- Dependency: [D5/S3/Combinatorics/Lattices/Tamari/TreeRotations](TreeRotations.md)
- Dependency: [D5/S3/Combinatorics/PriorityLattice/ForestCovers](../../PriorityLattice/ForestCovers.md)
