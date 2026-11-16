# Recursive Page-Table Walk

## Abstract

A self-mapped page-table root supports ordinary lookup, leaf introspection, and finite root closure.

**Theorem 1.1 (Recursive page-table walk).**

$$\operatorname{lookup}\left(root, self\right) = root \Rightarrow \left(\operatorname{lookup}\left(root, i\right) = leaf \Rightarrow \left(\operatorname{lookup}\left(leaf, j\right) = data \Rightarrow \left(\operatorname{Walk}\left(lookup, root, \operatorname{list}\left(i, j\right)\right) = data \land \left(\operatorname{Walk}\left(lookup, root, \operatorname{list}\left(self, i\right)\right) = leaf \land \forall L, \operatorname{Walk}\left(lookup, root, \operatorname{replicate}\left(L, self\right)\right) = root\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/RecursivePageTable.recursive_page_table_walk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lookup map consumes one index per dereference. The first two equalities follow by unfolding two steps: a root entry selects the leaf and the leaf entry selects the data, while the self-map slot sends the root back to itself.

Induction on the number of repeated self-map indices proves the final equality, so every finite all-zero walk remains at the root.

## References

- Truth anchor: `D5/S0/Diagonal/RecursivePageTable.recursive_page_table_walk`
