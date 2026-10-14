# Three Residual Labels Give the Full Native Cayley Graph

## Abstract

A complete actual supply frame with three residual labels already describes every permutation, including at the final outer parent.

**Theorem 1.1 (The Final Marked Layer Is the Whole Group).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right) = 2 \Rightarrow \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{Layer}\left(\mathrm{ToFinset}\left(\mathrm{Selected}\left(frame\right)\right), \mathrm{CycleOfList}\left(\mathrm{Cons}\left(\mathrm{Terminal}\left(frame\right), \mathrm{Base}\left(frame\right)\right)\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain.native_three_label_frame_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m and k and every complete SupplyFrame(m,k), a base of length two leaves exactly terminal plus those two base labels after deleting the selected labels. Every actual configuration belongs to this independently specified layer. Full nodup and complete-label obligations earn the residual membership equivalence; injectivity of the actual permutation earns the filtered list permutation. The existing three-label circular-order lemma then yields the base circle or its reverse. Neither a candidate scan nor a cardinality comparison supplies coverage.

**Theorem 1.2 (The Last Outer Parent Is the Whole Group).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right) = 3 \Rightarrow \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{Layer}\left(\mathrm{Insert}\left(\mathrm{Terminal}\left(frame\right), \mathrm{ToFinset}\left(\mathrm{Selected}\left(frame\right)\right)\right), \mathrm{CycleOfList}\left(\mathrm{Base}\left(frame\right)\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain.native_three_label_parent_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the last outer supply, delete the terminal as well as the selected labels. If the literal base has length three, its residual bracelet contains every actual permutation. The proof derives the exact remaining-label condition directly from the complete frame and applies the same genuine three-label order argument. This is the independent full parent domain required at the stopping layer of the all-size recursive construction.

**Definition 1.3 (Identity from the Full Marked Layer).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right) = 2 \Rightarrow \mathrm{GraphIso}\left(\mathrm{DomainGraph}\left(\mathrm{Layer}\left(\mathrm{ToFinset}\left(\mathrm{Selected}\left(frame\right)\right), \mathrm{CycleOfList}\left(\mathrm{Cons}\left(\mathrm{Terminal}\left(frame\right), \mathrm{Base}\left(frame\right)\right)\right)\right)\right), \mathrm{MulCayley}\left(\mathrm{NativeGenerators}\left(m\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain.fullDomainIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex map is Subtype.val. Its surjectivity is earned by native_three_label_frame_domain and its injectivity is subtype injectivity. Adjacency is exactly the same native a/b/c Cayley adjacency, so this is a graph isomorphism on actual configurations.

**Definition 1.4 (Identity from the Full Outer Parent).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right) = 3 \Rightarrow \mathrm{GraphIso}\left(\mathrm{DomainGraph}\left(\mathrm{Layer}\left(\mathrm{Insert}\left(\mathrm{Terminal}\left(frame\right), \mathrm{ToFinset}\left(\mathrm{Selected}\left(frame\right)\right)\right), \mathrm{CycleOfList}\left(\mathrm{Base}\left(frame\right)\right)\right)\right), \mathrm{MulCayley}\left(\mathrm{NativeGenerators}\left(m\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain.fullParentDomainIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same identity on configurations is a graph isomorphism from the final three-label parent domain to the full three-generator Cayley graph. Mapping an already constructed parent walk along it preserves that very walk's Hamiltonicity, vertices and edges. These domain theorems do not assume or independently construct the recursive Hamilton cycle.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain.fullDomainIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain.fullParentDomainIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain.native_three_label_frame_domain`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain.native_three_label_parent_domain`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/InsertionLayerPartition](InsertionLayerPartition.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveSupply](NativeRecursiveSupply.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarGrafting](NativeStarGrafting.md)
