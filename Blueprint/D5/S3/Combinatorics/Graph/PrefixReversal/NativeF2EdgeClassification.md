# Closed Actual F2 Native Edge Classification

## Abstract

One actual F2 Hamilton cycle consists exactly of all native circle edges outside its complete literal cut set and all literal T/E c seams.

F2NativeEdge is the union of every complete core native circle and every nonzero-gap circle of every remaining contact supplier. F2DeletedEdge is the complete literal T cut set together with the b cut at every gap of every remaining supplier, including gap zero, whose cut opens the actual contact circle. F2Seam consists of every actual T seam and every actual E seam. All three predicates are specified before a walk is selected.

**Theorem 1.1 (The Same Hamilton Witness Has Exactly the Closed Inventory).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\exists base \in \mathrm{Vertices}\left(\mathrm{F2Domain}\left(m\right)\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{domainGraph}\left(\mathrm{F2Domain}\left(m\right)\right), base, base\right),\; \mathrm{IsHamiltonianCycle}\left(w\right) \land \left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{Member}\left(e, \mathrm{RawEdges}\left(w\right)\right) \Leftrightarrow \left(\left(\mathrm{F2NativeEdge}\left(m, e\right) \land \left(\neg \mathrm{F2DeletedEdge}\left(m, e\right)\right)\right) \lor \mathrm{F2Seam}\left(m, e\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeClassification.native_f2_hamiltonian_cycle_with_closed_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least four, one Hamilton cycle w on F2Domain has, for every undirected raw configuration edge e, the exact classification: e occurs in RawEdges(w) if and only if it is a F2NativeEdge outside F2DeletedEdge or a F2Seam. Thus both inclusion and exclusion concern the same actual Hamilton witness, and the recipe contains no chosen walk.

The proof first flattens the earned finite contact recursion. The old core keeps exactly the edges outside all contacts opened so far; the added edges are precisely the uncut new circles and seams indexed by those contacts. Each nonzero new gap is disjoint from the entire old core: the core-star intersection is gap zero, and the supplier gap circles are disjoint. Distinct contact stars are disjoint, giving unique owners for all new native circles.

Endpoint ownership excludes every other circle's native cut from retained circle edges. Actual coordinate values show c differs from both a and b, so none of the literal seams can reintroduce any native cut. These facts remove the successor exclusions from earlier added edges and identify the complete closed native cut set. Substitution into the existing actual F2 edge certificate proves the displayed iff.

**Theorem 1.2 (Every Literal F2 Native Cut Is Absent).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{F2DeletedEdge}\left(m, e\right) \Rightarrow \left(\neg \left(\left(\mathrm{F2NativeEdge}\left(m, e\right) \land \left(\neg \mathrm{F2DeletedEdge}\left(m, e\right)\right)\right) \lor \mathrm{F2Seam}\left(m, e\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeClassification.native_f2_deleted_edge_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every F2DeletedEdge is absent from the complete closed inventory. In particular this includes every T cut, every contact b cut and every nonzero-gap b cut. The c-versus-native generator calculation excludes all seams from the native cut set.

The additional six v-marked cuts, their row-by-row positions, the five literal J2 words as full components and the all-size recursion remain separate obligations. The result here classifies the unmarked actual F2 cycle for every m at least four.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeClassification.native_f2_deleted_edge_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeClassification.native_f2_hamiltonian_cycle_with_closed_inventory`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreEdgeClassification](NativeCoreEdgeClassification.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeInventory](NativeF2EdgeInventory.md)
