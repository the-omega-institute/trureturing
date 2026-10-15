# Complete Actual F2 Edge Inventory

## Abstract

One actual Hamilton cycle on the complete F2 supplier union has exactly the arbitrary-edge inventory prescribed by its literal finite contact surgeries.

PartialEdge(m,0,e) is CoreUncut(m,e) or TSeam(m,e), using the complete actual two-star core inventory. At contact k<m-2, PartialEdge keeps the preceding edges except the literal edge from contactAnchor(k) to contactAnchor(k)b, adds the uncut native circle edges of every new gap, and adds the actual E c seams. The recipe is defined from the concrete suppliers and their original cuts, before choosing any walk.

**Theorem 1.1 (The Same Complete F2 Cycle Has Exactly the Prescribed Raw Edges).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\exists base \in \mathrm{Vertices}\left(\mathrm{F2Domain}\left(m\right)\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{domainGraph}\left(\mathrm{F2Domain}\left(m\right)\right), base, base\right),\; \mathrm{IsHamiltonianCycle}\left(w\right) \land \left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{Member}\left(e, \mathrm{RawEdges}\left(w\right)\right) \Leftrightarrow \mathrm{PartialEdge}\left(m, \mathrm{NatSub}\left(m, 2\right), e\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeInventory.native_f2_hamiltonian_cycle_with_edge_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least four, there is one actual Hamilton cycle w on F2Domain(m) such that, for every undirected edge e of actual configurations, e occurs in the subtype-forgetting image of w.edges exactly when PartialEdge(m,m-2,e) holds. Hamiltonicity and both directions of the edge classification concern the same witness; the inventory does not describe a separately chosen cycle or merely prove selected edges are retained.

The finite induction starts from the existing complete core certificate. Its retention law and the concrete exclusion of every future contact edge from CoreDeletedEdge earn the actual pending-edge invariant. Pairwise disjoint complete contact stars ensure that opening the next edge preserves every later contact along this same cycle.

At each step the generic actual one-contact graft theorem classifies every raw edge of its Hamilton witness as exactly an old uncut edge, a new uncut native circle edge, or an E seam. Substituting the preceding induction certificate proves the independent PartialEdge successor recipe in both directions. The actual graft domain is PartialDomain(m,k+1); its equality transports Hamiltonicity, pending edges and the whole raw-edge iff together. After m-2 steps the domain is F2Domain(m).

This complete recursive edge recipe supports subsequent deletion classification. A simplified closed table for the marked J2 paths, the proofs that their displayed words are whole components, and all-size recursive Hamiltonicity remain separate mathematical obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeInventory.native_f2_hamiltonian_cycle_with_edge_inventory`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeContactIteration](NativeContactIteration.md)
