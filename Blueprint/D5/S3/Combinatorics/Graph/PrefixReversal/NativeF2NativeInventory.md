# Actual Native F2 Edge Inventory

## Abstract

The independent native-circle catalog is exactly the actual F2 a/b edge set, and one actual Hamilton cycle retains precisely its uncut edges.

**Theorem 1.1 (Catalog Equals Actual Native Edges on the Full F2 Domain).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{F2NativeEdge}\left(m, e\right) \Leftrightarrow \left(\exists x \in \mathrm{Configuration}\left(m\right),\; \exists g \in \mathrm{Configuration}\left(m\right),\; \mathrm{F2Domain}\left(m, x\right) \land \left(\left(g = \mathrm{a}\left(m\right) \lor g = \mathrm{b}\left(m\right)\right) \land e = \mathrm{Sym2Pair}\left(x, \mathrm{Mul}\left(x, g\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2NativeInventory.native_f2_native_edge_catalog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four and every raw undirected edge e, F2NativeEdge(m,e) holds exactly when e is the a or b edge at an actual F2Domain vertex. Forward membership uses the actual core and supplier domains of each cataloged circle. Reverse membership uses the earned complete core circle partition or the earned complete supplier gap-circle partition. Gap zero of a remaining supplier lies in the core by the exact contact intersection; every other gap is already in the new catalog.

**Theorem 1.2 (One Hamilton Cycle Retains Exactly the Uncut Actual Native Edges).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\exists base \in \mathrm{Vertices}\left(\mathrm{F2Domain}\left(m\right)\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{domainGraph}\left(\mathrm{F2Domain}\left(m\right)\right), base, base\right),\; \mathrm{IsHamiltonianCycle}\left(w\right) \land \left(\left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{Member}\left(e, \mathrm{RawEdges}\left(w\right)\right) \Leftrightarrow \left(\left(\mathrm{F2NativeEdge}\left(m, e\right) \land \left(\neg \mathrm{F2DeletedEdge}\left(m, e\right)\right)\right) \lor \mathrm{F2Seam}\left(m, e\right)\right)\right) \land \left(\forall x \in \mathrm{Configuration}\left(m\right),\; \forall g \in \mathrm{Configuration}\left(m\right),\; \mathrm{F2Domain}\left(m, x\right) \Rightarrow \left(\left(g = \mathrm{a}\left(m\right) \lor g = \mathrm{b}\left(m\right)\right) \Rightarrow \left(\mathrm{Member}\left(\mathrm{Sym2Pair}\left(x, \mathrm{Mul}\left(x, g\right)\right), \mathrm{RawEdges}\left(w\right)\right) \Leftrightarrow \left(\neg \mathrm{F2DeletedEdge}\left(m, \mathrm{Sym2Pair}\left(x, \mathrm{Mul}\left(x, g\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2NativeInventory.native_f2_hamiltonian_cycle_with_native_edge_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, one actual Hamilton cycle w on F2Domain has the following exact law simultaneously for every actual vertex x in that domain and both native generators g=a,b: its raw edge from x to xg belongs to w precisely when it is outside F2DeletedEdge. The actual coordinate distinction c≠a,b excludes every T/E seam from these native edges. Combining that fact and the exact native catalog bridge with the complete closed inventory eliminates the seam alternative. The certificate also retains the full raw-edge iff, so native retention, every actual seam and Hamiltonicity concern the same witness.

This exact native edge criterion supports subsequent literal-word legality. It does not yet locate the additional six v-marked cuts or prove the five J2 words are complete components; those remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2NativeInventory.native_f2_hamiltonian_cycle_with_native_edge_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2NativeInventory.native_f2_native_edge_catalog`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeClassification](NativeF2EdgeClassification.md)
