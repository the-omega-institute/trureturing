# One Actual Frame Cycle With All Inventories

## Abstract

One choice of the actual complete F2 Hamilton cycle is mapped once to any native two-label frame, preserving its full inventory and earning retained a/b edges for the actual k2 Q construction.

**Definition 1.1 (The Actual Independent Frame Layer).**

$$\mathrm{FrameDomain}\left(F\right) = \mathrm{Layer}\left(\mathrm{ToFinset}\left(\mathrm{Selected}\left(F\right)\right), \mathrm{CycleOfList}\left(\mathrm{Cons}\left(\mathrm{Terminal}\left(F\right), \mathrm{Base}\left(F\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory.FrameDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FrameDomain(F) is precisely Layer(F.selected.toFinset, F.terminal :: F.base). The mapped target is this actual layer; it is never identified by definition with the raw F2Domain.

**Definition 1.2 (Undo the Earned Frame Relabelling).**

$$\mathrm{undoRelabel}\left(F, x\right) = \mathrm{Multiply}\left(\mathrm{Inverse}\left(\mathrm{relabel}\left(F\right)\right), x\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory.undoRelabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Undo is left multiplication by the inverse of the same relabel(F) used by frameDomainIso. Full native-edge, deleted-edge and seam inventories are evaluated on the two ambient endpoints after this undo map.

**Theorem 1.3 (The Same Actual Mapped Cycle Earns Every Required Inventory).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall F \in \mathrm{SupplyFrame}\left(m, 2\right),\; \exists rawBase \in \mathrm{F2Vertex}\left(m\right),\; \exists rawWalk \in \mathrm{F2ClosedWalk}\left(m, rawBase\right),\; \exists base \in \mathrm{FrameVertex}\left(F\right),\; \exists w \in \mathrm{FrameClosedWalk}\left(F, base\right),\; \mathrm{IsHamiltonianCycle}\left(rawWalk\right) \land \left(\left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{Member}\left(e, \mathrm{AmbientEdges}\left(rawWalk\right)\right) \Leftrightarrow \left(\left(\mathrm{F2NativeEdge}\left(m, e\right) \land \left(\neg \mathrm{F2DeletedEdge}\left(m, e\right)\right)\right) \lor \mathrm{F2Seam}\left(m, e\right)\right)\right) \land \left(base = \mathrm{Apply}\left(\mathrm{frameDomainIso}\left(m, F\right), rawBase\right) \land \left(\mathrm{HEq}\left(w, \mathrm{WalkMap}\left(rawWalk, \mathrm{frameDomainIso}\left(m, F\right)\right)\right) \land \left(\mathrm{IsHamiltonianCycle}\left(w\right) \land \left(\left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{Member}\left(e, \mathrm{AmbientEdges}\left(w\right)\right) \Leftrightarrow \left(\left(\mathrm{F2NativeEdge}\left(m, \mathrm{Sym2Map}\left(\mathrm{undoRelabel}\left(F\right), e\right)\right) \land \left(\neg \mathrm{F2DeletedEdge}\left(m, \mathrm{Sym2Map}\left(\mathrm{undoRelabel}\left(F\right), e\right)\right)\right)\right) \lor \mathrm{F2Seam}\left(m, \mathrm{Sym2Map}\left(\mathrm{undoRelabel}\left(F\right), e\right)\right)\right)\right) \land \left(\left(\forall i \in \mathrm{Product}\left(\mathrm{Fin}\left(3\right), \mathrm{Bool}\right),\; \mathrm{Member}\left(\mathrm{Sym2Map}\left(\mathrm{LeftMultiply}\left(\mathrm{relabel}\left(F\right)\right), \mathrm{markedEdge}\left(m, i\right)\right), \mathrm{AmbientEdges}\left(w\right)\right)\right) \land \left(\left(\forall x \in \mathrm{FrameVertex}\left(F\right),\; \forall y \in \mathrm{FrameVertex}\left(F\right),\; \left(\mathrm{Value}\left(y\right) = \mathrm{Multiply}\left(\mathrm{Value}\left(x\right), \mathrm{a}\left(m\right)\right) \land \left(\neg \mathrm{Sym2Pair}\left(\mathrm{LastLabel}\left(x\right), \mathrm{LastLabel}\left(y\right)\right) = \mathrm{Sym2Pair}\left(\mathrm{Apply}\left(\mathrm{relabel}\left(F\right), \mathrm{Last}\left(m\right)\right), \mathrm{Apply}\left(\mathrm{relabel}\left(F\right), 0\right)\right)\right)\right) \Rightarrow \mathrm{Member}\left(\mathrm{Sym2Pair}\left(x, y\right), \mathrm{Edges}\left(w\right)\right)\right) \land \left(\left(\forall x \in \mathrm{FrameVertex}\left(F\right),\; \forall y \in \mathrm{FrameVertex}\left(F\right),\; \left(\mathrm{Value}\left(y\right) = \mathrm{Multiply}\left(\mathrm{Value}\left(x\right), \mathrm{b}\left(m\right)\right) \land \left(\neg \mathrm{Member}\left(\mathrm{LastLabel}\left(x\right), \mathrm{ToFinset}\left(\mathrm{Selected}\left(F\right)\right)\right)\right)\right) \Rightarrow \mathrm{Member}\left(\mathrm{Sym2Pair}\left(x, y\right), \mathrm{Edges}\left(w\right)\right)\right) \land \left(\left(\neg \mathrm{Apply}\left(\mathrm{relabel}\left(F\right), \mathrm{Last}\left(m\right)\right) = \mathrm{Apply}\left(\mathrm{relabel}\left(F\right), 0\right)\right) \land \mathrm{ToFinset}\left(\mathrm{Selected}\left(F\right)\right) = \mathrm{PairSet}\left(\mathrm{Apply}\left(\mathrm{relabel}\left(F\right), \mathrm{Last}\left(m\right)\right), \mathrm{Apply}\left(\mathrm{relabel}\left(F\right), 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory.native_j2_frame_cycle_with_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and every SupplyFrame(m,2), choose the already proved canonical actual F2 Hamilton witness only once and map it by frameDomainIso. The theorem returns both raw and mapped witnesses together with the raw Hamilton and full-inventory facts, identifies the mapped base, and identifies the mapped walk by heterogeneous equality. This exact mapped walk is Hamiltonian, has the full raw native-minus-deleted plus seam inventory after undo relabelling, and contains the images of all six independently specified marked edges. The same walk also earns the actual native a-edge inventory: for frame vertices x,y with y=x*a, the edge is retained whenever its terminal-label pair differs from {rho(m),rho(0)}. The complete raw a-cut classification shows that both deleted a edges have terminal pair {0,m}; mapping the labels gives exactly the excluded pair. For y=x*b, every edge whose starting terminal lies outside F.selected.toFinset is retained, since the raw b-cut classification permits terminal zero or m only. These facts are conclusions earned from the selected witness, not supplied inventory premises. The two labels p=rho(m), q=rho(0) are distinct and their set is exactly the two selected frame labels. In particular the a-edge claim does not allow p=q. The same graph isomorphism and raw witness remain available to transport the literal six slices and actual half-restoration paths before the exceptional k2 Q route. The theorem supplies a base witness and its inventories; the higher all-size recursive Hamilton closure remains a separate obligation. This combines existing F2 inventory, marked-edge and graph-map results with the complete native cut classifications.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory.FrameDomain`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory.native_j2_frame_cycle_with_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory.undoRelabel`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport](NativeJ2FrameTransport.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory](NativeJ2MarkedInventory.md)
