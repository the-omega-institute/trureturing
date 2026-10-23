# Selected Terminal Labels of the Same Actual c Edges

## Abstract

The literal F2 seams and the exact inventory of one supplied frame walk earn the selected-terminal condition for every actual c edge.

**Theorem 1.1 (Every Literal Seam Endpoint Has a Selected Terminal).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{F2Seam}\left(m, e\right) \Rightarrow \left(\forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{Member}\left(x, e\right) \Rightarrow \mathrm{Member}\left(\mathrm{LastLabel}\left(x\right), \mathrm{PairSet}\left(0, \mathrm{Last}\left(m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SelectedC.native_f2_seam_selected_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, every literal F2 seam e, and every endpoint x of e, the terminal label x(m) is zero or m. For a T seam, its starting endpoint is the finish of its own indexed deleted a or b edge. The complete a-cut classification puts both terminal labels in {0,m}; the b-cut classification puts its terminal in the same set. An E seam similarly starts at the finish of its own indexed deleted b edge. The generator c fixes the terminal position, so the second endpoint keeps that label. This proves the condition directly from the independently defined seams.

**Theorem 1.2 (The Supplied Frame Walk Earns Its Selected c-Terminal Condition).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; \forall base \in \mathrm{FrameVertex}\left(frame\right),\; \forall w \in \mathrm{FrameClosedWalk}\left(frame, base\right),\; \left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{Member}\left(e, \mathrm{AmbientEdges}\left(w\right)\right) \Leftrightarrow \left(\left(\mathrm{F2NativeEdge}\left(m, \mathrm{Sym2Map}\left(\mathrm{undoRelabel}\left(frame\right), e\right)\right) \land \left(\neg \mathrm{F2DeletedEdge}\left(m, \mathrm{Sym2Map}\left(\mathrm{undoRelabel}\left(frame\right), e\right)\right)\right)\right) \lor \mathrm{F2Seam}\left(m, \mathrm{Sym2Map}\left(\mathrm{undoRelabel}\left(frame\right), e\right)\right)\right)\right) \Rightarrow \left(\forall x \in \mathrm{FrameVertex}\left(frame\right),\; \forall y \in \mathrm{FrameVertex}\left(frame\right),\; \left(\mathrm{Value}\left(y\right) = \mathrm{Multiply}\left(\mathrm{Value}\left(x\right), \mathrm{c}\left(m\right)\right) \land \mathrm{Member}\left(\mathrm{Sym2Pair}\left(x, y\right), \mathrm{Edges}\left(w\right)\right)\right) \Rightarrow \mathrm{Member}\left(\mathrm{LastLabel}\left(x\right), \mathrm{ToFinset}\left(\mathrm{Selected}\left(frame\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SelectedC.native_j2_frame_c_selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and every SupplyFrame(m,2), take any supplied closed walk w in the actual FrameDomain, with its exact undo-relabel inventory of native-minus-deleted edges together with F2 seams. Whenever x,y are actual frame vertices, y=x*c and their actual subtype edge occurs in w, the terminal label of x belongs to F.selected.toFinset. The c generator differs from both native generators a and b, so the retained native branch of this same inventory cannot supply that edge. The seam branch supplies the raw {0,m} terminal condition, and the same earned frame relabelling maps that set exactly to F.selected. The proof keeps this particular walk and earns its c-edge condition; no replacement cycle or separate target invariant is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SelectedC.native_f2_seam_selected_terminal`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SelectedC.native_j2_frame_c_selected`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory](NativeJ2FrameInventory.md)
