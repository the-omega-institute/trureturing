# Actual J2 Half-Cut Restoration

## Abstract

Restoring the opposite three actual J2 cuts earns both native one-frame three-component partitions, including the literal barred exception.

**Definition 1.1 (The Selected Three Actual Cuts).**

$$\forall m \in \mathrm{Nat},\; \forall side \in \mathrm{Bool},\; \forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{HalfCut}\left(m, side, e\right) \Leftrightarrow \left(\exists i \in \mathrm{Fin}\left(3\right),\; e = \mathrm{markedEdge}\left(m, \mathrm{Tuple2}\left(i, side\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.HalfCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HalfCut(m,side,e) holds precisely when e equals markedEdge(m,(i,side)) for an i in Fin(3).

**Definition 1.2 (The Independent Half-Cut Edge Inventory).**

$$\forall m \in \mathrm{Nat},\; \forall side \in \mathrm{Bool},\; \forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{HalfEdge}\left(m, side, e\right) \Leftrightarrow \left(\left(\left(\mathrm{F2NativeEdge}\left(m, e\right) \land \left(\neg \mathrm{F2DeletedEdge}\left(m, e\right)\right)\right) \lor \mathrm{F2Seam}\left(m, e\right)\right) \land \left(\neg \mathrm{HalfCut}\left(m, side, e\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.HalfEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep the complete actual F2 native inventory outside the original T/E cuts together with the actual T/E seams, and remove only the three marked cuts with the selected side.

**Definition 1.3 (The Actual Graph after Three Cuts).**

$$\forall m \in \mathrm{Nat},\; \forall side \in \mathrm{Bool},\; \forall x \in \mathrm{Configuration}\left(m\right),\; \forall y \in \mathrm{Configuration}\left(m\right),\; \mathrm{Adj}\left(\mathrm{halfGraph}\left(m, side\right), x, y\right) \Leftrightarrow \left(\mathrm{HalfEdge}\left(m, side, \mathrm{Sym2Pair}\left(x, y\right)\right) \land \left(\neg x = y\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.halfGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

halfGraph(m,side) is SimpleGraph.fromEdgeSet of HalfEdge(m,side). It contains the actual six-cut surviving graph and restores exactly the opposite three marked edges.

**Definition 1.4 (The Independent Half-Component Starting Ports).**

$$\forall side \in \mathrm{Bool},\; \forall i \in \mathrm{Fin}\left(3\right),\; \mathrm{halfStart}\left(side, i\right) = \mathrm{IfThenElse}\left(side, \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 0, \mathrm{Tuple3}\left(0, \mathrm{True}, \mathrm{False}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 1, \mathrm{Tuple3}\left(1, \mathrm{True}, \mathrm{True}\right), \mathrm{Tuple3}\left(2, \mathrm{True}, \mathrm{True}\right)\right)\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 0, \mathrm{Tuple3}\left(0, \mathrm{False}, \mathrm{False}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 1, \mathrm{Tuple3}\left(0, \mathrm{False}, \mathrm{True}\right), \mathrm{Tuple3}\left(1, \mathrm{False}, \mathrm{False}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.halfStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For side false the starts are R0, L0 and R1; for side true they are bar R0, bar L1 and bar L2, in native index order.

**Definition 1.5 (The Independent Half-Component Finishing Ports).**

$$\forall side \in \mathrm{Bool},\; \forall i \in \mathrm{Fin}\left(3\right),\; \mathrm{halfFinish}\left(side, i\right) = \mathrm{IfThenElse}\left(side, \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 0, \mathrm{Tuple3}\left(1, \mathrm{True}, \mathrm{False}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 1, \mathrm{Tuple3}\left(2, \mathrm{True}, \mathrm{False}\right), \mathrm{Tuple3}\left(0, \mathrm{True}, \mathrm{True}\right)\right)\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 0, \mathrm{Tuple3}\left(2, \mathrm{False}, \mathrm{False}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 1, \mathrm{Tuple3}\left(1, \mathrm{False}, \mathrm{True}\right), \mathrm{Tuple3}\left(2, \mathrm{False}, \mathrm{True}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.halfFinish` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For side false the finishes are R2, L1 and L2; for side true they are bar R1, bar R2 and bar L0. The barred indices are retained literally.

**Theorem 1.6 (Both Actual Native Three-Component Partitions Exhaust F2 Exactly Once).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall side \in \mathrm{Bool},\; \exists paths \in \mathrm{DependentWalkFamily}\left(\mathrm{Fin}\left(3\right), \mathrm{halfGraph}\left(m, side\right), \mathrm{HalfStartPortFamily}\left(side\right), \mathrm{HalfFinishPortFamily}\left(side\right), m\right),\; \left(\forall i \in \mathrm{Fin}\left(3\right),\; \mathrm{IsPath}\left(\mathrm{apply}\left(paths, i\right)\right)\right) \land \left(\left(\forall i \in \mathrm{Fin}\left(3\right),\; \forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{Member}\left(x, \mathrm{Support}\left(\mathrm{apply}\left(paths, i\right)\right)\right) \Leftrightarrow \mathrm{Reachable}\left(\mathrm{halfGraph}\left(m, side\right), \mathrm{port}\left(m, \mathrm{halfStart}\left(side, i\right)\right), x\right)\right) \land \left(\left(\forall i \in \mathrm{Fin}\left(3\right),\; \forall x \in \mathrm{Configuration}\left(m\right),\; \forall y \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{Adj}\left(\mathrm{halfGraph}\left(m, side\right), x, y\right) \land \mathrm{Reachable}\left(\mathrm{halfGraph}\left(m, side\right), \mathrm{port}\left(m, \mathrm{halfStart}\left(side, i\right)\right), x\right)\right) \Leftrightarrow \mathrm{Member}\left(\mathrm{Sym2Pair}\left(x, y\right), \mathrm{Edges}\left(\mathrm{apply}\left(paths, i\right)\right)\right)\right) \land \left(\left(\forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{F2Domain}\left(m, x\right) \Leftrightarrow \left(\exists i \in \mathrm{Fin}\left(3\right),\; \mathrm{Member}\left(x, \mathrm{Support}\left(\mathrm{apply}\left(paths, i\right)\right)\right) \land \left(\forall j \in \mathrm{Fin}\left(3\right),\; \mathrm{Member}\left(x, \mathrm{Support}\left(\mathrm{apply}\left(paths, j\right)\right)\right) \Rightarrow j = i\right)\right)\right) \land \left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{Member}\left(e, \mathrm{FlattenWalkEdges}\left(paths\right)\right) \Leftrightarrow \mathrm{HalfEdge}\left(m, side, e\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.native_j2_half_component_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and either side, three actual simple paths connect the independently specified starting and finishing ports. Each path exhausts its complete reachable component and contains every actual edge incident to it. A configuration belongs to F2Domain(m) exactly when it belongs to the support of a unique path. The flattened edge lists contain an edge exactly when it belongs to the independent HalfEdge(m,side) inventory; therefore they are the retained inventory of any original native F2 Hamilton witness with that same exact full inventory.

The six-cut partition supplies six actual component walks. Actual marked-edge injectivity proves that each of the opposite three marked edges is restored, while the selected three cuts remain missing. Concatenating those earned reachability bridges gives the independent pairs R0 to R2, L0 to L1 and R1 to L2 for side false, and bar R0 to bar R1, bar L1 to bar R2 and bar L2 to bar L0 for side true.

The original actual F2 Hamilton cycle bounds the half-cut graph degree by two and makes all selected ports leaves. A simple reachable path is nonbacktracking, so the leaf-component theorem earns full vertex and edge exhaustion. Every one of the six old components is linked to a half-component root, which proves full F2 coverage. The selected leaves and independent endpoint table force uniqueness. The barred table keeps the native k equals two exception; it does not rename or reverse the base indexing.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.HalfCut`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.HalfEdge`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.halfFinish`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.halfGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.halfStart`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration.native_j2_half_component_partition`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components](NativeJ2Components.md)
