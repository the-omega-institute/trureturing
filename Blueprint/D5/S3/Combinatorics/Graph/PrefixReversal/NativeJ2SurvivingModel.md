# The Actual F2 Six-Cut Graph

## Abstract

The actual surviving graph uses the complete F2 edge inventory with exactly the six independently specified marked edges removed.

**Definition 1.1 (The Six Independently Specified Cuts).**

$$\forall m \in \mathrm{Nat},\; \forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{MarkedCut}\left(m, e\right) \Leftrightarrow \left(\exists q \in \mathrm{Prod}\left(\mathrm{Fin}\left(3\right), \mathrm{Bool}\right),\; e = \mathrm{markedEdge}\left(m, q\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingModel.MarkedCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

MarkedCut(m,e) means e equals markedEdge(m,q) for q in Fin(3) times Bool. These six actual b edges have disjoint endpoint sets because all twelve independently specified ports are distinct.

**Definition 1.2 (The Independent Surviving Edge Inventory).**

$$\forall m \in \mathrm{Nat},\; \forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{SurvivingEdge}\left(m, e\right) \Leftrightarrow \left(\left(\left(\mathrm{F2NativeEdge}\left(m, e\right) \land \left(\neg \mathrm{F2DeletedEdge}\left(m, e\right)\right)\right) \lor \mathrm{F2Seam}\left(m, e\right)\right) \land \left(\neg \mathrm{MarkedCut}\left(m, e\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingModel.SurvivingEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An undirected edge survives exactly when it is an actual F2 native edge outside F2DeletedEdge or an actual F2 c seam, and it is outside MarkedCut. No word, walk support or chosen component defines this predicate.

**Definition 1.3 (The Graph Built from the Surviving Inventory).**

$$\forall m \in \mathrm{Nat},\; \forall x \in \mathrm{Configuration}\left(m\right),\; \forall y \in \mathrm{Configuration}\left(m\right),\; \mathrm{Adj}\left(\mathrm{survivingGraph}\left(m\right), x, y\right) \Leftrightarrow \left(\mathrm{SurvivingEdge}\left(m, \mathrm{Sym2Pair}\left(x, y\right)\right) \land \left(\neg x = y\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingModel.survivingGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

survivingGraph(m) is SimpleGraph.fromEdgeSet applied to the set of edges satisfying SurvivingEdge(m). Its adjacency law is the surviving inventory at s(x,y), together with x distinct from y.

The internal proof takes one actual F2 Hamilton witness containing all six marked edges. Mapping the original actual cycle into the Cayley graph bounds surviving degree by two. Each port loses its marked incident edge, so its surviving neighbor set has at most one element. These earned facts are consumed by the actual word-component proof.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingModel.MarkedCut`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingModel.SurvivingEdge`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingModel.survivingGraph`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory](NativeJ2MarkedInventory.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts](NativeJ2MarkedPorts.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing](../Walks/EdgeSlicing.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/LeafNonbacktrackingComponent](../Walks/LeafNonbacktrackingComponent.md)
