# Labelled supported brick geometry

## Abstract

A labelled real-plane brick history realizes the literal capacity trajectory.

OEIS A395531 places bricks of widths 1,2,3,... in the first quadrant, as close to x=0 as possible and on the highest supported row without overhang. The results below use the existing exact row scan and capacity conjugacy. rowEnd(ws,y) is the right endpoint of row y, with an empty slice outside the stored wall. A brick rectangle is [x,x+n) times [y,y+1); half-open ownership permits shared boundaries and implies disjoint ordinary interiors.

wall(ws,t,z) holds when t is nonnegative and lies below the right endpoint of the unique unit-height row containing z. legal requires first-quadrant coordinates, nonoverlap and full bottom support on the floor or the upper face of an occupied row. It allows arbitrary real horizontal endpoints and imposes no left contact. sourceOptimal requires legality and proves that x is minimal and y is maximal among all those physical competitors.

**Theorem 1.1 (The discrete scan has the physical real-plane optimum).**

$$\forall n \in \mathbb{N},\; \forall ws \in List\left(\mathbb{N}\right),\; \left(0 < n \land PairwiseLe\left(ws\right)\right) \Rightarrow \left(\exists x \in \mathbb{N},\; \exists y \in \mathbb{N},\; PlacementSite\left(n, ws, x, y\right) \land \left(sourceOptimal\left(n, ws, x, y\right) \land \left(\forall t \in \mathbb{R},\; \forall z \in \mathbb{R},\; wall\left(sourceRowStep\left(n, ws\right), t, z\right) \Leftrightarrow \left(wall\left(ws, t, z\right) \lor rectangle\left(n, x, y, t, z\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GreedyBrickLabelledHistory.continuous_row_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive n and monotone natural width list, the scan supplies natural x,y. A real competitor is reduced to the same row's occupied frontier: nonoverlap bounds its x below by that frontier and support makes the frontier eligible. The existing discrete theorem supplies the ordering. Floor-slice equivalences transport the exact cell addition to the real half-open rectangle union.

labelledWall(pos,N) is the union of rectangles labelled 1 through N, each with width equal to its label and position pos(i). NatToNatPair denotes functions from natural labels to natural coordinate pairs; x(pos,i) and y(pos,i) are their two coordinates. historyLegal uses only these previously placed labelled rectangles: the bottom is on the floor or every point under it lies on an old brick's upper face. historyOptimal compares against all such real competitors. These definitions contain no scan or assumed optimum.

**Theorem 1.2 (One labelled history realizes every finite prefix).**

$$\exists pos \in NatToNatPair\left(\right),\; \left(\forall N \in \mathbb{N},\; \forall t \in \mathbb{R},\; \forall z \in \mathbb{R},\; wall\left(widths\left(trajectory\left(N\right)\right), t, z\right) \Leftrightarrow labelledWall\left(pos, N, t, z\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow historyOptimal\left(pos, n - 1, n, x\left(pos, n\right), y\left(pos, n\right)\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow closedSupport\left(pos, n - 1, n, x\left(pos, n\right), y\left(pos, n\right)\right)\right) \land \left(\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; \left(0 < i \land i < j\right) \Rightarrow \left(\forall t \in \mathbb{R},\; \forall z \in \mathbb{R},\; rectangle\left(i, x\left(pos, i\right), y\left(pos, i\right), t, z\right) \Rightarrow \left(\neg rectangle\left(j, x\left(pos, j\right), y\left(pos, j\right), t, z\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GreedyBrickLabelledHistory.actual_labelled_history` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One position function is chosen for every positive brick label. Induction proves that every finite union equals the wall reconstructed from the actual trajectory. The union then transports full support in both directions between row geometry and the actual labelled brick faces. Every step is physically optimal in that preceding history, and distinct labels have disjoint half-open rectangles. Closed bottom support includes the right endpoint: an old brick covering the point half a unit before it has an integer right endpoint at least as far to the right.

These are derivations of the published placement rule, attributed to OEIS A395531 and A233380. They do not prove the OEIS self-composition identity. The geometric statements use unbounded mathematical naturals and real coordinates, not machine-integer simulations.

## References

- Truth anchor: `D5/S3/ArithSums/GreedyBrickLabelledHistory.actual_labelled_history`
- Truth anchor: `D5/S3/ArithSums/GreedyBrickLabelledHistory.continuous_row_geometry`
- Dependency: [D5/S3/ArithSums/GreedyBrickCapacityTotality](GreedyBrickCapacityTotality.md)
