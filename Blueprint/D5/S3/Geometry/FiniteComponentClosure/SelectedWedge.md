# SelectedWedge

## Abstract

Finite coordinate sphere bouquets close under gluing any existing selected vertices, with both inverse homotopies relative to the corresponding singleton.

Finite coordinate sphere bouquets close under gluing any existing selected vertices, with both inverse homotopies relative to the corresponding singleton.

**Definition 1.1 (Exactly the selected components merge).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.selectedWedgeSpec`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.selectedWedgeSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For input counts m,n and selected indices i,j, the output has m+n-1 indices. It enumerates one bouquet with list p(i) concatenated with q(j), every p(k) with k different from i, and every q(l) with l different from j. The finite enumeration retains repetitions and empty lists.

**Definition 1.2 (The actual vertex gluing).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.vertexWedgeComplex`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.vertexWedgeComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ambient vertex set is the quotient of the tagged input vertex sets identifying exactly the two selected vertices. The face collection is the union of the mapped input face collections. Its realization is homeomorphic to the actual topological quotient wedge.

**Definition 1.3 (Full based closure data).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.SelectedVertexWedgeClosure`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.SelectedVertexWedgeClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The data contain positive input model counts, their bouquet specifications and selected indices, a separate BasedEquivalence from each original selected vertex to its model vertex, the based quotient-wedge normalization, an output component index, a direct WPlus witness, and a BasedEquivalence from the actual glued native vertex to that output normal vertex. BasedEquivalence contains continuous forward and backward maps, both strict basepoint equations, and both inverse homotopies relative to the corresponding singleton.

**Definition 1.4 (Selected-vertex WPlus wedge closure).**

Lean statement: `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.selectedVertexWedgeClosure`

*Formalization.* `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.selectedVertexWedgeClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite pre-abstract simplicial complexes K,L satisfying WPlus, and any existing selected vertices a,b, construct SelectedVertexWedgeClosure K L a ha b hb. Normalize the input vertices using the two actual native singleton-cylinder retractions, replace both arms by their based packets, and rearrange the quotient into the selected concatenated bouquet and every unselected component. The component count is m+n-1. Finally use based_inverse only between native finite realizations to obtain both relative inverse homotopies at actual vertices. No cylinder retraction on an arbitrary quotient is assumed. This is a classical finite wedge closure ingredient for Carnero Bravo, arXiv:2505.06457v2, Question 22. The cone-rebasing construction keeps the quotient map unchanged and changes its inverse by a native vertex-to-apex based equivalence. Its exact forward homotopy trace lies in the collapsed cone; composing the quotient with that trace is constant, which makes both concatenated inverse homotopies relative to the chosen vertex. Two such cone collapses on one native union yield the based auxiliary base-quotient splitting without assuming a quotient cylinder retraction. The selected-vertex wedge result is independent of the finite-component join result below. Arbitrary-index reduction and the graph-substitution conclusion are separate obligations and are not asserted here.

## References

- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.SelectedVertexWedgeClosure`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.selectedVertexWedgeClosure`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.selectedWedgeSpec`
- Truth anchor: `D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.vertexWedgeComplex`
- Dependency: [D5/S3/Geometry/FiniteComponentClosure/ConeSplits](ConeSplits.md)
