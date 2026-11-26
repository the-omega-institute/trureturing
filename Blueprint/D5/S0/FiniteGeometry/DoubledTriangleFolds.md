# Minimum-fold colorings of doubled triangles

## Abstract

Minimum-fold colorings of doubled triangles

**Definition 1.1 (Barycentric axes).**

$$\operatorname{Axis}=\{x,y,z\}$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.Axis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three constructors of Axis index the three coordinates.

**Definition 1.2 (Barycentric coordinate carrier).**

$$\forall n: \mathbb{N}, \forall d: \mathbb{N}, \operatorname{Point}\left(n, d\right)=\{(x,y,z) \in \mathbb{N}\times\mathbb{N}\times\mathbb{N} \mid x+y+z+d=n\}$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.Point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural coordinate triple carries a proof of the additive constraint. The offset is zero for vertices, one for up cells and two for down cells.

**Definition 1.3 (Coordinate lookup).**

$$\forall n: \mathbb{N}, \forall d: \mathbb{N}, \forall p: \operatorname{Point}\left(n, d\right), \operatorname{coord}\left(p, x\right)=\operatorname{x}\left(p\right)\land \operatorname{coord}\left(p, y\right)=\operatorname{y}\left(p\right)\land \operatorname{coord}\left(p, z\right)=\operatorname{z}\left(p\right)$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.coord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Point.coord selects the coordinate indexed by the axis.

**Definition 1.4 (Cells of one sheet).**

$$\forall n: \mathbb{N}, \operatorname{Cell}\left(n\right)=\operatorname{Sum}\left(\operatorname{Point}\left(n, 1\right), \operatorname{Point}\left(n, 2\right)\right)$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.Cell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two summands distinguish up and down cells, including an empty down-cell carrier at side length one.

**Definition 1.5 (Faces of the doubled subdivision).**

$$\forall n: \mathbb{N}, \operatorname{Face}\left(n\right)=\operatorname{Bool}\times\operatorname{Cell}\left(n\right)$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.Face` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean tag is false for the front and true for the back.

**Definition 1.6 (Face colorings).**

$$\forall n: \mathbb{N}, \operatorname{Coloring}\left(n\right)=\operatorname{Face}\left(n\right)\to \operatorname{Bool}$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.Coloring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

True denotes black and false denotes white.

**Definition 1.7 (Up face).**

$$\forall n: \mathbb{N}, \forall s: \operatorname{Bool}, \forall p: \operatorname{Point}\left(n, 1\right), \operatorname{up}\left(s, p\right)=(s,\operatorname{inl}\left(p\right))$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.up` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the left summand of Cell on the selected sheet.

**Definition 1.8 (Down face).**

$$\forall n: \mathbb{N}, \forall s: \operatorname{Bool}, \forall p: \operatorname{Point}\left(n, 2\right), \operatorname{down}\left(s, p\right)=(s,\operatorname{inr}\left(p\right))$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.down` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the right summand of Cell on the selected sheet.

**Definition 1.9 (Boundary vertices).**

$$\forall n: \mathbb{N}, \forall v: \operatorname{Point}\left(n, 0\right), \operatorname{boundary}\left(v\right)\iff \operatorname{x}\left(v\right)=0\lor \operatorname{y}\left(v\right)=0\lor \operatorname{z}\left(v\right)=0$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A boundary vertex has at least one zero coordinate. Its front and back representatives are identified.

**Definition 1.10 (Single coordinate increment).**

$$\forall a: \operatorname{Axis}, \forall b: \operatorname{Axis}, \operatorname{bump}\left(a, b\right)=\operatorname{if} a=b \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.bump` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The increment is one on the selected axis and zero elsewhere.

**Definition 1.11 (Two coordinate increments).**

$$\forall a: \operatorname{Axis}, \forall b: \operatorname{Axis}, \operatorname{bumpPair}\left(a, b\right)=\operatorname{if} a=b \operatorname{then} 0 \operatorname{else} 1$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.bumpPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both coordinates other than the selected axis receive one.

**Definition 1.12 (Up corner incident to a vertex).**

$$\forall n: \mathbb{N}, \forall v: \operatorname{Point}\left(n, 0\right), \forall s: \operatorname{Bool}, \forall a: \operatorname{Axis}, \operatorname{atUp}\left(v, s, a\right)=\operatorname{if} 0<\operatorname{coord}\left(v, a\right) \operatorname{then} \operatorname{some}\left(\operatorname{up}\left(s, (\operatorname{x}\left(v\right)-\operatorname{bump}\left(a, x\right),\operatorname{y}\left(v\right)-\operatorname{bump}\left(a, y\right),\operatorname{z}\left(v\right)-\operatorname{bump}\left(a, z\right))\right)\right) \operatorname{else} \operatorname{none}$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.atUp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract one in the selected coordinate when it is positive. The resulting point indexes the up face on the chosen sheet.

**Definition 1.13 (Down corner incident to a vertex).**

$$\forall n: \mathbb{N}, \forall v: \operatorname{Point}\left(n, 0\right), \forall s: \operatorname{Bool}, \forall a: \operatorname{Axis}, \operatorname{atDown}\left(v, s, a\right)=\operatorname{if} \operatorname{bumpPair}\left(a, x\right)\leq \operatorname{x}\left(v\right)\land \operatorname{bumpPair}\left(a, y\right)\leq \operatorname{y}\left(v\right)\land \operatorname{bumpPair}\left(a, z\right)\leq \operatorname{z}\left(v\right) \operatorname{then} \operatorname{some}\left(\operatorname{down}\left(s, (\operatorname{x}\left(v\right)-\operatorname{bumpPair}\left(a, x\right),\operatorname{y}\left(v\right)-\operatorname{bumpPair}\left(a, y\right),\operatorname{z}\left(v\right)-\operatorname{bumpPair}\left(a, z\right))\right)\right) \operatorname{else} \operatorname{none}$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.atDown` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract one in each of the two other coordinates when both permit it. The resulting point indexes the down face on the chosen sheet.

**Definition 1.14 (Incident corners on one sheet).**

$$\forall n: \mathbb{N}, \forall v: \operatorname{Point}\left(n, 0\right), \forall s: \operatorname{Bool}, \operatorname{sheetCorners}\left(v, s\right)=\operatorname{filterMap}\left(\operatorname{id}, [\operatorname{atUp}\left(v, s, x\right),\operatorname{atUp}\left(v, s, y\right),\operatorname{atUp}\left(v, s, z\right),\operatorname{atDown}\left(v, s, x\right),\operatorname{atDown}\left(v, s, y\right),\operatorname{atDown}\left(v, s, z\right)]\right)$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.sheetCorners` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six possible corners are enumerated in axis order, first up and then down. Absent options are discarded by filterMap.

**Definition 1.15 (Incident corners at a quotient vertex).**

$$\forall n: \mathbb{N}, \forall v: \operatorname{Point}\left(n, 0\right), \forall s: \operatorname{Bool}, \operatorname{incidentCorners}\left(v, s\right)=\operatorname{if} \operatorname{boundary}\left(v\right) \operatorname{then} \operatorname{sheetCorners}\left(v, \operatorname{false}\right) ++ \operatorname{sheetCorners}\left(v, \operatorname{true}\right) \operatorname{else} \operatorname{sheetCorners}\left(v, s\right)$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.incidentCorners` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Boundary vertices concatenate the two sheet lists. An interior vertex keeps the list on its own sheet.

**Definition 1.16 (Black corner count).**

$$\forall n: \mathbb{N}, \forall C: \operatorname{Coloring}\left(n\right), \forall l: \operatorname{List}\left(\operatorname{Face}\left(n\right)\right), \operatorname{black}\left(C, l\right)=\operatorname{countP}\left(C, l\right)$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.black` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural count of true colors in the list is read as an integer.

**Definition 1.17 (White corner count).**

$$\forall n: \mathbb{N}, \forall C: \operatorname{Coloring}\left(n\right), \forall l: \operatorname{List}\left(\operatorname{Face}\left(n\right)\right), \operatorname{white}\left(C, l\right)=\operatorname{countP}\left((\Lambda f:\operatorname{Face}\left(n\right), \neg C\left(f\right)), l\right)$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.white` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural count of false colors in the list is read as an integer.

**Definition 1.18 (Good coloring).**

$$\forall n: \mathbb{N}, \forall C: \operatorname{Coloring}\left(n\right), \operatorname{Good}\left(C\right)\iff (\forall v: \operatorname{Point}\left(n, 0\right), \forall s: \operatorname{Bool}, 3\mid (\operatorname{black}\left(C, \operatorname{incidentCorners}\left(v, s\right)\right)-\operatorname{white}\left(C, \operatorname{incidentCorners}\left(v, s\right)\right)))$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.Good` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every quotient vertex the black corner count minus the white corner count is divisible by three in the integers. On the boundary the choice of representative sheet gives the same list.

**Definition 1.19 (Edges of the doubled subdivision).**

$$\forall n: \mathbb{N}, \operatorname{Edge}\left(n\right)=\{(p,a,s) \in \operatorname{Point}\left(n, 1\right)\times\operatorname{Axis}\times\operatorname{Bool} \mid \operatorname{coord}\left(p, a\right)=0\implies s=\operatorname{false}\}$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An up cell and omitted axis label an edge. A positive coordinate permits both sheet tags. A zero coordinate permits the canonical false sheet tag only.

**Definition 1.20 (Down cell across an interior edge).**

$$\forall n: \mathbb{N}, \forall p: \operatorname{Point}\left(n, 1\right), \forall a: \operatorname{Axis}, \operatorname{coord}\left(p, a\right)\neq 0\implies \operatorname{below}\left(p, a\right)=(\operatorname{x}\left(p\right)-\operatorname{bump}\left(a, x\right),\operatorname{y}\left(p\right)-\operatorname{bump}\left(a, y\right),\operatorname{z}\left(p\right)-\operatorname{bump}\left(a, z\right))$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.below` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive coordinate permits natural subtraction of one. It produces a triple of sum n minus two.

**Definition 1.21 (The two faces at an edge).**

$$\forall n: \mathbb{N}, \forall (p,a,s): \operatorname{Edge}\left(n\right), \operatorname{edgeFaces}\left((p,a,s)\right)=(\operatorname{up}\left(s, p\right),\operatorname{if} \operatorname{coord}\left(p, a\right)=0 \operatorname{then} \operatorname{up}\left(\operatorname{true}, p\right) \operatorname{else} \operatorname{down}\left(s, \operatorname{below}\left(p, a\right)\right))$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.edgeFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a seam the first face is front and the second back. Away from the seam the first face is up and the second down on the same sheet.

**Definition 1.22 (Fold predicate).**

$$\forall n: \mathbb{N}, \forall C: \operatorname{Coloring}\left(n\right), \forall e: \operatorname{Edge}\left(n\right), \operatorname{Fold}\left(C, e\right)\iff C\left((\operatorname{edgeFaces}\left(e\right)).1\right)\neq C\left((\operatorname{edgeFaces}\left(e\right)).2\right)$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.Fold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two incident face colors differ.

**Definition 1.23 (Folded edges).**

$$\forall n: \mathbb{N}, \forall C: \operatorname{Coloring}\left(n\right), \operatorname{folds}\left(C\right)=\{e \in \operatorname{Edge}\left(n\right) \mid \operatorname{Fold}\left(C, e\right)\}$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.folds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set of all edges is filtered by Fold.

**Definition 1.24 (Total number of folds).**

$$\forall n: \mathbb{N}, \forall C: \operatorname{Coloring}\left(n\right), \operatorname{foldCount}\left(C\right)=\operatorname{card}\left(\operatorname{folds}\left(C\right)\right)$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.foldCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each folded edge, including a seam edge, contributes exactly once.

**Definition 1.25 (Opposite uniform sheets).**

$$\forall n: \mathbb{N}, \forall b: \operatorname{Bool}, \forall s: \operatorname{Bool}, \forall t: \operatorname{Cell}\left(n\right), \operatorname{twoSided}\left(b\right)\left((s,t)\right)=\operatorname{if} s \operatorname{then} \neg b \operatorname{else} b$$

*Formalization.* `D5/S0/FiniteGeometry/DoubledTriangleFolds.twoSided` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The front has color b and the back its Boolean complement.

**Theorem 1.26 (Equality forces the two-sided coloring).**

$$\forall n: \mathbb{N}, \forall C: \operatorname{Coloring}\left(n\right), 0<n\implies ((\operatorname{Good}\left(C\right)\land \operatorname{foldCount}\left(C\right)=3\times n)\iff (\exists b: \operatorname{Bool}, (\forall t: \operatorname{Cell}\left(n\right), C\left((\operatorname{false},t)\right)=b)\land (\forall t: \operatorname{Cell}\left(n\right), C\left((\operatorname{true},t)\right)=\neg b)))$$

*Proof.* Machine-checked in Lean as `D5/S0/FiniteGeometry/DoubledTriangleFolds.minimum_fold_uniqueness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lakshitha Fernando, Eranda Dhananjaya, Rajitha Ranasinghe, and Dinusha Priyadarshani (2026). *Good colorings of doubled triangles and a conjecture of Schwartz*. DOI: [10.48550/arXiv.2611.12065](https://doi.org/10.48550/arXiv.2611.12065). URL: <https://arxiv.org/html/2611.12065v1#Thmquestionx2>.

*Commentary.*

For every positive side length n, a coloring is good and has exactly 3n folds if and only if its front faces all have one color and its back faces all have the opposite color. Goodness requires the signed difference in incident black and white face corners to be divisible by three at every quotient vertex, including each sheet interior vertex. The identity symmetry suffices, with a global swap when the front is white.

Up and down cells are indexed by barycentric triples of sum n minus one and n minus two, respectively. Each up cell and omitted corner specifies an edge on each sheet when the corresponding coordinate is positive. At zero there is one seam edge and the two incident up cells lie on opposite sheets. In particular, side length one has two faces and three distinct seam edges.

A monochromatic ring would force every successive ring toward the corner to have that color. The vertex congruence first fixes both faces at the seam, then propagates across each sheet through triples of consecutive faces. The two corner faces have different colors. In a closed traversal of a nonmonochromatic ring, a rise and a fall in color occur at different edges. Every fold crosses two coordinate cuts, so there are at least 3n folds. At equality each cut has exactly two.

At each side, the two corner folds leaving the side exhaust the nearest parallel cut. The up, down, up fans joining consecutive side faces on each sheet therefore use unfolded edges. Both sheets retain their first corner colors along the side, so every seam edge folds. The seam count exhausts the total of 3n and the remaining edges are unfolded. Moving one unit of barycentric mass toward a fixed corner connects all up cells through down cells within each sheet, and every down cell joins an up cell.

Conversely, the opposite uniform sheets balance their incident corners at boundary vertices. Each interior vertex has six corners of one color. Exactly the seam edges fold, giving 3n folds.

## References

- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.Axis`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.Cell`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.Coloring`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.Edge`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.Face`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.Fold`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.Good`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.Point`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.atDown`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.atUp`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.below`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.black`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.boundary`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.bump`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.bumpPair`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.coord`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.down`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.edgeFaces`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.foldCount`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.folds`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.incidentCorners`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.minimum_fold_uniqueness`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.sheetCorners`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.twoSided`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.up`
- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.white`
