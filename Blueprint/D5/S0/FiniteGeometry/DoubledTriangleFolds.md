# Minimum-fold colorings of doubled triangles

## Abstract

Minimum-fold colorings of doubled triangles

**Theorem 1.1 (Equality forces the two-sided coloring).**

Lean statement: `D5/S0/FiniteGeometry/DoubledTriangleFolds.minimum_fold_uniqueness`

*Proof.* Machine-checked in Lean as `D5/S0/FiniteGeometry/DoubledTriangleFolds.minimum_fold_uniqueness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lakshitha Fernando, Eranda Dhananjaya, Rajitha Ranasinghe, and Dinusha Priyadarshani (2026). *Good colorings of doubled triangles and a conjecture of Schwartz*. DOI: [10.48550/arXiv.2611.12065](https://doi.org/10.48550/arXiv.2611.12065). URL: <https://arxiv.org/html/2611.12065v1#Thmquestionx2>.

*Commentary.*

For every positive side length n, a coloring is good and has exactly 3n folds if and only if its front faces all have one color and its back faces all have the opposite color. Goodness requires the signed difference in incident black and white face corners to be divisible by three at every glued vertex. The identity symmetry suffices, with a global swap when the front is white.

Up and down cells are indexed by barycentric triples of sum n minus one and n minus two, respectively. Each up cell and omitted corner specifies an edge on each sheet when the corresponding coordinate is positive. At zero there is one seam edge and the two incident up cells lie on opposite sheets. In particular, side length one has two faces and three distinct seam edges.

A monochromatic ring would force every successive ring toward the corner to have that color. The vertex congruence first fixes both faces at the seam, then propagates across each sheet through triples of consecutive faces. The two corner faces have different colors. In a closed traversal of a nonmonochromatic ring, a rise and a fall in color occur at different edges. Every fold crosses two coordinate cuts, so there are at least 3n folds. At equality each cut has exactly two.

At each side, the two corner folds leaving the side exhaust the nearest parallel cut. The up, down, up fans joining consecutive side faces on each sheet therefore use unfolded edges. Both sheets retain their first corner colors along the side, so every seam edge folds. The seam count exhausts the total of 3n and the remaining edges are unfolded. Moving one unit of barycentric mass toward a fixed corner connects all up cells through down cells within each sheet, and every down cell joins an up cell.

Conversely, the opposite uniform sheets balance their incident corners at boundary vertices. Each interior vertex has six corners of one color. Exactly the seam edges fold, giving 3n folds.

## References

- Truth anchor: `D5/S0/FiniteGeometry/DoubledTriangleFolds.minimum_fold_uniqueness`
