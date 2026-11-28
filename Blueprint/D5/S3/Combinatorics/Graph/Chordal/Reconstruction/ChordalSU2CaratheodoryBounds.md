# Carathéodory bounds for round quaternion gains

## Abstract

Caratheodory caps control round unit-quaternion reconstruction on all finite chordal graphs at small defect and across all defects at clique cutoffs five and six.

**Theorem 1.1 (Small defects at arbitrary clique number).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_su2_gain_potential_caratheodory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_su2_gain_potential_caratheodory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite chordal graph and every nonnegative defect budget through arcsine of the square root of 5 over 12, the edge error is bounded by twice arcsine of the product of the square root of 3 over 2 and the sine of the budget.

The minimum-norm point of each spherical convex hull has a representation by at most four points in its supporting hyperplane. The normalized centers transport along breadth-first layers, and an inner-product estimate controls the edges within each layer.

**Theorem 1.2 (Global clique-five coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_cliqueFive_su2_gain_potential_caratheodory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_cliqueFive_su2_gain_potential_caratheodory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph with cliques of size at most five admits the uniform coefficient pi over arccosine of one third, which is strictly below eight thirds.

The small-defect radius is convex on the relevant interval. At the crossover it matches the closed hemisphere fit available from four insertion candidates.

**Theorem 1.3 (Clique-six spherical cap).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_cliqueSix_su2_gain_potential_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_cliqueSix_su2_gain_potential_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph with cliques of size at most six admits a fit at radius arccosine of negative one quarter, for every skew gain assignment.

Five points on the unit quaternion sphere admit this cap. A supporting hyperplane or a facet of their convex hull supplies its center. Reverse simplicial elimination uses this cap at each vertex.

**Theorem 1.4 (Global clique-six coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_cliqueSix_su2_gain_potential_caratheodory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_cliqueSix_su2_gain_potential_caratheodory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph with cliques of size at most six admits the uniform coefficient twice arccosine of negative one quarter over arccosine of one sixth, which is strictly below thirteen fifths.

At the largest defect in the small-defect theorem, the radius equals the constant cap bound. The secant inequality and the cap then cover the full defect range.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_cliqueFive_su2_gain_potential_caratheodory`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_cliqueSix_su2_gain_potential_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_cliqueSix_su2_gain_potential_caratheodory`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds.exists_su2_gain_potential_caratheodory`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds](ChordalSU2SharpBounds.md)
