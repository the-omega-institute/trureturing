# Joint restrictions on continuation directions

## Abstract

Exterior lifts of the six-axis cubical grid

**Definition 1.1 (Selected lifts in one row and one column).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridExterior.selectedLiftLabels`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridExterior.selectedLiftLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix a middle indexed by i and j and a flip direction e. A false label k tests the lift of middle (k,j), and a true label k tests the lift of middle (i,k). The filter keeps exactly the labels whose lifts belong to the ambient support. The central lift, when selected, contributes both its incident labels.

**Theorem 1.2 (Axes excluded by lifts in the same exterior direction).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridExterior.exterior_lift_direction_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridExterior.exterior_lift_direction_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let an injectively labelled six-axis grid lie in a balanced cube support. Fix a selected middle lift along an axis e outside the six grid axes. Its selected-neighbor directions are disjoint from the image of the selected lift labels. On its column this excludes the false axis of each selected lift, and on its row it excludes the true axis of each selected lift.

At the central lift, either incident flip commutes past e and cancels the corresponding flip from the branch to the middle. The branch, the middle, and their two e-lifts would form a selected coordinate square, which balance forbids.

Two distinct middles in a common column have a common branch p. Their directions a and b from p are distinct. With both e-lifts selected, a continuation along b from the a-middle lift would give two selected three-step words a,e,b and b,e,a from p to the same point. Balance forces equal first directions, contradicting a and b being distinct. The argument for a common row uses the other branch class.

Injectivity counts each excluded label as a distinct axis. The number of selected internal continuation directions is bounded by six minus the number of selected labels, or four minus the number of other selected middles in the row and column using e. The statement holds for every exterior e on the same ambient support.

In the singleton-trace branch of Hong–Wu–Xia Problem 2, the rule applies conditionally when the fifteen-point trace is the once-subdivided K3,3 on six coordinate axes. It constrains the possible exterior continuations of that trace. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridExterior.exterior_lift_direction_exclusion`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridExterior.selectedLiftLabels`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](../BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity](../CubicalSubdivisionRigidity.md)
