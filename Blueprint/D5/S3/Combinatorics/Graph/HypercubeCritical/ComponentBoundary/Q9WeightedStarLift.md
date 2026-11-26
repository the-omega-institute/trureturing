# The six-axis core and three star axes

## Abstract

Weighted Huang boundary kernels of the star lift

**Definition 1.1 (Vacuum and singleton layers).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift.starLift`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift.starLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let M and B occupy opposite parities of the six-axis cube. The lift retains M at the all-true star vertex and M union B at each vertex with one false star bit. The boundary kernel consists of functions supported in the input set whose Huang images are supported in the output set. For an input of fixed parity, the output set is the opposite parity of the retained lift.

**Theorem 1.2 (The vacuum toggles cube parity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift.parity_append_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift.parity_append_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three all-true vacuum bits change the parity of the six-axis vertex. Each singleton has two true bits and preserves its parity.

**Definition 1.3 (Both lifted parities recover the base kernel).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift.weightedStarLiftEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift.weightedStarLiftEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Work over any field. Write Hx for the weighted base action, w for the three star weights, W for their sum of squares and sigma for the parity sign on M. Assume W is nonzero. The parity without a vacuum slice sends a base vector m to singleton slices w_i m. The vacuum parity sends m to vacuum slice m and singleton slices w_i sigma Hx m / W. Both maps are linear equivalences with the kernel of the rows outside B on base functions supported in M.

The signed doubleton rows give w_i s_j = w_j s_i for each pair of axes. Any nonzero w_i recovers the common slice, including when another weight vanishes. In the vacuum parity, the vacuum rows outside M force that common slice to be sigma Hx m / W. The Huang square identity then makes each singleton row outside M vanish. The nine-axis row uses the six-axis Huang action plus the base parity sign times the three-axis Huang action.

The 72-vertex construction in the study of Hong–Wu–Xia Problem 2 uses a twenty-vertex core with eight branch and twelve middle vertices. Its three singleton layers contain the whole core and its vacuum layer contains the twelve middle vertices. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift.parity_append_empty`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift.starLift`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift.weightedStarLiftEquiv`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](Q9IsotropicHuang.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridSignedCompression](SixAxisGridSignedCompression.md)
