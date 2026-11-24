# Fixed directions and translation periods

## Abstract

Order-three orbits of fixed-axis edges in a balanced cubic support

**Theorem 1.1 (A fixed axis has a multiple of three selected edges).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/OrderThreeFixedAxisEdges.three_dvd_directionEdges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/OrderThreeFixedAxisEdges.three_dvd_directionEdges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a cube symmetry stabilize a balanced induced cubic support. Assume the symmetry and its axis permutation have order dividing three and the axis permutation fixes at most three axes. At a fixed vertex incident to a fixed-axis edge, the three selected directions form an invariant set with at least one fixed element. A nontrivial orbit would require three other directions, so the three directions exhaust the fixed axes.

The other endpoint is fixed and has the same three directions. A second direction then produces a selected coordinate square, forbidden by Huang balance. The symmetry therefore has no fixed selected edge in the chosen axis. An action of order dividing three cannot exchange two endpoints of a fixed edge, so all edge orbits have size three.

**Theorem 1.2 (A fixed axis and an off-axis translation period force divisibility by thirty-six).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/OrderThreeFixedAxisEdges.thirtySix_dvd_card_of_fixed_axis_and_period`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/OrderThreeFixedAxisEdges.thirtySix_dvd_card_of_fixed_axis_and_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the preceding order-three hypotheses, suppose the support lies in Q9 and admits an XOR translation period that changes a coordinate other than the chosen fixed axis. The translation pairs all selected edges in that axis. The edge count is divisible by both two and three. In Q9 the balance identity equates six times the directional edge count with the total size of the support, giving divisibility by thirty-six.

If the coordinate permutation (012)(345) stabilizes the support, axes 6, 7 and 8 are fixed. Every nonzero translation period moves a coordinate outside at least one of those axes. Thus only 72, 108 and 144 pass this divisibility test in the interval 66–144 for the periodic double-three-cycle branch of Hong, Wu and Xia’s Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/OrderThreeFixedAxisEdges.thirtySix_dvd_card_of_fixed_axis_and_period`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/OrderThreeFixedAxisEdges.three_dvd_directionEdges`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](../BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](../BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/HuangTranslationObstruction](HuangTranslationObstruction.md)
