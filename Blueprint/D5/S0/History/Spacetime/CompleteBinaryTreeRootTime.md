# Complete Binary Tree Root Time

## Abstract

A finite complete binary tree propagates leaf times by a unit delay per edge.

**Proposition 1.1 (Root time is the maximum of leaf time plus depth).**

$$t_{\mathrm{root}} = \max_{i} (t_{i} + \operatorname{depth}_{i}).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Spacetime/CompleteBinaryTreeRootTime.rootTime_eq_max_leaf_time_add_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The CompleteBinaryTree carrier has integer-valued leaves and exactly two children at every internal node. The root rule takes the larger child time and adds one. Its finite leaf records carry both the input time and the number of edges from the current root. The theorem proves that the root time is the maximum of time plus depth over those records.

The proof is structural induction. At an internal node, every leaf record receives one additional depth unit, and translation by one commutes with the finite maximum. The root time is computed from the children up, and leaf scores accumulate depth from the root down. Every complete tree has at least one leaf. The statement concerns this construction tree only: archived events outside the tree can have later times, so this is not the maximum of the entire archive or a physical time law.

## References

- Truth anchor: `D5/S0/History/Spacetime/CompleteBinaryTreeRootTime.rootTime_eq_max_leaf_time_add_depth`
