# Tree Markov replacement stability

## Abstract

Finite normalized tree replacement schedules telescope in total variation. The edge replacements contribute once each, while a node discrepancy is charged once for every non-root child replacement. The resulting degree-weighted bound is capped by one, and the same-node-marginal specialization removes the node term.

The formal source is an explicit finite replacement interface. It records nonnegative normalized source and target laws, a finite hybrid path, local edge and node replacement bounds, and the degree charge accounting. The telescope is proved from the finite total-variation triangle inequality; the cap uses the finite probability unit bound.

**Theorem 1.1 (Degree-weighted tree replacement bound).**

Lean statement: `D5/S3/TotalVariation/TreeMarkovStability.tree_markov_total_variation_bound`

*Proof.* The finite hybrid path is summed by induction. Finite sum exchange and the charge accounting identify the path budget with the edge sum plus `sum_v (degree v - 1) * nodeError v`. ∎

**Theorem 1.2 (Capped degree-weighted bound).**

Lean statement: `D5/S3/TotalVariation/TreeMarkovStability.tree_markov_capped_total_variation_bound`

*Proof.* Apply the probability unit bound to the normalized endpoints and take the minimum with the telescope. ∎

**Theorem 1.3 (Same-node-marginal bound).**

Lean statement: `D5/S3/TotalVariation/TreeMarkovStability.tree_markov_capped_same_node_marginal_bound`

*Proof.* Zero node errors remove the degree-weighted term before applying the same cap. ∎

**Theorem 1.4 (Universal sharpness of edge coefficient one).**

Lean statement: `D5/S3/TotalVariation/TreeMarkovStability.edge_coefficient_one_sharp`

*Proof.* The two point masses on the diagonal Bool pairs have total variation one. Hence any universal coefficient strictly below one fails on this two-node edge witness. ∎

## Boundary

The module proves the replacement and charge layer. A separate source-level construction is still required to instantiate its schedule from arbitrary finite trees, normalized conditional kernels, zero-mass rows, and the source-compatible node and edge marginal interfaces of Theorem 9.2.

## References

- Truth anchor: `D5/S3/TotalVariation/TreeMarkovStability.tree_markov_capped_total_variation_bound`
- Truth anchor: `D5/S3/TotalVariation/TreeMarkovStability.tree_markov_capped_same_node_marginal_bound`
- Truth anchor: `D5/S3/TotalVariation/TreeMarkovStability.edge_coefficient_one_sharp`
- Dependency: [D5/S3/TotalVariation/Metric](Metric.md)
