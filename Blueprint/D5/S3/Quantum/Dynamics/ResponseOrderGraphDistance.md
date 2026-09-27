# Response Order and Graph Distance

## Abstract

Positive off-diagonal couplings first appear at the graph distance.

**Definition 1.1 (The coupling graph).**

$$\operatorname{couplingGraph}(H).\operatorname{Adj}(i, j) \iff i \neq j \land (0 < H_{i j} \lor 0 < H_{j i}).$$

*Formalization.* `D5/S3/Quantum/Dynamics/ResponseOrderGraphDistance.couplingGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph joins distinct vertices whenever the corresponding coupling entry is positive.

**Theorem 1.2 (The first nonzero power is the graph distance).**

$$H \in \mathbb{R}^{d \times d}, \forall i, j, H_{i j} = H_{j i}, \forall i, j, i \neq j \Rightarrow 0 \leq H_{i j},\\{}i \neq j, \operatorname{Reachable}(\operatorname{couplingGraph}(H), i, j) \Rightarrow (\forall n < \operatorname{dist}(\operatorname{couplingGraph}(H), i, j), {H^{n}}_{j i} = 0) \land 0 < {H^{\operatorname{dist}(\operatorname{couplingGraph}(H), i, j)}}_{j i}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a symmetric matrix whose off-diagonal entries are nonnegative, every power below the distance between reachable distinct vertices has zero cross-entry, while the power at that distance has a strictly positive cross-entry.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/ResponseOrderGraphDistance.couplingGraph`
- Truth anchor: `D5/S3/Quantum/Dynamics/ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance`
