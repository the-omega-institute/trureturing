# Intertwining Defect Bounds

## Abstract

The weighted and uniform norm estimates jointly quantify defect propagation.

**Theorem 1.1 (Both propagation bounds hold).**

$$\forall K : Type, X : Type, Y : Type, A, C, T, L, n,\\{}\operatorname{NontriviallyNormedField}(K) \land \operatorname{SeminormedAddCommGroup}(X) \land \operatorname{NormedSpace}(K, X) \land\\{}\operatorname{SeminormedAddCommGroup}(Y) \land \operatorname{NormedSpace}(K, Y) \land A \in \operatorname{ContinuousLinearMap}(K, Y, Y) \land\\{}C \in \operatorname{ContinuousLinearMap}(K, X, Y) \land T \in \operatorname{ContinuousLinearMap}(K, X, X) \land L \in R \land n \in N \Rightarrow\\{}\Vert C \cdot T^{n} - A^{n} \cdot C \Vert \leq \sum_{j=0}^{n-1} \Vert A \Vert^{n-1-j} \cdot \Vert C \cdot T - A \cdot C \Vert \cdot \Vert T \Vert^{j} \land\\{}{\Vert A \Vert \leq L \land \Vert T \Vert \leq L \Rightarrow \Vert C \cdot T^{n} - A^{n} \cdot C \Vert \leq n \cdot L^{n-1} \cdot \Vert C \cdot T - A \cdot C \Vert}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Approximation/IntertwiningDefectBounds.intertwining_defect_propagation_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct is the weighted finite-sum estimate. The second states that uniform bounds on both evolution operators imply the linear-in-time estimate.

Both conjuncts apply the canonical declarations from the existing intertwining-defect family; this module introduces no new mathematical definition.

## References

- Truth anchor: `D5/S3/Observer/Approximation/IntertwiningDefectBounds.intertwining_defect_propagation_bounds`
- Dependency: [D5/S3/Observer/Approximation/IntertwiningDefectPropagation](IntertwiningDefectPropagation.md)
