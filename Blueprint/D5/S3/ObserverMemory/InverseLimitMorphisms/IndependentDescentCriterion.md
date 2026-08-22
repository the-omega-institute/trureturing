# Independent Inverse-Limit Descent Criterion

## Abstract

Inverse-limit descent and its coordinate-liftable converse have independent premises.

**Theorem 1.1 (Unique descent and the independent coordinate-liftable converse).**

$$\begin{gathered}\forall I, S, T, delta,\\{}((\forall j, i, j \geq i, Q_{j,i} \circ delta_{j} = delta_{i} \circ P_{j,i}) \Rightarrow \exists! Delta, \forall i, \pi_{i}^{T} \circ Delta = delta_{i} \circ \pi_{i}^{S}) \land\\{}(((\forall i, \operatorname{Surjective}(\pi_{i}^{S})) \land \exists Delta, \forall i, \pi_{i}^{T} \circ Delta = delta_{i} \circ \pi_{i}^{S}) \Rightarrow \forall j, i, j \geq i, Q_{j,i} \circ delta_{j} = delta_{i} \circ P_{j,i}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimitMorphisms/IndependentDescentCriterion.inverse_limit_descent_and_independent_converse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S and T be inverse-stage systems over a preordered index type, and let delta be a family of maps between corresponding stages. The first public conjunct assumes finite naturality and concludes the existence and uniqueness of the coordinate-compatible map between compatible-family limits.

The second public conjunct is independent: it assumes every source coordinate projection is surjective and that some map between the compatible-family limits has the coordinate equation. Those two premises recover finite naturality; finite naturality is not an ambient hypothesis of this converse.

The proof imports the canonical inverse-stage and compatible-family types. It applies the frozen predecessor only to the valid forward half, while the converse lifts an arbitrary finite-stage value and uses compatibility of the two limit families.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimitMorphisms/IndependentDescentCriterion.inverse_limit_descent_and_independent_converse`
- Dependency: [D5/S3/ObserverMemory/Refinement/InverseLimitDescent](../Refinement/InverseLimitDescent.md)
