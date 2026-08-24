# Global Frame Coboundary Criterion

## Abstract

A nonvanishing frame descends from local bases exactly when their unit-valued transition data is a coboundary.

**Theorem 1.1 (A global frame exists exactly for coboundary transition data).**

$$\begin{gathered}\forall I, X, U: \operatorname{Type},\\{}[\operatorname{Group}\left(U\right)],\\{}overlap: I \to I \to X \to \operatorname{Prop},\\{}g: I \to I \to X \to U,\\{}(\exists a: I \to X \to U,\\{}\forall i, j, x, \operatorname{overlap}\left(i, j, x\right) \Rightarrow a_{i}(x) = g_{i, j}(x) a_{j}(x)) \iff\\{}(\exists h: I \to X \to U,\\{}\forall i, j, x, \operatorname{overlap}\left(i, j, x\right) \Rightarrow g_{i, j}(x) = h_{i}(x)^{-1} h_{j}(x)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/GlobalFrameCoboundaryCriterion.global_frame_iff_transition_coboundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The overlap predicate specifies where two local trivializations meet. All displayed coefficient values lie in a group of units, so they represent nonvanishing rescalings of the chosen local bases. Compatibility is stated directly on every overlap.

From compatible frame coefficients a, take h_i to be the pointwise inverse of a_i. Right cancellation then gives g_ij = h_i^{-1} h_j. Conversely, rescale the i-th local basis by h_i^{-1}; the coboundary equation makes these rescaled bases agree on every overlap.

This is the algebraic descent carrier of the criterion. It is pointwise in the base and therefore applies to unit-valued local functions; no topology-specific regularity assertion is added.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/GlobalFrameCoboundaryCriterion.global_frame_iff_transition_coboundary`
