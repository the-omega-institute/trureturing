# Finite Time Projection Restriction Laws

## Abstract

Finite time projections expand into bounded readout equality and restrict exactly along horizon inclusion.

**Theorem 1.1 (Projection expansion, horizon restriction, and the zero-horizon law).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}q: X \to O, tau: X \to X,\\{}N, M: \mathbb{N}, h: N \leq M, x, y: X,\\{}(\operatorname{timeProjection}\left(q, tau, N, x\right) = \operatorname{timeProjection}\left(q, tau, N, y\right) \iff\\{}\forall k: \mathbb{N}, k \leq N \Rightarrow q(\operatorname{timeIter}\left(tau, k, x\right)) = q(\operatorname{timeIter}\left(tau, k, y\right))) \land\\{}\operatorname{restrictTime}\left(h, \operatorname{timeProjection}\left(q, tau, M, x\right)\right) = \operatorname{timeProjection}\left(q, tau, N, x\right) \land\\{}\operatorname{timeProjection}\left(q, tau, 0, x, 0\right) = q(x).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionRestrictionLaws.finite_time_projection_expansion_and_restriction_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of two projections through N is equivalent to equality of their iterated readouts at every natural time k no later than N.

The restriction map preserves the value of every finite index when embedding Fin(N+1) into Fin(M+1). Consequently a longer projection restricts definitionally to the shorter projection, while horizon zero returns the current readout.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionRestrictionLaws.finite_time_projection_expansion_and_restriction_laws`
- Dependency: [D5/S3/ConceptDynamics/TimeProjection/PredictionExpansionEscape](PredictionExpansionEscape.md)
