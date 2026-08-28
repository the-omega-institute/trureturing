# Finite-Time Escape Decidability

## Abstract

Finite range scans decide all three finite-time relations.

**Definition 1.1 (Finite scans construct all three decision procedures).**

$$\forall X, O: \operatorname{Type}, [\operatorname{DecidableEq}\left(O\right)],\\{}q: X \to O, \tau: X \to X,\\{}N, N'\in \mathbb{N}, h: N \leq N', x, y\in X,\\{}\operatorname{Decidable}\left(\operatorname{TimeExpansionEscape}\left(q, \tau, N, N', h, x, y\right)\right) \times\\{}\operatorname{Decidable}\left(\operatorname{PredictionEscape}\left(q, \tau, N, x, y\right)\right) \times\\{}\operatorname{Decidable}\left(\operatorname{timeProjection}\left(q, \tau, N, x\right) = \operatorname{timeProjection}\left(q, \tau, N, y\right)\right).$$

*Formalization.* `D5/S3/ConceptDynamics/TimeProjection/FiniteTimeEscapeDecidability.finite_time_escape_decidability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

TimeExpansionEscape is independently defined by agreement through the old horizon and a separating coordinate in the added interval. It is not defined through ExpansionEscape.

The construction uses Finset.range (N + 1) and Finset.range (N' + 1) to decide the old-horizon universal clause, the bounded witnesses, and pointwise equality of the projected functions.

Only decidable equality on the output carrier is assumed; the state and output carriers need neither finiteness nor global inhabitants.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TimeProjection/FiniteTimeEscapeDecidability.finite_time_escape_decidability`
- Dependency: [D5/S3/ConceptDynamics/TimeProjection/PredictionExpansionEscape](PredictionExpansionEscape.md)
