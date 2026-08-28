# Time-Horizon Escape as Expansion Escape

## Abstract

Escape between nested finite horizons is exactly readout expansion escape.

**Theorem 1.1 (Extending a finite horizon realizes expansion escape).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(O\right)],\\{}q: X \to O, tau: X \to X,\\{}N, M: \mathbb{N}, h: N \leq M,\\{}x, y: X,\\{}\operatorname{TimeExpansionEscape}\left(q, tau, N, M, h, x, y\right) \iff\\{}\operatorname{ExpansionEscape}\left(\operatorname{timeProjection}\left(q, tau, N\right), \operatorname{timeProjection}\left(q, tau, M\right), x, y\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TimeProjection/TimeExpansionEscape.time_expansion_escape_iff_expansion_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

TimeExpansionEscape is defined independently: the two states agree at every natural-number coordinate through N, and differ at a witness strictly after N but no later than M.

The forward implication evaluates longer-projection equality at the witness. In reverse, decidable equality on O supports a finite scan of Fin(M+1); shorter-projection equality excludes every returned coordinate at or before N.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TimeProjection/TimeExpansionEscape.time_expansion_escape_iff_expansion_escape`
- Dependency: [D5/S3/ConceptDynamics/TimeProjection/PredictionExpansionEscape](PredictionExpansionEscape.md)
