# Language Postprocessing Obstruction

## Abstract

Processing a language readout cannot recover a distinction absent from that readout.

**Theorem 1.1 (Language postprocessing preserves a missing distinction).**

$$\begin{gathered}\forall X, B_{L}, B_{Phi}, Z: \operatorname{Type},\\{}L: X \to B_{L}, Phi: X \to B_{Phi},\\{}\forall x, y: X,\\{}(L(x) = L(y) \land Phi(x) \neq Phi(y)) \Rightarrow \\{}\forall h: B_{L} \to Z, h(L(x)) = h(L(y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Communication/LanguagePostprocessingObstruction.language_postprocessing_preserves_missing_distinction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The language and phenomenon concepts are readouts on the same source carrier. Two public witness states share a language value while having different phenomenon values.

For every output carrier and every function of the language value, equality transport makes the postprocessed outputs equal on the same witnesses.

Thus longer text, richer rhetoric, or recursive interpretation cannot recover the missing distinction when its entire input still factors through the old language readout.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Communication/LanguagePostprocessingObstruction.language_postprocessing_preserves_missing_distinction`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
