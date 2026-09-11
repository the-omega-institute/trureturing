# Empty

## Abstract

Every map from Empty equals its eliminator.

**Theorem 1.1 (Elimination of an empty domain).**

$$\forall f: \mathit{Empty} \to \alpha, f= \mathit{elim}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcLanguageSupport/Empty.eq_elim` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every target sort and every function from Empty to it, the function equals Empty.elim.

This equality supports empty-language elimination in the retained first-order semantics route. It does not construct a model or eliminate all CSA definitions.

Retained mathematical command: upstream line 9. The selected definitions and proofs retain Foundation revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. Attribution, the complete Apache-2.0 license and the replacement condition are in Library/ConceptDynamics/foundation2026firstorder.md.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ZfcLanguageSupport/Empty.eq_elim`
