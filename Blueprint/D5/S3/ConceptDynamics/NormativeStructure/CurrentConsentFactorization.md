# Current Consent Factorization

## Abstract

Non-factorization of current consent rules out exact systems using only history.

**Theorem 1.1 (Current consent cannot be recovered from history alone).**

$$\forall X : Type, H : Type,\\{}Hnow: X \to H, Cnow: X \to Bool,\\{}\neg \operatorname{Refines}(Cnow, Hnow) \Rightarrow\\{}\neg \exists J, J: X \to Bool, \operatorname{Refines}(J, Hnow) \land J = Cnow.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/CurrentConsentFactorization.current_consent_not_history_only` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier, history readout, and current-consent readout are independent source primitives on the canonical Concept carrier.

The premise states publicly that current consent does not refine through history. The conclusion quantifies a history-factoring system and requires exact equality with current consent, then rules out that pair.

The proof composes the proposed system factor with its exact-response equality, contradicting the non-factorization premise. No object is defined from the nonexistence target.

The search found no exact frozen current-consent theorem; the pinned Refines factorization relation is applied directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/CurrentConsentFactorization.current_consent_not_history_only`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
