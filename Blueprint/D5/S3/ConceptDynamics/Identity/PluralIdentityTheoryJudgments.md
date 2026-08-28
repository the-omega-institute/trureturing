# Plural Identity Theory Judgments

## Abstract

Distinct identity concepts can issue opposite judgments under distinct relations.

**Theorem 1.1 (Identity theories can disagree on distinct propositions).**

$$\exists C1, C2: Bool \to Bool,\\{}C1 \neq C2 \land\\{}\operatorname{ConceptIdentity}\left(C1\right) \neq \operatorname{ConceptIdentity}\left(C2\right) \land\\{}\operatorname{ConceptIdentity}\left(C1, false, true\right) \land\\{}\neg \operatorname{ConceptIdentity}\left(C2, false, true\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identity/PluralIdentityTheoryJudgments.identity_theories_can_disagree_on_distinct_propositions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first Boolean concept is constant, while the second is the identity readout. They are different concepts and induce different concept-relative compatibility relations.

The constant concept identifies false with true, whereas the identity concept distinguishes them. Because each judgment names its own compatibility relation, the disagreement is not a proposition and its negation inside one theory.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identity/PluralIdentityTheoryJudgments.identity_theories_can_disagree_on_distinct_propositions`
- Dependency: [D5/S3/ConceptDynamics/Identity/ConceptRelativeIdentity](ConceptRelativeIdentity.md)
