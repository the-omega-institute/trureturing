# Retrospective Lookup Failure

## Abstract

Finite table copying has zero retrospective loss but fails non-anticipation.

**Theorem 1.1 (Lookup copying is exact retrospectively but contaminated for anticipation).**

$$\forall Z, Answer: Type, comparison: \operatorname{CopyComparison}(Z, Answer), commitment: \operatorname{CopyCommitment}(Z), \left(\left([\operatorname{Fintype}(Z)] \land [\operatorname{DecidableEq}(Z)]\right) \land \operatorname{IncorporatesTableCopy}(commitment)\right) \Rightarrow \left(\operatorname{retrospectiveLoss}(comparison, \operatorname{tableCopy}(comparison)) = 0 \land \left((\forall z: Z, \neg \operatorname{NonAnticipating}(commitment, z)) \land \left(\neg \left(\operatorname{retrospectiveLoss}(comparison, \operatorname{tableCopy}(comparison)) = 0 \Rightarrow \forall prospectiveGain: (Z \to Answer) \to \mathbb{N}, \operatorname{PositiveProspectiveGain}(prospectiveGain, \operatorname{tableCopy}(comparison))\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure.lookup_copy_zero_loss_and_nonanticipating_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite record type, CopyComparison supplies the observed answer, a Nat-valued pointwise loss, and the self-loss-zero law. The tableCopy is exactly the observed-answer function, and retrospectiveLoss is only the finite sum of those pointwise losses, with no complexity or regularization term.

The self-loss law makes every summand zero, so the lookup copier's total retrospective loss is zero. IncorporatesTableCopy places every record in the commitment's evidence dependency closure; this contradicts the absence-of-dependency clause of NonAnticipating for every record, even when the record was frozen beforehand.

PositiveProspectiveGain is an independent future-evaluation quantity. The zero prospective-gain function witnesses that zero retrospective loss does not entail a strictly positive prospective gain. Concrete Bool/Nat examples separately show exact lookup loss zero and a one-unit loss for a constant wrong copy.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure.lookup_copy_zero_loss_and_nonanticipating_failure`
