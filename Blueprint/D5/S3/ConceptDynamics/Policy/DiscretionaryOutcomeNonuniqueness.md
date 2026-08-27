# Discretionary Outcome Nonuniqueness

## Abstract

A public-law fiber with two licensed outcomes does not determine a unique result.

**Theorem 1.1 (A hard case has no uniquely determined outcome).**

$$\begin{aligned}\forall Case, PublicFact, Outcome: \operatorname{Type},\\publicLaw: Case \to PublicFact, admissible: Case \to \operatorname{Prop},\\permitted: Case \to Outcome \to \operatorname{Prop}, b: PublicFact,\\(\exists y0, y1: Outcome, y0 \neq y1 \land (\exists x0: Case, admissible(x0) \land publicLaw(x0) = b \land \operatorname{permitted}\left(x0, y0\right)) \land (\exists x1: Case, admissible(x1) \land publicLaw(x1) = b \land \operatorname{permitted}\left(x1, y1\right))) \implies\\\neg(\exists ! y: Outcome, \exists x: Case, admissible(x) \land publicLaw(x) = b \land \operatorname{permitted}\left(x, y\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Policy/DiscretionaryOutcomeNonuniqueness.discretionary_outcome_nonuniqueness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outcome predicate is constructed directly from admissibility, the public-law readout, and the permission relation.

Two distinct outcomes satisfying that same predicate contradict any claim of unique existence. A determinate choice therefore needs information or a selection rule beyond the public interface.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Policy/DiscretionaryOutcomeNonuniqueness.discretionary_outcome_nonuniqueness`
