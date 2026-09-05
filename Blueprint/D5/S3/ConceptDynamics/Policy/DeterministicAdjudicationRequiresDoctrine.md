# Deterministic Adjudication Requires Additional Doctrine

## Abstract

Two distinct licensed outcomes require a distinguishing doctrine input beyond their common public-law value.

**Definition 1.1 (Additional adjudication doctrine).**

Lean statement: `D5/S3/ConceptDynamics/Policy/DeterministicAdjudicationRequiresDoctrine.AdjudicationDoctrine`

*Formalization.* `D5/S3/ConceptDynamics/Policy/DeterministicAdjudicationRequiresDoctrine.AdjudicationDoctrine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier records exactly the six source alternatives: priority, equity, a historical anchor, value weights, a randomized selection, or a finer fact concept.

**Theorem 1.2 (Distinct licensed outcomes require additional doctrine).**

$$\begin{aligned}\forall Case, PublicFact, Outcome, Weight, Seed, FineFact: \operatorname{Type},\\publicLaw: Case \to PublicFact, admissible: Case \to \operatorname{Prop},\\permitted: Case \to \left(Outcome \to \operatorname{Prop}\right), b: PublicFact,\\y0, y1: Outcome,\\(y0 \neq y1 \land (\exists x0: Case, admissible\left(x0\right) \land publicLaw\left(x0\right) = b \land permitted\left(x0, y0\right)) \land (\exists x1: Case, admissible\left(x1\right) \land publicLaw\left(x1\right) = b \land permitted\left(x1, y1\right))) \Rightarrow\\(\neg(\exists ! y: Outcome, \exists x: Case, admissible\left(x\right) \land publicLaw\left(x\right) = b \land permitted\left(x, y\right)) \land \neg(\exists publicAdjudicator: PublicFact \to \left(Outcome \to \operatorname{Prop}\right), \operatorname{RightUnique}\left(publicAdjudicator\right) \land publicAdjudicator\left(b, y0\right) \land publicAdjudicator\left(b, y1\right)) \land (\forall adjudicator: PublicFact \times \operatorname{AdjudicationDoctrine}\left(Case, Outcome, Weight, Seed, FineFact\right) \to \left(Outcome \to \operatorname{Prop}\right), \operatorname{RightUnique}\left(adjudicator\right) \Rightarrow \forall d0, d1: \operatorname{AdjudicationDoctrine}\left(Case, Outcome, Weight, Seed, FineFact\right), (adjudicator\left((b, d0), y0\right) \land adjudicator\left((b, d1), y1\right)) \Rightarrow d0 \neq d1)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Policy/DeterministicAdjudicationRequiresDoctrine.deterministic_adjudication_requires_additional_doctrine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The permitted-outcome predicate is built directly from admissibility, the public-law readout, and the permission relation. Two distinct witnesses rule out a unique outcome.

A right-unique relation on the public-law value alone cannot realize both witnesses. After the doctrine channel is added, right uniqueness forces the two doctrine inputs to differ.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Policy/DeterministicAdjudicationRequiresDoctrine.AdjudicationDoctrine`
- Truth anchor: `D5/S3/ConceptDynamics/Policy/DeterministicAdjudicationRequiresDoctrine.deterministic_adjudication_requires_additional_doctrine`
- Dependency: [D5/S3/ConceptDynamics/Policy/DiscretionaryOutcomeNonuniqueness](DiscretionaryOutcomeNonuniqueness.md)
