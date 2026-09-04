# Commuting Completion Exchange Realization

## Abstract

The FourState countermodel realizes a discrete FLOW/FLOW/CUT kernel.

**Definition 1.1 (Concrete completion realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutingCompletionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutingCompletionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The primitive realization assigns the two source maps to the FLOW slots and the source predicate to the CUT slot.

**Theorem 1.2 (Countermodel realization equivalence).**

$${\neg \operatorname{Commute}\left(counterexampleF, counterexampleG\right) \land \neg \operatorname{KernelEquivalent}\left(\operatorname{predictiveProjection}\left(counterexampleF, \operatorname{predictiveProjection}\left(counterexampleG, counterexampleReadout\right)\right), \operatorname{predictiveProjection}\left(counterexampleG, \operatorname{predictiveProjection}\left(counterexampleF, counterexampleReadout\right)\right)\right)} \iff commutingCompletionArena.Law(commutingCompletionRealization).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfolding identifies both negated source clauses with the realization law.

**Theorem 1.3 (Four kernel classes).**

$$(Finset.univ.image((state: FourState \mapsto (counterexampleF\left(state\right), counterexampleG\left(state\right), counterexampleReadout\left(state\right))))).card = 4.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_partition_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exhaustive FourState evaluation gives four distinct signatures.

**Theorem 1.4 (Private pair separation).**

$$\neg commutingCompletionRealization.toPrimitiveBundle.agrees(FourState.a, FourState.b).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_private_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second flow sends a and b to different states.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_partition_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_private_pair`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutingCompletionRealization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange](../InformationEscapeArenas/CommutingCompletionExchange.md)
