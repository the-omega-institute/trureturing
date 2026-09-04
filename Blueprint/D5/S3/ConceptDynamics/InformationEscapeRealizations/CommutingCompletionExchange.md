# Commuting Completion Exchange Realization

## Abstract

The FourState countermodel realizes a discrete FLOW/FLOW/CUT kernel.

**Theorem 1.1 (Countermodel realization equivalence).**

$$\operatorname{LegacyPrimitiveRealization}\left(commutingCompletionArena, CommutativityNecessaryStatement, commutingCompletionRealization\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfolding identifies both negated source clauses with the realization law.

**Theorem 1.2 (Four kernel classes).**

$$\operatorname{card}\left(signatureClasses\right) = 4.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_partition_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exhaustive FourState evaluation gives four distinct signatures.

**Theorem 1.3 (Private pair separation).**

$$\operatorname{Not}\left(\operatorname{agrees}\left(commutingCompletionRealization, a, b\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_private_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second flow sends a and b to different states.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_partition_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_private_pair`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange](../InformationEscapeArenas/CommutingCompletionExchange.md)
