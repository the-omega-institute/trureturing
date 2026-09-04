# Commuting Completion Exchange Arena

## Abstract

The completion countermodel law uses two typed flows and one cut.

**Definition 1.1 (Four-state constructor code).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.fourStateCode`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.fourStateCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The code sends the four source constructors to the corresponding elements of Fin four.

**Definition 1.2 (Four-state code inverse).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.fourStateOfCode`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.fourStateOfCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse sends each element of Fin four back to its source-state constructor.

**Definition 1.3 (Four-state equivalence).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.fourStateEquiv`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.fourStateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exhaustive code and inverse form the private equivalence with Fin four.

**Definition 1.4 (Finite four-state carrier).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.instFintypeFourState`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.instFintypeFourState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite instance is obtained through a private equivalence.

**Definition 1.5 (Four-state decidable equality).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.instDecidableEqFourState`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.instDecidableEqFourState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decidable-equality instance is obtained through a private equivalence.

**Definition 1.6 (Completion readout indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.CompletionReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.CompletionReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout index type has two FLOW roles and one CUT role.

**Definition 1.7 (Finite completion readouts).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.instFintypeCompletionReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.instFintypeCompletionReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite instance lists the three readout constructors exhaustively.

**Definition 1.8 (Completion signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.completionSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.completionSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature assigns state-valued outputs to the FLOW slots and a Boolean output to the CUT slot.

**Definition 1.9 (Frozen commutativity statement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.CommutativityNecessaryStatement`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.CommutativityNecessaryStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This alias is definitionally the type of the frozen theorem D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.commutativity_hypothesis_is_necessary.

**Definition 1.10 (Completion countermodel arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.commutingCompletionArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.commutingCompletionArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both completion orders are formed directly from realization FLOW and CUT slots.

**Theorem 1.11 (Commuting-completion arena is nondegenerate).**

$$\operatorname{Nondegenerate}(\operatorname{toArena}(commutingCompletionArena))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.commutingCompletionArena_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four-state source carrier contains a pair of distinct states.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.CommutativityNecessaryStatement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.CompletionReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.commutingCompletionArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.commutingCompletionArena_nondegenerate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.completionSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.fourStateCode`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.fourStateEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.fourStateOfCode`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.instDecidableEqFourState`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.instFintypeCompletionReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.instFintypeFourState`
- Dependency: [D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange](../Completion/CommutingCompletionExchange.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](../InformationEscape/TheoremUnit.md)
