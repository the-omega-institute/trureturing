# CounterexampleRecord

## Abstract

A finite witness carrier refutes a universal claim through its predicate readout and a reverse bridge.

**Definition 1.1 (Witness arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.WitnessArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.WitnessArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The arena stores a finite carrier, the claim's quantifier domain, a predicate, an embedding, and a predicate decision at each embedded point. Its signature is a single Boolean CUT; its fixed law requires a false readout at some carrier point. The computed realization uses the stored decisions.

**Definition 1.2 (Infinite domain and embedded carrier).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.StrictWitnessArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.StrictWitnessArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The strengthened arena carries proofs that its domain is infinite and its embedding is injective, and coerces to the underlying witness arena.

**Definition 1.3 (Counterexample template).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.counterexampleRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.counterexampleRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The enrolled template accepts a Boolean check and exposes it unchanged as a CUT readout. The arena's computed realization is the required definitional tie for that check. The four-slot interpretation uses the quantifier domain as origin, the finite predicate check as handling, the negated claim as new information, and open as continuation. Full witness registration requires separate judge support.

**Definition 1.4 (Reverse bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.WitnessPrimitiveRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.WitnessPrimitiveRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Prop-valued reverse bridge turns the law of the selected actual realization into the statement. Its theorem-unit conversion consumes a proof of that law, applies the backward bridge, and retains the actual realization's compiled bundle.

**Definition 1.5 (Defining record obligations).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.WitnessArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.WitnessArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law of the arena's computed realization refutes the universal predicate. Given the selected actual realization's law, variation pairs that same law with failure of the constant-true law, and sensitivity witnesses the CUT slot's effect. These generic obligations are Prop-valued definitions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.StrictWitnessArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.WitnessArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.WitnessArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.WitnessPrimitiveRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord.counterexampleRealization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates](RegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](TheoremUnit.md)
