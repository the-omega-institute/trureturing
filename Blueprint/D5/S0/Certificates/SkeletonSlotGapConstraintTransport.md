# Slot Gap Constraint Transport

## Abstract

Actual slot runs induce the original finite shared-selection constraints and their terminal observation domains.

**Definition 1.1 (Gap blocks).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.gapBlocks`

*Formalization.* `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.gapBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A gap index k expands to oneZero followed by k zero return blocks.

**Definition 1.2 (Gap code).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.gapCode`

*Formalization.* `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.gapCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two original terminal channels end in one or in one followed by zero.

**Definition 1.3 (Slot readout).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.slotReadout`

*Formalization.* `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.slotReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both readouts come from the original slot and return fields.

**Definition 1.4 (Gap trace).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.traceFrom`

*Formalization.* `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.traceFrom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite fold of the already derived gap maps.

**Theorem 1.5 (Original evaluation agrees with the gap trace).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.eval_gapCode`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.eval_gapCode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction proves the equation for arbitrary gap lists and both terminal channels.

**Definition 1.6 (Variable indexing).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.variableIndex`

*Formalization.* `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.variableIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Standard finite sum and product equivalences assign table and trace coordinates.

**Definition 1.7 (Selection constraint).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.gapSelection`

*Formalization.* `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.gapSelection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing finite-domain Selection type owns the local equation.

**Definition 1.8 (Actual trace color).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.traceColor`

*Formalization.* `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.traceColor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The color is computed from the actual slot witness.

**Definition 1.9 (Induced assignment).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.inducedAssignment`

*Formalization.* `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.inducedAssignment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual table entries and actual prefix states fill the finite variables.

**Theorem 1.10 (Incidence gives the selection equation).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.induced_selection_holds`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.induced_selection_holds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A syntactic prefix-append identity yields the same deterministic local equation used by the checker.

**Definition 1.11 (Observation domains).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.observationDomains`

*Formalization.* `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.observationDomains` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the stated terminal observations restrict trace domains. Unobserved outputs are not copied from the reference machine.

**Theorem 1.12 (Fitted observations give domain membership).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.induced_assignment_in_domains`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.induced_assignment_in_domains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original evaluation equation proves membership without an assumed replacement-machine correctness field.

**Theorem 1.13 (Every fitted slot witness induces a solution).**

Lean statement: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.fitted_slots_induce_selection_solution`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.fitted_slots_induce_selection_solution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the slot-to-CSP transport. Concrete parsing, anchor normalization and evaluation of an external refutation remain separate obligations.

## References

- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.eval_gapCode`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.fitted_slots_induce_selection_solution`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.gapBlocks`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.gapCode`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.gapSelection`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.inducedAssignment`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.induced_assignment_in_domains`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.induced_selection_holds`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.observationDomains`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.slotReadout`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.traceColor`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.traceFrom`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotGapConstraintTransport.variableIndex`
- Dependency: [D5/S0/Certificates/FiniteDomainSelectionRefutation](FiniteDomainSelectionRefutation.md)
- Dependency: [D5/S0/Certificates/SkeletonSlotZeroResponse](SkeletonSlotZeroResponse.md)
