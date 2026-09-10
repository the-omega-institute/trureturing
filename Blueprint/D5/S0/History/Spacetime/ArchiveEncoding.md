# Context and Selection Representation

## Abstract

Finite contexts and rich selections correspond exactly to structurally legal HF records.

**Definition 1.1 (An exact context representation).**

Lean statement: `D5/S0/History/Spacetime/ArchiveEncoding.context_code_equiv`

*Formalization.* `D5/S0/History/Spacetime/ArchiveEncoding.context_code_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The independent context grammar specifies an event set, legal attribute and causal graphs, and a current region contained in the event set. Graph reconstruction restores the complete archive. Both round trips and equality reflection hold for the actual context.

**Definition 1.2 (Selections preserve both containment guards).**

Lean statement: `D5/S0/History/Spacetime/ArchiveEncoding.rich_code_equiv`

*Formalization.* `D5/S0/History/Spacetime/ArchiveEncoding.rich_code_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A rich record appends a selected HF set contained in the current region. Reconstruction keeps the archive, current region and selection distinct. These predicates are specified through tuple structure, graph legality and membership, independently of encoder ranges.

This batch proves finite representation in Lean. Infinite rational Cauchy sequences, arithmetic quotients and a first-order definition-elimination or conservativity bridge are outside these declarations.

## References

- Truth anchor: `D5/S0/History/Spacetime/ArchiveEncoding.context_code_equiv`
- Truth anchor: `D5/S0/History/Spacetime/ArchiveEncoding.rich_code_equiv`
- Dependency: [D5/S0/History/Spacetime/ArchiveRecordEncoding](ArchiveRecordEncoding.md)
