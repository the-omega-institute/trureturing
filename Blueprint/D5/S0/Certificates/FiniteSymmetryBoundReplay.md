# Finite event and partial-assignment interface

## Abstract

Actual events, partial assignments and compatibility

A complete event assigns a value to every original coordinate. A partial event records either an assigned value or an unknown coordinate. Compatibility requires the complete event to agree at every assigned coordinate. These shared definitions are used by the accepted local row DAG and cache association proofs.

**Definition 1.1 (Complete events).**

Lean statement: `D5/S0/Certificates/FiniteSymmetryBoundReplay.Event`

*Formalization.* `D5/S0/Certificates/FiniteSymmetryBoundReplay.Event` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complete event is a function from original coordinates to values.

**Definition 1.2 (Partial assignments).**

Lean statement: `D5/S0/Certificates/FiniteSymmetryBoundReplay.Partial`

*Formalization.* `D5/S0/Certificates/FiniteSymmetryBoundReplay.Partial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each original coordinate holds either a value or none; the entire function is retained in every association.

**Definition 1.3 (Agreement at every assigned coordinate).**

Lean statement: `D5/S0/Certificates/FiniteSymmetryBoundReplay.Compatible`

*Formalization.* `D5/S0/Certificates/FiniteSymmetryBoundReplay.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every recorded value must equal the corresponding value of the actual complete event.

**Definition 1.4 (View a complete event as a partial assignment).**

Lean statement: `D5/S0/Certificates/FiniteSymmetryBoundReplay.completed`

*Formalization.* `D5/S0/Certificates/FiniteSymmetryBoundReplay.completed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every coordinate is assigned its actual value. The local DAG's terminal checker uses this exact completed function.

## References

- Truth anchor: `D5/S0/Certificates/FiniteSymmetryBoundReplay.Compatible`
- Truth anchor: `D5/S0/Certificates/FiniteSymmetryBoundReplay.Event`
- Truth anchor: `D5/S0/Certificates/FiniteSymmetryBoundReplay.Partial`
- Truth anchor: `D5/S0/Certificates/FiniteSymmetryBoundReplay.completed`
