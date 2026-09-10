# Coordinate and Attribute Tuples

## Abstract

Finite-dimensional coordinates and four event attributes have exact literal HF tuple codes.

**Definition 1.1 (An arbitrary fixed finite dimension).**

Lean statement: `D5/S0/History/Spacetime/CoordinateEncoding.position_code_equiv`

*Formalization.* `D5/S0/History/Spacetime/CoordinateEncoding.position_code_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A recursive tuple grammar contains exactly the prescribed number of integer entries, followed by an empty-set terminator. The representation applies Mathlib's Fin.consEquiv and the proved integer coding equivalence.

**Definition 1.2 (All four attributes are preserved).**

Lean statement: `D5/S0/History/Spacetime/CoordinateEncoding.attributes_code_equiv`

*Formalization.* `D5/S0/History/Spacetime/CoordinateEncoding.attributes_code_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tuple stores time, position, sign and source tree in that order. Its sign component is exactly the integer code of positive or negative one. Component equivalences supply both round trips without assumed compatibility fields.

## References

- Truth anchor: `D5/S0/History/Spacetime/CoordinateEncoding.attributes_code_equiv`
- Truth anchor: `D5/S0/History/Spacetime/CoordinateEncoding.position_code_equiv`
- Dependency: [D5/S0/History/Spacetime/ArchiveCarrier](ArchiveCarrier.md)
- Dependency: [D5/S0/History/Spacetime/IntegerEncoding](IntegerEncoding.md)
