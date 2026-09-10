# Legal Archive Records

## Abstract

Legal finite graph records reconstruct full causal archives and preserve their time constraints.

**Definition 1.1 (Archive fields are exactly recoverable).**

Lean statement: `D5/S0/History/Spacetime/ArchiveRecordEncoding.archive_record_equiv`

*Formalization.* `D5/S0/History/Spacetime/ArchiveRecordEncoding.archive_record_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Record legality requires a total single-valued attribute graph, a relation whose endpoints are archived, irreflexivity, transitivity and strict increase of decoded integer time. Reconstruction uses the unique graph values to recover each dependent attribute function.

**Definition 1.2 (Literal HF tuples have an independent legality predicate).**

Lean statement: `D5/S0/History/Spacetime/ArchiveRecordEncoding.archive_code_equiv`

*Formalization.* `D5/S0/History/Spacetime/ArchiveRecordEncoding.archive_code_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record becomes a Kuratowski tuple of the event set, attribute graph and causal graph. Its grammar is specified directly on those components. Encoding and decoding are inverse on every legal record, so code equality reflects complete archive equality. Current regions remain a separate component of the context representation.

## References

- Truth anchor: `D5/S0/History/Spacetime/ArchiveRecordEncoding.archive_code_equiv`
- Truth anchor: `D5/S0/History/Spacetime/ArchiveRecordEncoding.archive_record_equiv`
- Dependency: [D5/S0/History/Spacetime/CoordinateEncoding](CoordinateEncoding.md)
- Dependency: [D5/S0/History/Spacetime/FiniteGraphEncoding](FiniteGraphEncoding.md)
