# Finite Matrix Path Transport

## Abstract

Finite matrix transport composes along vertex paths and gauge factors telescope to the endpoints.

**Definition 1.1 (Path endpoint).**

Lean statement: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathEnd`

*Formalization.* `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathEnd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A start vertex and list of successive vertices determine the terminal vertex.

**Definition 1.2 (Finite path transport).**

Lean statement: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathTransport`

*Formalization.* `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathTransport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Invertible edge matrices are multiplied in reverse order so the first edge acts first on a column state.

**Definition 1.3 (Gauge-transformed edge transport).**

Lean statement: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.gaugeEdgeTransport`

*Formalization.* `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.gaugeEdgeTransport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each edge matrix is conjugated by the gauges at its target and source.

**Theorem 1.4 (Path append composition).**

Lean statement: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathTransport_append`

*Formalization.* `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathTransport_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transport of appended path segments is the later transport multiplied by the earlier transport.

**Theorem 1.5 (Gauge factors telescope).**

Lean statement: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathTransport_gauge`

*Formalization.* `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathTransport_gauge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All interior vertex gauges cancel and only endpoint factors remain.

**Theorem 1.6 (Loop holonomy is gauge conjugate).**

Lean statement: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.loopTransport_gauge_conjugate`

*Formalization.* `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.loopTransport_gauge_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A closed path transforms by conjugation at its base vertex.

**Theorem 1.7 (One-edge transport).**

Lean statement: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.one_edge_path_transport`

*Formalization.* `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.one_edge_path_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A path containing one target vertex evaluates to its single edge matrix.

## References

- Truth anchor: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathEnd`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathTransport`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.gaugeEdgeTransport`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathTransport_append`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.pathTransport_gauge`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.loopTransport_gauge_conjugate`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.one_edge_path_transport`
