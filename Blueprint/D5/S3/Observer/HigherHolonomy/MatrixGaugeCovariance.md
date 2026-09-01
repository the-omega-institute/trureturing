# Gauge-Invariant Finite Loop Observables

## Abstract

Trace and determinant of finite matrix loop holonomy are invariant under vertex gauge transport.

**Definition 1.1 (Transport trace).**

Lean statement: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.transportTrace`

*Formalization.* `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.transportTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite path is observed through the trace of its matrix transport.

**Definition 1.2 (Transport determinant).**

Lean statement: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.transportDeterminant`

*Formalization.* `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.transportDeterminant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite path is observed through the determinant of its matrix transport.

**Theorem 1.3 (Trace is conjugacy invariant).**

Lean statement: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.trace_unit_conjugate`

*Formalization.* `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.trace_unit_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating a matrix unit by another unit preserves its trace.

**Theorem 1.4 (Determinant is conjugacy invariant).**

Lean statement: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.determinant_unit_conjugate`

*Formalization.* `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.determinant_unit_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating a matrix unit by another unit preserves its determinant.

**Theorem 1.5 (Loop trace is gauge invariant).**

Lean statement: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.loop_transport_trace_gauge_invariant`

*Formalization.* `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.loop_transport_trace_gauge_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Endpoint gauge covariance becomes trace invariance on every closed path.

**Theorem 1.6 (Loop determinant is gauge invariant).**

Lean statement: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.loop_transport_determinant_gauge_invariant`

*Formalization.* `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.loop_transport_determinant_gauge_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Endpoint gauge covariance becomes determinant invariance on every closed path.

**Theorem 1.7 (Empty-loop determinant).**

Lean statement: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.transportDeterminant_empty`

*Formalization.* `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.transportDeterminant_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant observable of the identity path equals one.

## References

- Truth anchor: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.transportTrace`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.transportDeterminant`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.trace_unit_conjugate`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.determinant_unit_conjugate`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.loop_transport_trace_gauge_invariant`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.loop_transport_determinant_gauge_invariant`
- Truth anchor: `D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.transportDeterminant_empty`
- Dependency: [D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport](FiniteMatrixTransport.md)
