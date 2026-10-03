# Measurable Matrix History Density

## Abstract

Positive finite-dimensional matrix-valued measures admit a common scalar density.

**Definition 1.1 (Positive matrix-valued history measure).**

Lean statement: `D5/S3/Quantum/Measurement/MeasurableInstrumentHistory.PositiveHistoryMeasure`

*Formalization.* `D5/S3/Quantum/Measurement/MeasurableInstrumentHistory.PositiveHistoryMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate complex measures form a positive semidefinite matrix on every measurable event. The finite scalar measure is their trace on those events.

**Theorem 1.2 (Common density with a fixed null-set value).**

Lean statement: `D5/S3/Quantum/Measurement/MeasurableInstrumentHistory.positive_history_density`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/MeasurableInstrumentHistory.positive_history_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate absolute continuity follows when a positive event matrix has zero trace. Signed Radon-Nikodym derivatives represent its real and imaginary entries on every event.

A countable dense family of rational-complex vectors tests positivity simultaneously almost everywhere. Continuity extends the quadratic-form inequalities to all vectors. One measurable null set carries a fixed positive trace-one matrix; coordinate integral uniqueness determines the density almost everywhere.

**Theorem 1.3 (The scalar trace measure is derived from the coordinates).**

Lean statement: `D5/S3/Quantum/Measurement/MeasurableInstrumentHistory.positive_history_density_from_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/MeasurableInstrumentHistory.positive_history_density_from_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real diagonal coordinate measures sum to a nonnegative signed measure, whose finite positive measure has the eventwise matrix trace as its value. The common density and its almost-everywhere uniqueness then apply to these derived coordinates.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/MeasurableInstrumentHistory.PositiveHistoryMeasure`
- Truth anchor: `D5/S3/Quantum/Measurement/MeasurableInstrumentHistory.positive_history_density`
- Truth anchor: `D5/S3/Quantum/Measurement/MeasurableInstrumentHistory.positive_history_density_from_coordinates`
