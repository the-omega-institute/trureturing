# Finite Causal Path Bounds

## Abstract

Finite Causal Path Bounds.

**Theorem 1.1 (A legal archive bounds every causal path).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/FiniteCausalPaths.path_length_bound`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/FiniteCausalPaths.path_length_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The archive's strict causal order is converted to Mathlib's partial-order interface, and its set-of-pairs relation series becomes an LTSeries. The direct application of LTSeries.length_lt_card gives at most N minus one edges for N archived events.

**Theorem 1.2 (Bounded sequences characterize transitive closure).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/FiniteCausalPaths.transGen_iff_bounded_series`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/FiniteCausalPaths.transGen_iff_bounded_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any generating subrelation of a legal archive, a nonempty TransGen path is equivalent to a finite relation series with matching endpoints and length at most N minus one. Mathlib's reflexive-transitive list-chain witness supplies the tail after the first edge, and its list-to-series equivalence supplies the series. This is a general finite theorem, including the vacuity of an empty event set.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/FiniteCausalPaths.path_length_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/FiniteCausalPaths.transGen_iff_bounded_series`
- Dependency: [D5/S0/History/Spacetime/ArchiveCarrier](../../../S0/History/Spacetime/ArchiveCarrier.md)
