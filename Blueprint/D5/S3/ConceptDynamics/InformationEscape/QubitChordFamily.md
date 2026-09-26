# QubitChordFamily

## Abstract

One joint-observation role retains the full quantum chord and spectral Fisher-information law.

**Definition 1.1 (Physical processor states).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.signature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.signature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Params and Role are Unit, anchors are Empty, and State is QuantumChannel (Fin 3 × Fin 2) (Fin 3). Output is a real-linear map from the three-dimensional Bloch space to the two probe-indexed complex 3 × 3 matrices. Neither processors nor outputs are finitely sampled.

**Definition 1.2 (Joint observation).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.actual`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.actual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual readout is jointObservation G. A single role uniformly replaces its three uses in the law: orthogonal-kernel membership of c, membership of v, and the projected Bloch-curve identity. Spectral QFI is retained in the conclusion, not introduced as a separately observed role.

**Definition 1.3 (Bloch-coordinate intervention).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.projectX`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.projectX` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

projectX is the real-linear projection retaining only the x coordinate. It is composed before the physical processor's joint observation; it does not change the original processor, program curve or exactness hypotheses.

**Definition 1.4 (Projected observation family).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.rejected`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.rejected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rejected readout is jointObservation G composed with projectX. The Reg mirror supplies a physical processor and exact curve that refute its law, and distinct processors whose actual joint observations establish dependence. Merely defining this realization is not that proof.

**Definition 1.5 (Complete chord and spectral QFI).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.arena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.arena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law preserves all a with 0 < a < 1, processors G, program curves rho, density hypotheses and exactness for both probes on (2a-1,1). It retains probe density, nonzero chord direction, all bounds on b, the coupled c/v kernel and projection clauses, two-probe affine exactness for every real u, the norm and positivity equivalences with [b,1], trace one, strict interior norm, pure endpoints, and endpoint-overlap bounds. The second conjunct states that for every u in (2a-1,1), if rho is differentiable at u, the lower bound (1-a²)/((1-u)(1+u-2a²)) holds on spectralQFI of the same rho and its derivative.

The preserved source is `D5/S3/Quantum/Information/ActualQubitChordObstruction.actual_two_probe_chord_and_qfi`. Its Reg mirror supplies the full-statement bridge, variation, sole-role sensitivity and actual observational dependence. Source reconstruction ties all three occurrences to the same observation and preserves the original chord-plus-QFI conjunction; it does not claim an independent QFI sensitivity result or exactness for arbitrary signals.

This is repository-derived consumer-model content, with no new theorem wrapper, novelty, coverage or freeze claim. Raw open denotes unknown residual information, not an infinity, undecidability or completeness certificate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.actual`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.arena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.projectX`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.rejected`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.signature`
- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.actual_two_probe_chord_and_qfi`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/DependentFamily](DependentFamily.md)
- Dependency: [D5/S3/Quantum/Information/ActualQubitChordObstruction](../../Quantum/Information/ActualQubitChordObstruction.md)
