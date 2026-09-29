# InfiniteCalibrationFamily

## Abstract

The calibration consumer observes a real control witness over the full infinite calibration domain.

**Definition 1.1 (Real parameters and controls).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.signature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.signature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Params is the dependent triple (a, δ, b) of real numbers. State and Output are both the entire real line, with one Unit role and Empty anchors. There is no finite truncation, sampling or replacement by a finite witness type.

**Definition 1.2 (Identity control observation).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.actual`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.actual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual readout returns the real control k itself at every parameter triple. Distinct real states can therefore supply the required actual observational dependence.

**Definition 1.3 (Zero control intervention).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.rejected`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.rejected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rejected readout sends every real control to zero. InfiniteScalarControl requires strict positivity of the observed control, so the Reg proof can refute the intervened law at an admissible parameter triple. The name rejected is an operand definition; the law-breaking proof lives in Reg.

**Definition 1.4 (Full calibration existence law).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.arena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.arena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law retains all real a, δ, b and all seven premises: 0 < a < 1, 0 < δ, δ < (1-a)/4, δ < (1-a²)/16, 0 < b and b < 1-a/(1-δ). It asks for a real k whose observed value satisfies the original InfiniteScalarControl. That predicate retains strict physicality and analyticity on the whole interval (a,1), and the equivalence between simultaneous value/derivative calibration jets and the positive-natural nodes 1-b/n.

The source declaration is `D5/S3/Quantum/Information/InfiniteCalibrationControl.result`. Its Reg mirror retains the full source statement, uses the identity bridge, and supplies actual-law, variation, sole-role sensitivity and dependence proofs. Source binding selects the three real parameters and the existential control occurrence; it does not replace the infinite real domain with the counterexample's single parameter triple.

These are repository-derived consumer definitions, not new proven theorem wrappers. No novelty, coverage or freeze status is asserted. The raw open residual records unknown residual information and provides no infinity, undecidability or completeness certificate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.actual`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.arena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.rejected`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily.signature`
- Truth anchor: `D5/S3/Quantum/Information/InfiniteCalibrationControl.result`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/DependentFamily](DependentFamily.md)
- Dependency: [D5/S3/Quantum/Information/InfiniteCalibrationControl](../../Quantum/Information/InfiniteCalibrationControl.md)
