# The exhaustive certificate cases and their physical transfer

## Abstract

The exhaustive certificate cases and their physical transfer

**Theorem 1.1 (Existence in the smaller dimension).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.exists_spectral_budget_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.exists_spectral_budget_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When twice the working dimension is at most total capacity, nonnegative traces bounded by their capacities and summing to the dimension admit a certificate. The cases are zero dimension, excess deficits, a saturated trace, a zero trace, and the strict direct or complementary equations.

**Theorem 1.2 (Every certificate gives a greatest spectral value).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.spectral_budget_certificate_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.spectral_budget_certificate_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For admissible trace data, any certificate supplies the greatest feasible spectral score. Saturated and zero faces use the common binary optima of the two objectives, and strict certificates use the original-label optima.

**Theorem 1.3 (Physical attainment via the exact range).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.complete_budget_of_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.complete_budget_of_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The range equality turns the spectral optimum into a greatest pinching gain divided by the input rank. The coherent record identities give the mutual information and conditional entropy extrema. A feasible law has an attaining input, while any admissible input supplies positive effects whose trace and rank bounds imply feasibility.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.complete_budget_of_geometry`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.exists_spectral_budget_certificate`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly.spectral_budget_certificate_maximum`
- Dependency: [D5/S3/Quantum/Measurement/Auric/DisjointPhysicalBudget](DisjointPhysicalBudget.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/StrictCertificateBudgets](StrictCertificateBudgets.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/UnequalBlockBoundary](UnequalBlockBoundary.md)
