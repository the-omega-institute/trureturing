# Defect Decomposition for Projected Updates

## Abstract

A Lipschitz update splits the total projection defect into two component defects.

**Theorem 1.1 (A Lipschitz update splits the total projection defect).**

$$\forall E,\ d(projectOutput(updateHigh(diagHigh(E))), updateLow(diagLow(projectTable(E)))) \leq d(projectOutput(updateHigh(diagHigh(E))), updateLow(projectOutput(diagHigh(E)))) + K d(projectOutput(diagHigh(E)), diagLow(projectTable(E))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/DefectDecomposition.defect_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Insert the low-level update of the projected high-level diagonal between the projected high-level update and the low-level update of the projected table diagonal. The metric triangle inequality gives the two component distances, and the Lipschitz bound on the low-level update controls the second distance by K times the diagonal-projection defect.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/DefectDecomposition.defect_decomposition`
