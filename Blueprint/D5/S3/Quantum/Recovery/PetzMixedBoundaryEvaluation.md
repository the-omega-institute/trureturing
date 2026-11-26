# Logistic evaluation in a mixed output eigenbasis

## Abstract

The logistic evaluation coefficient counts distinct levels of the two output spectra.

**Definition 1.1 (Distinct spectral levels).**

Lean statement: `D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.levelCount`

*Formalization.* `D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.levelCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real family on a finite carrier, count the elements of its image.

**Definition 1.2 (Mixed boundary curve).**

Lean statement: `D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.mixedBoundary`

*Formalization.* `D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.mixedBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The curve uses the reference basis on the left and the source basis on the right. The first product has imaginary output powers followed by a square coefficient matrix. The second starts with another square coefficient matrix and uses the displaced output powers. A rectangular connector joins the eigenbases. In the physical application the square matrices represent the source and reference square roots.

**Theorem 1.3 (Evaluation with distinct levels).**

Lean statement: `D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.mixedBoundary_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.mixedBoundary_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full logistic density times the squared Frobenius norm of the mixed curve is integrable. Its integral times the sum of the distinct level counts minus one bounds the squared norm at time zero. In each entry the two frequency lists have the frequency log(p_j) − log(q_i) in common.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.levelCount`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.mixedBoundary`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation.mixedBoundary_evaluation`
- Dependency: [D5/S3/Analytic/PetzLogisticEvaluation](../../Analytic/PetzLogisticEvaluation.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzSupportedStinespringGram](PetzSupportedStinespringGram.md)
