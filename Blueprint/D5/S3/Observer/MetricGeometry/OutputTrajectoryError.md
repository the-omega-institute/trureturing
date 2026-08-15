# Output Trajectory Error

## Abstract

Output-orbit error is controlled by readout mismatch and accumulated transition defect.

**Theorem 1.1 (Output trajectory error bound).**

$$\forall k\in\mathbb{N}, \forall y\in Y,\ d_{O}(q(\tau^{k}(y)), o(\sigma^{k}(\pi y))) \leq eta + M\delta \sum_{j=0}^{k-1} L^{j}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/OutputTrajectoryError.output_trajectory_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the abstract update is L-Lipschitz, the abstract readout is M-Lipschitz, every one-step projection defect is at most delta, and every current readout mismatch is at most eta. Then the output error after k updates is bounded by eta plus M times the transition defect accumulated through the finite geometric sum.

The proof first bounds projection-orbit error by induction. At the successor step it inserts the k-fold abstract update of the projected next state. The induction hypothesis controls the first distance, while the imported Lipschitz iterate bound controls the second.

Finally, insert the abstract readout of the projected concrete orbit. The triangle inequality separates current readout mismatch from propagated orbit error, and the M-Lipschitz estimate gives the stated bound. The statement includes k=0, where the geometric sum is empty.

Loogle found the exact supporting declarations LipschitzWith.iterate and LipschitzWith.edist_le_mul_of_le, which are imported and applied. No full-statement match was found by Loogle, LeanSearch, or repository search.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/OutputTrajectoryError.output_trajectory_error`
