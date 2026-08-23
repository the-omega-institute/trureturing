# Purity Pythagoras Decomposition

## Abstract

Pairwise orthogonal basis measurements split density-matrix purity excess into visible probability energy and orthogonal residual mass.

**Lemma 1.1 (Every visible measurement is orthogonal to the residual).**

$$\operatorname{RankOneContextFamily}\left(C, d\right) \land \operatorname{RecordMeasurements}\left(C\right) \land \operatorname{PairwiseOrthogonalMeasurements}\left(C\right) \Rightarrow\\{}\forall l, x, s: \operatorname{traceZeroHermitian}\left(d\right), \operatorname{innerR}\left(\operatorname{traceZeroBasisMeasurement}\left(\operatorname{context}\left(C, l\right), x\right), \operatorname{residualVector}\left(C, s\right)\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.measurement_inner_residualVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a finite family of complete rank-one record measurements on the trace-zero Hermitian space. Assume the ranges of the corresponding real orthogonal projections are pairwise orthogonal.

For any chosen context, projected test vector, and state, the real Hilbert--Schmidt inner product of that visible component with the state minus the sum of all visible components is zero. Thus the defined residual lies in the orthogonal complement of every visible measurement image.

Symmetry and idempotence identify the selected context's contribution with its pairing against the original state, while pairwise orthogonality removes every cross-context contribution.

**Theorem 1.2 (Purity excess splits into visible and residual mass).**

$$\operatorname{NormalizedDensity}\left(\rho, d\right) \land \operatorname{RecordMeasurements}\left(C\right) \land \operatorname{PairwiseOrthogonalMeasurements}\left(C\right) \Rightarrow\\{}\operatorname{ReTr}\left(\rho^{2}\right) - \frac{1}{d} =\\{}\sum_{l} \sum_{j} {\operatorname{basisProbability}\left(\rho, \operatorname{context}\left(C, l\right), j\right) - \frac{1}{d}}^{2} + \operatorname{purityResidual}\left(C, \operatorname{centeredDensity}\left(\rho\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.purity_pythagoras_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a positive semidefinite complex matrix of trace one in dimension d. Centering it by the maximally mixed state produces a trace-zero Hermitian vector whose squared Hilbert--Schmidt norm is the real trace purity minus the inverse dimension.

For each complete rank-one record context, the squared norm of its visible projection is the sum over outcomes of the squared Born probability deviations from the uniform value. Pairwise orthogonality makes these visible energies add without cross terms.

The preceding residual-orthogonality result then gives an exact Pythagorean split: purity excess equals the double sum of visible probability energies plus the squared norm of the remaining component. The family need not be tomographically complete; any unseen mass is retained by the nonnegative residual term.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.measurement_inner_residualVector`
- Truth anchor: `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.purity_pythagoras_decomposition`
- Dependency: [D5/S3/Quantum/Measurement/BasisMeasurementProjection](../Measurement/BasisMeasurementProjection.md)
