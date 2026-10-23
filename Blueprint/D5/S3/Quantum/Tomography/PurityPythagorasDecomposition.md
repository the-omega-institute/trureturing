# Purity Pythagoras Decomposition

## Abstract

Pairwise orthogonal basis measurements split density-matrix purity excess into visible probability energy and orthogonal residual mass.

**Theorem 1.1 (The complex matrix inner product is a trace pairing).**

$$\forall (d: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (C: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{inner}\left(\mathbb{C}, A, C\right) = \operatorname{trace}\left(\operatorname{conjTranspose}\left(A\right) \cdot C\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.matrix_inner_eq_trace_conjTranspose_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Hilbert–Schmidt inner product of two square complex matrices is the trace of the conjugate transpose of the first times the second. This identity applies in every natural dimension, including zero.

**Theorem 1.2 (Products of Hermitian matrices have real trace).**

$$\forall (d: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (C: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{IsHermitian}\left(A\right)) \Rightarrow ((\operatorname{IsHermitian}\left(C\right)) \Rightarrow (\operatorname{trace}\left(A \cdot C\right) = (\operatorname{re}\left(\operatorname{trace}\left(A \cdot C\right)\right): \mathbb{C})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.trace_mul_real_of_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two Hermitian factors need not commute. Taking the conjugate of their product trace reverses their order, and cyclicity of trace restores the original value. Thus the complex trace is its real part embedded into the complex numbers.

**Theorem 1.3 (Centering removes the squared scalar trace component).**

$$\forall (d: \mathbb{N}), [\operatorname{NeZero}\left(d\right)] \forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{IsHermitian}\left(H\right)) \Rightarrow ((\left\lVert H - \operatorname{smul}\left(\frac{\operatorname{trace}\left(H\right)}{(d: \mathbb{C})}, (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))\right) \right\rVert)^{2} = \operatorname{re}\left(\operatorname{trace}\left(H \cdot H\right)\right) - \frac{(\operatorname{re}\left(\operatorname{trace}\left(H\right)\right))^{2}}{(d: \mathbb{R})})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.centered_hermitian_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Hermitian matrix in nonzero dimension, subtracting trace(H)/d times the identity removes exactly (real trace H) squared divided by d from its squared Hilbert–Schmidt norm. The trace is real and the remaining matrix has trace zero.

**Theorem 1.4 (Measurement energy is the sum of squared trace coordinates).**

$$\forall (d: \mathbb{N}), [\operatorname{NeZero}\left(d\right)] \forall (B: \operatorname{RankOneContext}\left(d\right)), (\operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(B\right)\right)) \Rightarrow (\forall (X: \operatorname{traceZeroHermitian}\left(d\right)), (\left\lVert \sum_{j: \operatorname{Fin}\left(d\right)} (\operatorname{projector}\left(B, j\right) \cdot (X).1.1 \cdot \operatorname{projector}\left(B, j\right)) \right\rVert)^{2} = \sum_{j: \operatorname{Fin}\left(d\right)} ((\operatorname{re}\left(\operatorname{trace}\left((X).1.1 \cdot \operatorname{projector}\left(B, j\right)\right)\right))^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.traceZero_measurement_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A trace-zero Hermitian matrix X is a Hermitian matrix with trace zero, represented by its underlying matrix X.1.1. For a complete rank-one record context, its measured matrix is the sum of P_j X P_j. The rank-one compression identity expresses this as a sum of trace coordinates times P_j, and these projectors are orthonormal in the Hilbert–Schmidt inner product. Its squared norm is therefore the sum of squared real trace coordinates.

**Theorem 1.5 (Orthogonal contexts split every trace-zero Hermitian matrix).**

$$\forall (d: \mathbb{N}), [\operatorname{NeZero}\left(d\right)] \forall (L: Type*), [\operatorname{Fintype}\left(L\right)] \forall (C: (L \to \operatorname{RankOneContext}\left(d\right))), (\forall (l: L), \operatorname{IsRecordMeasurement}\left(\operatorname{projector}\left(C\left(l\right)\right)\right)) \Rightarrow ((\forall (l: L), \forall (k: L), (l \ne k) \Rightarrow (\forall (x: \operatorname{traceZeroHermitian}\left(d\right)), \forall (y: \operatorname{traceZeroHermitian}\left(d\right)), \operatorname{inner}\left(\mathbb{R}, \sum_{j: \operatorname{Fin}\left(d\right)} (\operatorname{projector}\left(C\left(l\right), j\right) \cdot (x).1.1 \cdot \operatorname{projector}\left(C\left(l\right), j\right)), \sum_{j: \operatorname{Fin}\left(d\right)} (\operatorname{projector}\left(C\left(k\right), j\right) \cdot (y).1.1 \cdot \operatorname{projector}\left(C\left(k\right), j\right))\right) = 0)) \Rightarrow (\forall (s: \operatorname{traceZeroHermitian}\left(d\right)), (\left\lVert (s).1.1 \right\rVert)^{2} = \sum_{l: L} ((\left\lVert \sum_{j: \operatorname{Fin}\left(d\right)} (\operatorname{projector}\left(C\left(l\right), j\right) \cdot (s).1.1 \cdot \operatorname{projector}\left(C\left(l\right), j\right)) \right\rVert)^{2}) + (\left\lVert (s).1.1 - \sum_{l: L} (\sum_{j: \operatorname{Fin}\left(d\right)} (\operatorname{projector}\left(C\left(l\right), j\right) \cdot (s).1.1 \cdot \operatorname{projector}\left(C\left(l\right), j\right))) \right\rVert)^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.traceZero_context_pythagoras` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each context is a family of normalized Hermitian rank-one idempotents resolving the identity. A record context has pairwise orthogonal projectors. Assume that the measurement images of distinct contexts are mutually orthogonal for the real Hilbert–Schmidt inner product; this is the expanded hypothesis below. The underlying trace-zero Hermitian matrix then splits into the sum of all measured components and their orthogonal residual. The formula expands each measured component as its compression sum and the residual as the original matrix minus the sum of these components. No positivity or trace-one assumption is imposed on the input.

**Lemma 1.6 (Every visible measurement is orthogonal to the residual).**

$$\operatorname{RankOneContextFamily}\left(C, d\right) \land \operatorname{RecordMeasurements}\left(C\right) \land \operatorname{PairwiseOrthogonalMeasurements}\left(C\right) \Rightarrow\\{}\forall l, x, s: \operatorname{traceZeroHermitian}\left(d\right), \operatorname{innerR}\left(\operatorname{traceZeroBasisMeasurement}\left(\operatorname{context}\left(C, l\right), x\right), \operatorname{residualVector}\left(C, s\right)\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.measurement_inner_residualVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a finite family of complete rank-one record measurements on the trace-zero Hermitian space. Assume the ranges of the corresponding real orthogonal projections are pairwise orthogonal.

For any chosen context, projected test vector, and state, the real Hilbert--Schmidt inner product of that visible component with the state minus the sum of all visible components is zero. Thus the defined residual lies in the orthogonal complement of every visible measurement image.

Symmetry and idempotence identify the selected context's contribution with its pairing against the original state, while pairwise orthogonality removes every cross-context contribution.

**Theorem 1.7 (Purity excess splits into visible and residual mass).**

$$\operatorname{NormalizedDensity}\left(\rho, d\right) \land \operatorname{RecordMeasurements}\left(C\right) \land \operatorname{PairwiseOrthogonalMeasurements}\left(C\right) \Rightarrow\\{}\operatorname{ReTr}\left(\rho^{2}\right) - \frac{1}{d} =\\{}\sum_{l} \sum_{j} {\operatorname{basisProbability}\left(\rho, \operatorname{context}\left(C, l\right), j\right) - \frac{1}{d}}^{2} + \operatorname{purityResidual}\left(C, \operatorname{centeredDensity}\left(\rho\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.purity_pythagoras_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a positive semidefinite complex matrix of trace one in dimension d. Centering it by the maximally mixed state produces a trace-zero Hermitian vector whose squared Hilbert--Schmidt norm is the real trace purity minus the inverse dimension.

For each complete rank-one record context, the squared norm of its visible projection is the sum over outcomes of the squared Born probability deviations from the uniform value. Pairwise orthogonality makes these visible energies add without cross terms.

The preceding residual-orthogonality result then gives an exact Pythagorean split: purity excess equals the double sum of visible probability energies plus the squared norm of the remaining component. The family need not be tomographically complete; any unseen mass is retained by the nonnegative residual term.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.centered_hermitian_norm_sq`
- Truth anchor: `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.matrix_inner_eq_trace_conjTranspose_mul`
- Truth anchor: `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.measurement_inner_residualVector`
- Truth anchor: `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.purity_pythagoras_decomposition`
- Truth anchor: `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.traceZero_context_pythagoras`
- Truth anchor: `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.traceZero_measurement_norm_sq`
- Truth anchor: `D5/S3/Quantum/Tomography/PurityPythagorasDecomposition.trace_mul_real_of_hermitian`
- Dependency: [D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence](../Fibers/TraceZeroReadoutOrthogonalEquivalence.md)
- Dependency: [D5/S3/Quantum/Measurement/BasisMeasurementProjection](../Measurement/BasisMeasurementProjection.md)
