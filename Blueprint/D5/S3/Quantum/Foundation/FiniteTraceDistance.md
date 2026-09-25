# Finite Trace Distance

## Abstract

Trace norm, actual density-state distance, and contraction for every canonical quantum channel.

DensityState and QuantumChannel are the canonical FiniteStateChannel carriers. raw denotes CStarMatrix.ofMatrix.symm, applied to the value of a state when its argument is a density state; toCstar denotes the forward equivalence. All coordinate types are finite with decidable equality, including empty types. RCLike is the existing Mathlib scalar interface. Adjoint means conjugate transpose and the square root uses the positive-semidefinite matrix order.

**Definition 1.1 (Actual trace norm).**

$$\forall m \in FiniteType, n \in FiniteType, R \in RCLike, A \in \operatorname{Matrix}\left(m, n, R\right),\; \operatorname{traceNorm}\left(A\right) = \operatorname{re}\left(\operatorname{trace}\left(\operatorname{sqrt}\left(A^{*} \cdot A\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm` (`✓ std3`).

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

This is the real part of the trace of the positive square root of the Gram matrix.

**Theorem 1.2 (Negation invariance).**

$$\forall m \in FiniteType, n \in FiniteType, R \in RCLike, A \in \operatorname{Matrix}\left(m, n, R\right),\; \operatorname{traceNorm}\left(0 - A\right) = \operatorname{traceNorm}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_neg` (`✓ std3`). ∎

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

Negation leaves the Gram matrix unchanged.

**Theorem 1.3 (Nonnegative trace norm).**

$$\forall m \in FiniteType, n \in FiniteType, R \in RCLike, A \in \operatorname{Matrix}\left(m, n, R\right),\; 0 \le \operatorname{traceNorm}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_nonneg` (`✓ std3`). ∎

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

The positive square root is positive semidefinite and has nonnegative real trace.

**Theorem 1.4 (Unitary maximum formula).**

$$\forall n \in FiniteType, A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \left(\exists U \in \operatorname{unitaryGroup}\left(n, \mathbb{C}\right),\; \operatorname{re}\left(\operatorname{trace}\left(\operatorname{val}\left(U\right) \cdot A\right)\right) = \operatorname{traceNorm}\left(A\right)\right) \land \left(\forall U \in \operatorname{unitaryGroup}\left(n, \mathbb{C}\right),\; \operatorname{re}\left(\operatorname{trace}\left(\operatorname{val}\left(U\right) \cdot A\right)\right) \le \operatorname{traceNorm}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_eq_max_re_tr_U` (`✓ std3`). ∎

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

A unitary attains the trace norm as the real trace of its product with A, and every unitary gives a value at most the trace norm. Here val denotes the underlying matrix. The formula holds in every finite complex square dimension, including the empty type.

**Theorem 1.5 (Trace norm triangle inequality).**

$$\forall n \in FiniteType, A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right), B \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{traceNorm}\left(A + B\right) \le \operatorname{traceNorm}\left(A\right) + \operatorname{traceNorm}\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_add_le` (`✓ std3`). ∎

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

The retained SVD proof identifies the norm as the maximum real trace over unitaries; trace additivity gives the bound.

**Theorem 1.6 (Positive trace norm).**

$$\forall n \in FiniteType, R \in RCLike, A \in \operatorname{Matrix}\left(n, n, R\right),\; \operatorname{PosSemidef}\left(A\right) \Rightarrow \operatorname{embed}\left(R, \operatorname{traceNorm}\left(A\right)\right) = \operatorname{trace}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_of_posSemidef` (`✓ std3`). ∎

*Citation.* Mark M. Wilde (2017). *Quantum Information Theory*. DOI: [10.1017/9781316809976](https://doi.org/10.1017/9781316809976).

*Commentary.*

For a positive semidefinite matrix, the Gram matrix is its square and its positive square root is the original matrix.

**Definition 1.7 (Canonical channel on matrix coordinates).**

$$\forall n \in FiniteType, C \in \operatorname{QuantumChannel}\left(n, n\right), A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{act}\left(C, A\right) = \operatorname{raw}\left(\operatorname{applyCP}\left(C, \operatorname{toCstar}\left(A\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteTraceDistance.act` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix coordinate equivalence transports the actual completely positive map.

**Definition 1.8 (Actual density distance).**

$$\forall n \in FiniteType, rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right),\; \operatorname{traceDistance}\left(rho, sigma\right) = \frac{\operatorname{traceNorm}\left(\operatorname{raw}\left(rho\right) - \operatorname{raw}\left(sigma\right)\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical density-state values are converted to matrices before taking half the trace norm of their difference.

**Theorem 1.9 (Nonnegative density distance).**

$$\forall n \in FiniteType, rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right),\; 0 \le \operatorname{traceDistance}\left(rho, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Trace-norm nonnegativity gives the lower endpoint of the density-distance interval.

**Theorem 1.10 (Symmetry).**

$$\forall n \in FiniteType, rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right),\; \operatorname{traceDistance}\left(rho, sigma\right) = \operatorname{traceDistance}\left(sigma, rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing the state difference negates the matrix and preserves its trace norm.

**Theorem 1.11 (Density distance triangle inequality).**

$$\forall n \in FiniteType, rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right), tau \in \operatorname{DensityState}\left(n\right),\; \operatorname{traceDistance}\left(rho, tau\right) \le \operatorname{traceDistance}\left(rho, sigma\right) + \operatorname{traceDistance}\left(sigma, tau\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split the state difference through the intermediate state and apply the trace-norm triangle inequality.

**Theorem 1.12 (All density distances are at most one).**

$$\forall n \in FiniteType, rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right),\; \operatorname{traceDistance}\left(rho, sigma\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each density matrix has trace norm one; the triangle inequality bounds their difference by two.

**Theorem 1.13 (Every CPTP channel contracts trace distance).**

$$\forall n \in FiniteType, C \in \operatorname{QuantumChannel}\left(n, n\right), rho \in \operatorname{DensityState}\left(n\right), sigma \in \operatorname{DensityState}\left(n\right),\; \operatorname{traceDistance}\left(\operatorname{mapState}\left(C, rho\right), \operatorname{mapState}\left(C, sigma\right)\right) \le \operatorname{traceDistance}\left(rho, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split the Hermitian state difference into positive and negative parts. Positivity and trace preservation preserve their trace-norm masses, whose sum is the original trace norm.

The trace-norm proofs and their necessary SVD, orthonormal extension, and unitary row-sum dependencies retain Alex Meiburg's Physlib source at revision 6a09b2d1761a0d4430083045a247eb121d8da260. The Lean owner retains its copyright and full Apache 2.0 license. Retention ends when equivalent declarations are available in this repository's own pinned Mathlib.

Contraction follows from the actual Hermitian Jordan positive and negative parts, their trace-norm mass identity, complete positivity, and trace preservation. It assumes neither a contractivity field nor a Kraus representation of the recovery. The finite-record recovery-error theorem consumes these laws; no computational recovery algorithm is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.act`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_contract`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_le_one`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_nonneg`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_symm`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_triangle`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_add_le`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_eq_max_re_tr_U`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_neg`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_nonneg`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_of_posSemidef`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](FiniteStateChannel.md)
