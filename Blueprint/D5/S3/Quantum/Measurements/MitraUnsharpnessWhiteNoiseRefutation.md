# Mitra's white-noise conjecture for qubit observables

## Abstract

A four-outcome diagonal qubit observable contradicts the first inequality in Mitra's white-noise conjecture.

A qubit observable is a finite family of positive semidefinite complex two-by-two matrices summing to the identity. The predicate D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM has the following meaning:

$$
\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(A\right)\right) \Leftrightarrow \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Matrix.PosSemidef}\left(A\left(i\right)\right)\right)\right) \land \left(\sum_{\left(i: \operatorname{Fin}\left(n\right)\right)} \left(A\left(i\right)\right) = \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right)\right)\right)\right)
$$

All outcome indices are zero-based Fin indices. The numeral one of matrix type is the identity matrix. A centered dot with a real left operand denotes real scalar multiplication; a star denotes matrix multiplication. The notation (n : ℝ) denotes the cast from ℕ to ℝ, and every displayed quotient is real division. The definitions of the quantities below allow n = 0; the conjecture requires n ≥ 1.

**Definition 1.1 (The Euclidean operator norm).**

$$\forall \left(M: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.opNorm}\left(M\right): \mathbb{R}\right) = \left\lVert \operatorname{Matrix.toEuclideanCLM}\left(M\right) \right\rVert\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.opNorm` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Section IV uses the operator norm. Matrix.toEuclideanCLM here has scalar field ℂ and index type Fin 2; its norm is the continuous-linear-map norm induced by the Euclidean norm on ℂ².

**Definition 1.2 (The norm-weighted matrix).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.X}\left(A\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right) = \sum_{\left(i: \operatorname{Fin}\left(n\right)\right)} \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.opNorm}\left(A\left(i\right)\right)\right) \cdot \left(A\left(i\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.X` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Section IV.A defines the X-matrix as the sum of each effect multiplied by its operator norm. The same matrix appears in equation (51).

**Definition 1.3 (The lowest Hermitian eigenvalue).**

$$\forall \left(M: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\forall \left(hM: \operatorname{Matrix.IsHermitian}\left(M\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.xMin}\left(M\right): \mathbb{R}\right) = \operatorname{min}\left(\operatorname{Matrix.IsHermitian.eigenvalues}\left(hM, 0\right), \operatorname{Matrix.IsHermitian.eigenvalues}\left(hM, 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.xMin` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Theorem 3 uses the lowest eigenvalue of the Hermitian X-matrix. For any Hermitian two-by-two matrix M, the minimum of its two Matrix.IsHermitian.eigenvalues is its lowest eigenvalue. The Hermitian proof argument hM of xMin is not displayed in the application xMin(M); it is retained in the eigenvalue applications. No ordering of the two eigenvalue indices is assumed.

**Definition 1.4 (The first spectral quantity).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\forall \left(hA: \operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(A\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.sigma1}\left(A, hA\right): \mathbb{R}\right) = \left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.xMin}\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.X}\left(A\right)\right)\right) - \left(\frac{1}{\left(n: \mathbb{R}\right)}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.sigma1` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Theorem 3, equation (50), defines Σ₁ as the lowest eigenvalue of the X-matrix minus 1/n. The proof argument hA of sigma1 is displayed in its application; the Hermitian proof argument of xMin is not displayed. The matrix passed to xMin is X(A).

**Definition 1.5 (The second spectral quantity).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\forall \left(hA: \operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(A\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.sigma2}\left(A, hA\right): \mathbb{R}\right) = \left(\frac{\sum_{\left(i: \operatorname{Fin}\left(n\right)\right)} \left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.opNorm}\left(A\left(i\right)\right)\right)}{\left(n: \mathbb{R}\right)}\right) - \left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.xMin}\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.X}\left(A\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.sigma2` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Theorem 3, equation (50), defines Σ₂ as the mean effect norm minus the lowest eigenvalue of the X-matrix. The proof argument hA of sigma2 is displayed in its application; the Hermitian proof argument of xMin is not displayed. The matrix passed to xMin is X(A).

**Definition 1.6 (The first trace quantity).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.sigma1Prime}\left(A\right): \mathbb{R}\right) = \left(\frac{\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.X}\left(A\right)\right)\right)}{2}\right) - \left(\frac{1}{\left(n: \mathbb{R}\right)}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.sigma1Prime` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Theorem 4, equation (60), defines Σ′₁ using the normalized trace. In dimension two this is the real part of Matrix.trace of X(A), divided by two, minus 1/n. This definition places no positivity assumption on A.

**Definition 1.7 (The second trace quantity).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.sigma2Prime}\left(A\right): \mathbb{R}\right) = \left(\frac{\sum_{\left(i: \operatorname{Fin}\left(n\right)\right)} \left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.opNorm}\left(A\left(i\right)\right)\right)}{\left(n: \mathbb{R}\right)}\right) - \left(\frac{\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.X}\left(A\right)\right)\right)}{2}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.sigma2Prime` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Theorem 4, equation (60), defines Σ′₂ as the mean effect norm minus the normalized trace of X(A). The displayed real part is Complex.re. This definition places no positivity assumption on A.

**Definition 1.8 (Operator-norm unsharpness).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.E}\left(A\right): \mathbb{R}\right) = \operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.opNorm}\left(\left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right) - \left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.X}\left(A\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.E` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Section IV.A, equation (44), gives the unsharpness as the operator norm of the identity minus the X-matrix.

**Definition 1.9 (Normalized-trace unsharpness).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.EPrime}\left(A\right): \mathbb{R}\right) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\left(\left(\left(\frac{1}{2}: \mathbb{R}\right)\right) \cdot \left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right)\right) * \left(\left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right) - \left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.X}\left(A\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.EPrime` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Section IV.A, equation (48), gives the trace of (I/d)(I − X). Here d = 2, the factor 1/2 acts on the identity by real scalar multiplication, and Complex.re takes the real part of the trace of the matrix product.

**Definition 1.10 (Adding white noise).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\forall \left(l: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.noisy}\left(A, l\right): \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right) = \lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\left(\left(l\right) \cdot \left(A\left(i\right)\right)\right) + \left(\left(\frac{\left(1\right) - \left(l\right)}{\left(n: \mathbb{R}\right)}\right) \cdot \left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.noisy` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Theorems 3 and 4 use the mixture λAᵢ + (1 − λ)I/n. The definition accepts every real l; the conjecture restricts l to Set.Icc 0 1, the closed real interval from zero to one.

**Definition 1.11 (Conjecture 1).**

$$\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.claim}\right) \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\left(1 \le n\right) \Rightarrow \left(\forall \left(A: \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right), \left(\forall \left(hA: \operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(A\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.sigma2}\left(A, hA\right) \le \operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.sigma1}\left(A, hA\right)\right) \land \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.sigma2Prime}\left(A\right) \le \operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.sigma1Prime}\left(A\right)\right) \land \left(\left(\forall \left(l: \mathbb{R}\right), \left(\left(l \in \operatorname{Set.Icc}\left(\left(0: \mathbb{R}\right), 1\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.E}\left(A\right) \le \operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.E}\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.noisy}\left(A, l\right)\right)\right)\right)\right) \land \left(\forall \left(l: \mathbb{R}\right), \left(\left(l \in \operatorname{Set.Icc}\left(\left(0: \mathbb{R}\right), 1\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.EPrime}\left(A\right) \le \operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.EPrime}\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.noisy}\left(A, l\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.claim` (`✓ std3`).

*Citation.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

Section IV.B, page 11, Conjecture 1 states: For any qubit observable A, inequality Σ₁ ≥ Σ₂ and inequality Σ′₁ ≥ Σ′₂ hold and therefore, E(A^λ) ≥ E(A) and E′(A^λ) ≥ E′(A) for all 1 ≥ λ ≥ 0. The formula retains all four assertions, for every n ≥ 1 and every qubit observable, without a diagonal or distinctness condition. The proof argument hA of sigma1 and sigma2 is displayed in their applications. Theorems 3 and 4 explain the two inequalities used by the conjecture; their equivalences are not asserted here.

**Definition 1.12 (A real diagonal complex matrix).**

$$\forall \left(u: \mathbb{R}\right), \left(\forall \left(v: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.diag2}\left(u, v\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right) = \operatorname{Matrix.diagonal}\left(![\left(u: \mathbb{C}\right), \left(v: \mathbb{C}\right)]\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.diag2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

The two real entries are embedded in ℂ before Matrix.diagonal forms the matrix. This construction supplies diagonal observables for the quantities in Section IV.

**Definition 1.13 (Four diagonal effects).**

$$\left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.witness}: \left(\operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right) = ![\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.diag2}\left(\left(\frac{12}{40}: \mathbb{R}\right), \left(\frac{1}{40}: \mathbb{R}\right)\right), \operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.diag2}\left(\left(\frac{13}{40}: \mathbb{R}\right), \left(\frac{1}{40}: \mathbb{R}\right)\right), \operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.diag2}\left(\left(\frac{14}{40}: \mathbb{R}\right), \left(\frac{1}{40}: \mathbb{R}\right)\right), \operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.diag2}\left(\left(\frac{1}{40}: \mathbb{R}\right), \left(\frac{37}{40}: \mathbb{R}\right)\right)]$$

*Formalization.* `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.witness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

The four effects, in outcome order, have diagonal entries (12/40, 1/40), (13/40, 1/40), (14/40, 1/40), and (1/40, 37/40). They are positive semidefinite and sum to the identity, so they form a qubit observable to which Conjecture 1 applies.

**Theorem 1.14 (The universal conjecture is false).**

$$\neg \left(\operatorname{D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mitra-2022-unsharpness-white-noise-monotonicity-refutation` (refuted) by `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mitra-2022-unsharpness-white-noise-monotonicity-refutation","declaration_gid":"D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arindam Mitra (2022). *Quantifying unsharpness of observables in an outcome-independent way*. DOI: [10.1007/s10773-022-05219-2](https://doi.org/10.1007/s10773-022-05219-2). URL: <https://arxiv.org/abs/2201.02578v3>.

*Commentary.*

For the four diagonal effects above, the operator norms are 12/40, 13/40, 14/40, and 37/40, with sum 19/10. Their X-matrix has diagonal entries 273/800 and 704/800, so its lowest eigenvalue is 273/800. Consequently Σ₁ = 73/800 < Σ₂ = 107/800. The first inequality in Conjecture 1 fails, which refutes the conjunction.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.E`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.EPrime`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.X`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.diag2`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.noisy`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.opNorm`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.sigma1`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.sigma1Prime`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.sigma2`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.sigma2Prime`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.witness`
- Truth anchor: `D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.xMin`
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
