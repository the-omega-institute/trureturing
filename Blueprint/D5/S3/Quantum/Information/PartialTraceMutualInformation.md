# Partial Trace and Quantum Mutual Information

## Abstract

Partial traces give density-state marginals, and independent product states have zero quantum mutual information.

Application: commuting terminal menus on a common two-qubit source. Let A = M = C squared, let rho be any positive semidefinite trace-one matrix on A tensor M, and let E(c,b) be a finite calibrated menu. Every effect and its identity complement are positive semidefinite, each setting sums to the identity, and every two effects commute, including effects from different settings. The same rho is fixed before all setting and outcome quantifiers. The record is the entire unnormalized matrix partialTraceRight((I tensor E(c,b)) rho).

Flatten the menu using its dependent setting-outcome index. Matrix.commute_euclideanLin and the pinned Mathlib joint-eigenspace decomposition for a pairwise commuting symmetric family supply a common orthonormal eigenbasis b(j). Restricting to nonzero joint eigenspaces gives a finite independent family; its subordinate orthonormal basis has two vectors. Thus the common basis is derived from the actual effects. Scalar menus and an empty setting carrier require no nontrivial-effect assumption.

Put P(j) = b(j) b(j) adjoint and define the rectangular inclusion R(j)((a,m),a') = delta(a,a') b(j)(m). The actual blocks are D(j) = R(j) adjoint rho R(j), and K(j) = I tensor P(j) = R(j) R(j) adjoint. Positivity under compression gives D(j) positive semidefinite. Orthonormality gives P(j) squared = P(j), trace(P(j)) = 1, and sum P(j) = I. Finite matrix algebra gives the same matrix omega = sum K(j) rho K(j) = sum D(j) tensor P(j). Cyclicity of trace and sum K(j) = I give sum trace(D(j)) = trace(rho) = 1. Consequently omega is positive semidefinite and has trace one.

This is normalized finite convex separability, including zero blocks. Take the real weight p(j) = Re trace(D(j)). Positivity makes it nonnegative and makes the trace real. If p(j) is positive, take alpha(j) = D(j)/p(j); if p(j) is zero, the positive-semidefinite zero-trace criterion gives D(j) = 0, and alpha(j) can be the fixed density diag(1,0). In both cases D(j) = p(j) alpha(j), with alpha(j) positive semidefinite of trace one. With beta(j) = P(j), omega is the sum of p(j) alpha(j) tensor beta(j), and sum p(j) = 1. No division by a zero trace or removal of a zero outcome is used.

Each actual effect commutes with every P(j). For every path matrix O, Kronecker multiplication, cyclicity of trace, idempotence of K(j), and sum K(j) = I give trace((O tensor E(c,b)) omega) = trace((O tensor E(c,b)) rho). The trace_mul_kron_one_right supplier identifies these with pairings against the corresponding partial traces. Matrix.ext_iff_trace_mul_left then gives equality of the full conditional matrices simultaneously for all settings and outcomes, including their probabilities and populations. Taking the identity effect preserves the reduced path state; menu completeness makes each sum of conditional matrices equal to that same reduced state.

The application uses existing joint-basis, positive-matrix, trace and partial-trace results; it introduces no new mathematical declaration. For a retained history, apply the construction separately to its supplied normalized common conditional source, independent of setting. Calibration, conditional tomography, the two-qubit dimension and common-source conditions are premises. The conclusion compares terminal records and asserts neither a physical preparation procedure nor preservation under unperformed coherent reuse. It supplies the commuting forward implication only; the converse and Bell-record uniqueness require their separate arguments.

**Theorem 1.1 (Density states are positive in matrix coordinates).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall rho \in \operatorname{DensityState}\left(n\right),\; \operatorname{Matrix.PosSemidef}\left(\operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.density_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The star algebra equivalence from CStarMatrix to Matrix preserves nonnegativity, hence positive semidefiniteness.

**Theorem 1.2 (Tracing out the left factor preserves positivity).**

$$\forall M, \operatorname{PosSemidef}\left(M\right) \Rightarrow \operatorname{PosSemidef}\left(\operatorname{partialTraceLeft}\left(M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_posSemidef` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace, spectral entropy and general Lie-Trotter products in CsdLean4*. URL: <https://github.com/zblore/csd-lean4>.

*Commentary.*

For arbitrary finite carriers A and B, the reduced matrix is a finite sum of principal submatrices.

**Theorem 1.3 (Tracing out the right factor preserves positivity).**

$$\forall M, \operatorname{PosSemidef}\left(M\right) \Rightarrow \operatorname{PosSemidef}\left(\operatorname{partialTraceRight}\left(M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_posSemidef` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace, spectral entropy and general Lie-Trotter products in CsdLean4*. URL: <https://github.com/zblore/csd-lean4>.

*Commentary.*

The same principal-submatrix argument applies to the other factor.

**Theorem 1.4 (The left partial trace preserves trace).**

$$\forall M, \operatorname{trace}\left(\operatorname{partialTraceLeft}\left(M\right)\right) = \operatorname{trace}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceLeft` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace, spectral entropy and general Lie-Trotter products in CsdLean4*. URL: <https://github.com/zblore/csd-lean4>.

*Commentary.*

For every joint matrix, summing the reduced diagonal recovers its diagonal sum.

**Theorem 1.5 (The right partial trace preserves trace).**

$$\forall M, \operatorname{trace}\left(\operatorname{partialTraceRight}\left(M\right)\right) = \operatorname{trace}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace, spectral entropy and general Lie-Trotter products in CsdLean4*. URL: <https://github.com/zblore/csd-lean4>.

*Commentary.*

Together with positivity, trace preservation gives a normalized marginal.

**Definition 1.6 (Spectral entropy of a Hermitian matrix).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall rho \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall h \in \operatorname{Matrix.IsHermitian}\left(rho\right),\; \operatorname{spectralEntropy}\left(h\right) = \sum_{i:n} \operatorname{Real.negMulLog}\left(\operatorname{Matrix.IsHermitian.eigenvalues}\left(h, i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/PartialTraceMutualInformation.spectralEntropy` (`✓ std3`).

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For any Hermitian matrix on a finite carrier, spectralEntropy sums Real.negMulLog over its eigenvalues. On density matrices this is von Neumann entropy in nats, including singular states with the zero-eigenvalue contribution set to zero.

**Theorem 1.7 (Unitary conjugation preserves the characteristic polynomial).**

$$\forall i \in \operatorname{Type},\; [\operatorname{Fintype}\left(i\right)] [\operatorname{DecidableEq}\left(i\right)] \forall rho \in \operatorname{Matrix}\left(i, i, \mathbb{C}\right),\; \forall U \in \operatorname{Matrix}\left(i, i, \mathbb{C}\right),\; (\operatorname{star}\left(U\right) \cdot U = 1) \Rightarrow (\operatorname{Matrix.charpoly}\left(U \cdot rho \cdot \operatorname{star}\left(U\right)\right) = \operatorname{Matrix.charpoly}\left(rho\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.charpoly_conj_unitary` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace, spectral entropy and general Lie-Trotter products in CsdLean4*. URL: <https://github.com/zblore/csd-lean4>.

*Commentary.*

For every finite matrix index type, conjugation by a matrix whose adjoint times the matrix is the identity leaves the characteristic polynomial unchanged.

**Definition 1.8 (Mutual information of a joint density state).**

$$\operatorname{quantumMutualInformation}\left(\rho\right) = \operatorname{vonNeumannEntropy}\left(\operatorname{marginalRight}\left(\rho\right)\right) + \operatorname{vonNeumannEntropy}\left(\operatorname{marginalLeft}\left(\rho\right)\right) - \operatorname{vonNeumannEntropy}\left(\rho\right)$$

*Formalization.* `D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation` (`✓ std3`).

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The only input is the joint state. marginalRight retains A and marginalLeft retains B; each is constructed by partial trace.

**Theorem 1.9 (Entropy adds on independent product states).**

$$\forall \rho, \sigma, \operatorname{vonNeumannEntropy}\left(\operatorname{productState}\left(\rho, \sigma\right)\right) = \operatorname{vonNeumannEntropy}\left(\rho\right) + \operatorname{vonNeumannEntropy}\left(\sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.vonNeumannEntropy_productState` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace, spectral entropy and general Lie-Trotter products in CsdLean4*. URL: <https://github.com/zblore/csd-lean4>.

*Commentary.*

The spectrum of the product is the multiset of pairwise eigenvalue products. For any two density states on finite carriers, including singular states, the proof uses the zero value of x log x at zero.

**Theorem 1.10 (Independent product states have zero mutual information).**

$$\forall \rho, \sigma, \operatorname{quantumMutualInformation}\left(\operatorname{productState}\left(\rho, \sigma\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation_productState` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Partial trace, spectral entropy and general Lie-Trotter products in CsdLean4*. URL: <https://github.com/zblore/csd-lean4>.

*Commentary.*

The actual partial traces recover the two factors. Their entropies cancel the entropy of the product by tensor additivity.

## References

- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.charpoly_conj_unitary`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.density_posSemidef`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft_posSemidef`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_posSemidef`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation_productState`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.spectralEntropy`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceLeft`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.vonNeumannEntropy_productState`
- Dependency: [D5/S3/Quantum/Divergence/VonNeumannEntropyPinching](../Divergence/VonNeumannEntropyPinching.md)
