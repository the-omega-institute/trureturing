# Partial Trace and Quantum Mutual Information

## Abstract

Partial traces give density-state marginals, and independent product states have zero quantum mutual information.

Application: the literal ordered-site Slater prefix marginal. Fix natural numbers N, k and ell with k at most N and ell at most N. Let V be a complex N by k matrix satisfying V adjoint V = I. A Boolean word x on Fin N determines its occupied subset S(x), the sites where x is true. Define psi(V,x) to be det(V restricted to S(x) in increasing natural row order) when S(x) has size k, and zero otherwise; the column order is unchanged. The Boolean words are in bijection with all subsets of Fin N. Applying the rectangular cauchyBinet formula as in CompoundMatrices and summing the zero amplitudes gives sum over all x of conjugate(psi(V,x)) times psi(V,x) = 1. Normalization is derived from V, rather than assumed for a separately chosen state.

Use Fin.appendEquiv ell (N - ell), followed by the equality ell + (N - ell) = N, to concatenate a prefix word a on Fin ell and a tail word b on Fin (N - ell) in the original site order. Put psiSplit(a,b) = psi(V,ab) and M((a,b),(a',b')) = psiSplit(a,b) conjugate(psiSplit(a',b')). The literal matrix R(a,a') = sum over all tail words b of psiSplit(a,b) conjugate(psiSplit(a',b)) is exactly partialTraceRight(M). Matrix.posSemidef_vecMulVec_self_star makes M positive semidefinite, and partialTraceRight_posSemidef therefore makes R positive semidefinite. The diagonal sum, reindexed by the same concatenation bijection, gives trace(R) = 1. This constructs a density matrix on every Boolean prefix word, including zero amplitudes, without any spectrum or correlation assumption. The argument includes N = 0, k = 0, k = N and ell = 0 or N.

The ordered-prefix identity in CompoundMatrices has an actual partial-trace consumer. For any complex ell by ell matrix U put B = U directSum I_(N-ell), in the same literal site order. The determinant-amplitude action gives psi(B V) = Gamma_N(B) psi(V). After reindexing by Fin.appendEquiv, ordered-prefix locality identifies Gamma_N(B) with Gamma_ell(U) tensor I on all prefix and tail words. Hence the actual rank-one matrix M_(B V) is (Gamma_ell(U) tensor I) M_V (Gamma_ell(U) tensor I) adjoint. The existing D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.trace_local_right applied with its tail matrix equal to the identity therefore gives R_(B V) = Gamma_ell(U) R_V Gamma_ell(U) adjoint. This derives covariance from the literal minors and the literal partial trace; covariance is not an input assumption. The identity itself holds for arbitrary U and V, with no orthonormality premise.

For a change of orthonormal one-particle basis, the exact hypothesis is U adjoint U = I on Fin ell. The full occupation lift then satisfies Gamma_ell(U) adjoint Gamma_ell(U) = I, so it belongs to Matrix.unitaryGroup on every Boolean prefix word. Block multiplication also gives B adjoint B = I, and therefore (B V) adjoint (B V) = V adjoint V = I. This preserves the actual normalized Slater construction. Taking N = ell + n and then n = N - ell preserves arbitrary k at most N and ell at most N, including N = 0, vacuum, full filling, empty prefix and full prefix. This covariance application reuses existing suppliers and introduces no new mathematical declaration.

The unresolved spectrum statement concerns this R. Write V_I for the first ell rows of V and P_I = V_I V_I adjoint. It requires a unitary on all Boolean prefix words which conjugates R to a diagonal matrix whose entry at a is the product, over every i in Fin ell, of nu(i) if a(i) is true and 1 - nu(i) otherwise. Here nu must be the complete ell-indexed eigenvalue list of P_I, with its interval bounds derived from V. All repetitions and zero or one modes must remain. The k by k matrix V_I adjoint V_I cannot substitute its index carrier for these ell spatial modes. The ordered prefix tensor correspondence and covariance above allow a spatial change of basis. What remains is to prove that diagonalizing P_I makes this same literal marginal diagonal with the stated product entries, without assuming Gaussianity or a diagonal realization. This entry formula is required before applying complete spectral-permutation and entropy results. The product-state entropy theorem below does not provide that correspondence.

The normalization and marginal construction above reuse existing results and introduce no new mathematical declaration. They establish neither the Slater two-point formula nor its full prefix spectrum and entropy. Noncontiguous site subsystems require their own fermionic-order correspondence. Physical ground-state selection, filling, many-body gaps and spatial entropy scaling also require separate hypotheses and results.

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
