# Partial Trace and Quantum Mutual Information

## Abstract

Partial traces give density-state marginals, and independent product states have zero quantum mutual information.

Application: the literal ordered-site Slater prefix marginal. Fix natural numbers N, k and ell with k at most N and ell at most N. Let V be a complex N by k matrix satisfying V adjoint V = I. A Boolean word x on Fin N determines its occupied subset S(x), the sites where x is true. Define psi(V,x) to be det(V restricted to S(x) in increasing natural row order) when S(x) has size k, and zero otherwise; the column order is unchanged. The Boolean words are in bijection with all subsets of Fin N. Applying the rectangular cauchyBinet formula as in CompoundMatrices and summing the zero amplitudes gives sum over all x of conjugate(psi(V,x)) times psi(V,x) = 1. Normalization is derived from V, rather than assumed for a separately chosen state.

Use Fin.appendEquiv ell (N - ell), followed by the equality ell + (N - ell) = N, to concatenate a prefix word a on Fin ell and a tail word b on Fin (N - ell) in the original site order. Put psiSplit(a,b) = psi(V,ab) and M((a,b),(a',b')) = psiSplit(a,b) conjugate(psiSplit(a',b')). The literal matrix R(a,a') = sum over all tail words b of psiSplit(a,b) conjugate(psiSplit(a',b)) is exactly partialTraceRight(M). Matrix.posSemidef_vecMulVec_self_star makes M positive semidefinite, and partialTraceRight_posSemidef therefore makes R positive semidefinite. The diagonal sum, reindexed by the same concatenation bijection, gives trace(R) = 1. This constructs a density matrix on every Boolean prefix word, including zero amplitudes, without any spectrum or correlation assumption. The argument includes N = 0, k = 0, k = N and ell = 0 or N.

The ordered-prefix identity in CompoundMatrices has an actual partial-trace consumer. For any complex ell by ell matrix U put B = U directSum I_(N-ell), in the same literal site order. The determinant-amplitude action gives psi(B V) = Gamma_N(B) psi(V). After reindexing by Fin.appendEquiv, ordered-prefix locality identifies Gamma_N(B) with Gamma_ell(U) tensor I on all prefix and tail words. Hence the actual rank-one matrix M_(B V) is (Gamma_ell(U) tensor I) M_V (Gamma_ell(U) tensor I) adjoint. The existing D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.trace_local_right applied with its tail matrix equal to the identity therefore gives R_(B V) = Gamma_ell(U) R_V Gamma_ell(U) adjoint. This derives covariance from the literal minors and the literal partial trace; covariance is not an input assumption. The identity itself holds for arbitrary U and V, with no orthonormality premise.

For a change of orthonormal one-particle basis, the exact hypothesis is U adjoint U = I on Fin ell. The full occupation lift then satisfies Gamma_ell(U) adjoint Gamma_ell(U) = I, so it belongs to Matrix.unitaryGroup on every Boolean prefix word. Block multiplication also gives B adjoint B = I, and therefore (B V) adjoint (B V) = V adjoint V = I. This preserves the actual normalized Slater construction. Taking N = ell + n and then n = N - ell preserves arbitrary k at most N and ell at most N, including N = 0, vacuum, full filling, empty prefix and full prefix. This covariance application reuses existing suppliers and introduces no new mathematical declaration.

The actual kernel when the prefix compression is diagonal. Write N = ell + n, X = V restricted to its first ell rows, and Y = V restricted to the last n rows. Suppose only X X adjoint = diag(nu), where nu is a real list indexed by every i in Fin ell. Then the literal marginal above satisfies R(a,a') = delta(a,a') p(a), where p(a) is the product over all i of nu(i) when a(i) is true and 1 - nu(i) otherwise. This is an entry identity for the same determinant-amplitude vector, rather than a state reconstructed from its correlations. Orthonormality and the actual diagonal compression are its only matrix hypotheses.

Here is a coefficient derivation with exact parameter correspondence. Let S and T be occupied prefix subsets of equal cardinality r, and let X_S and X_T retain their increasing natural rows. Stack X_S above Y, and X_T above the same Y. In cauchyBinet, weight each of the first r rows by the polynomial variable t and each tail row by one. Extracting the coefficient of t to the r selects exactly the minors containing all r selected prefix rows. Hence the actual sum over all tail subsets B of det(V_(S union B)) conjugate(det(V_(T union B))) equals the coefficient of t to the r in det(Y adjoint Y + t X_T adjoint X_S). Each determinant is zero unless its row count is k. The prefix and tail are joined by Fin.castAdd n and Fin.natAdd ell, respectively, so these are exactly the original natural-order minors. Finset.orderEmbOfFin_unique identifies the increasing enumerations; no classical compound order or unaccounted permutation sign enters this calculation.

The original column orthonormality gives X adjoint X + Y adjoint Y = I. Define E_(T,S) by its entry (i,j) being the sum over q in Fin r of delta(i,T(q)) delta(j,S(q)), using the increasing enumerations of S and T. Thus X_T adjoint X_S = X adjoint E_(T,S) X. Matrix.det_one_add_mul_comm, applied over the polynomial ring, changes the determinant above into det(I - P + t E_(T,S) P), where P = X X adjoint. With P = diag(nu), the variable rows are supported on T and the variable columns on S. Reindex by T and its complement. Matrix.det_fromBlocks_zero₂₁ and Polynomial.coeff_det_X_add_C_card give the coefficient as det((E_(T,S) diag(nu)) restricted to T by T) times the product over i outside T of 1 - nu(i). If S = T the first matrix is diagonal with entries nu(i). If S differs from T, equal cardinality gives a site in T outside S, whose column is zero; Matrix.det_eq_zero_of_column_eq_zero makes the coefficient zero. If the cardinalities differ, the same tail subset cannot make both total row counts equal k, so every summand is zero.

The Boolean-word/subset equivalence sends a to the finite set of sites at which a is true. Under literal Fin.append it sends ab to S(a) disjoint-union S(b), mapped by finSumFinEquiv. Reindexing the tail-subset sum through this equivalence gives the literal tail-word sum defining R. Finset.prod_ite rewrites the occupied and unoccupied products as p(a). This establishes every matrix entry simultaneously, including unequal prefix particle sectors. No inverse, strictly interior eigenvalue, Gaussianity, covariance or desired density realization is used as a premise.

The interval bounds also come from V. The full matrix P_full = V V adjoint is positive semidefinite and idempotent. Consequently I - P_full = (I - P_full) adjoint (I - P_full) is positive semidefinite. Compress both matrices to the first ell sites. Their diagonal entries are nu(i) and 1 - nu(i), so Matrix.PosSemidef.diag_nonneg gives 0 at most nu(i) at most 1 for every one of the ell indices. The proof keeps repeated values and zero or one values, with no discarded null space. It includes k = 0, k = N, ell = 0, ell = N and N = 0; empty determinants and empty products are one.

There is an actual application to the Hermitian spectral basis. For the original P = X X adjoint let Q be its eigenvectorUnitary and nu its complete Fin ell eigenvalue list. Define W by replacing the prefix rows X by Q adjoint X and retaining the same tail rows Y. Block multiplication gives W adjoint W = I, and Matrix.IsHermitian.spectral_theorem gives the actual prefix compression of W as diag(nu). The kernel calculation therefore gives R_W = diag(p) and all the interval bounds. Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal with the identity unitary gives a permutation of the entire Boolean occupation carrier identifying the eigenvalues of R_W with p. Thus it retains all 2 to the ell values with their multiplicities, including zeros.

For this rotated actual marginal the spectral entropy is the sum over i in Fin ell of Real.binEntropy(nu(i)). Indeed, Finset.prod_univ_sum gives sum over a of p(a) = 1. Split an occupation word into its first Boolean coordinate and its remaining coordinates with Fin.consEquiv. The identity Real.negMulLog_mul and that normalization sum reduce the spectral sum by one coordinate. Finite induction gives the sum of Real.negMulLog(nu(i)) and Real.negMulLog(1 - nu(i)), which is Real.binEntropy(nu(i)). The identity uses Real.negMulLog_zero, so it includes singular states and the empty prefix. These coefficient, basis and spectral applications reuse existing declarations and introduce no new mathematical declaration or originality claim.

Return now to the original basis of the same Slater vector. Put G = Gamma_ell(Q adjoint), and let U = G adjoint on the complete Boolean prefix carrier. The matrix W defined by its rotated prefix rows is exactly (Q adjoint directSum I_n) V: the first ell rows are Q adjoint X and the final n rows are Y. Hence the literal covariance identity gives R_W = G R_V G adjoint. Together with G adjoint G = I and R_W = diag(p), multiplication on the left by G adjoint and on the right by G gives R_V = U diag(p) U adjoint. The full occupation lift makes U unitary on every Boolean word, including all particle sectors. The only matrix hypothesis on the original V is V adjoint V = I; the diagonal compression, covariance, density realization and normalization in this conclusion are all derived.

The complete spectrum is indexed by the entire Boolean prefix carrier, rather than by the k particle columns. Applying Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal to R_V with the actual U above gives a permutation sigma of all Boolean words such that eigenvalues(R_V)(sigma(a)) = p(a). Equivalently, the eigenvalue multiset is the multiset of the 2 to the ell products p(a). Every multiplicity, zero and one spatial mode and impossible occupation sector is retained. For arbitrary ell at most N take n = N - ell and transport the literal Fin.append word by finCongr(ell + n = N). The prefix row map then is Fin.castLE ell N. Thus nu is exactly the complete Fin ell eigenvalue list of the original X X adjoint, with no substituted particle Gram carrier.

Let rho_V be the density state whose matrix coordinates are the same literal R_V. Its positivity and trace one were derived above from the determinant amplitudes and tail-word sum. The original entropy_eq_spectral theorem gives vonNeumannEntropy(rho_V) = spectralEntropy(R_V). Reindexing that spectral sum by sigma and using the finite product entropy identity yields vonNeumannEntropy(rho_V) = sum over all i in Fin ell of Real.binEntropy(nu(i)). In particular this is the von Neumann entropy defined by minus trace(rho log rho), including singular density states. All conclusions apply simultaneously to the same original V and R_V, including N = 0, k = 0, k = N, ell = 0 and ell = N. The determinant, partial-trace, unitary-spectrum and entropy identities establish these conclusions. The Slater two-point formula, noncontiguous subsystems with their fermionic ordering, physical ground-state selection, filling, many-body gaps and spatial entropy scaling retain their separate obligations.

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
