# Realignment spectra and elementary-symmetric separation

## Abstract

Realignment spectra and sharp elementary-symmetric tail bounds

**Definition 1.1 (Realignment).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.realign`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.realign` (`✓ std3`).

*Citation.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

The complex bipartite matrix with entries indexed by (i,a) and (j,b) is rearranged into a rectangular matrix with row (i,j), column (a,b), and the same entry. The definition applies to arbitrary index types.

**Definition 1.2 (The row singular-value vector).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.singularVector`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.singularVector` (`✓ std3`).

*Citation.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For a complex matrix on finite row and column types, this vector consists of the descending native singular values of its adjoint, through the row dimension. It therefore has the square of Alice's dimension entries for a realigned bipartite matrix. Zero values remain in the vector.

**Definition 1.3 (Elementary symmetric functions of singular values).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymmSV`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymmSV` (`✓ std3`).

*Citation.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

The degree ell elementary symmetric function is evaluated on the multiset of row singular values. Each subset of ell positions contributes the product of the corresponding singular values.

**Definition 1.4 (Elementary symmetric functions of finite real vectors).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymmVec`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymmVec` (`✓ std3`).

*Citation.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For a vector of length k, the degree ell elementary symmetric function is evaluated on its complete multiset of entries, including repetitions and zeros.

**Definition 1.5 (The common tail coordinate).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.tailMean`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.tailMean` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For k coordinates and distinguished value a, the common tail value is (1-a)/(k-1). The natural subtraction in the denominator is retained in the definition.

**Definition 1.6 (The one-heavy-coordinate profile).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.schurProfile`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.schurProfile` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

The profile is choose(k-1,ell) times b to the ell plus choose(k-1,ell-1) times a times b to the ell-1, where b=(1-a)/(k-1). For k at least one and positive ell this is the elementary symmetric function at (a,b,...,b).

**Definition 1.7 (The covariance tail threshold).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separableThreshold`

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separableThreshold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For natural local dimensions m and n, the threshold is one minus the square root of (1-1/m)(1-1/n).

**Theorem 1.8 (The threshold is below one).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separableThreshold_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separableThreshold_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For local dimensions m and n at least two, the covariance tail threshold is strictly below one.

**Theorem 1.9 (The threshold exceeds the uniform coordinate).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separableThreshold_gt_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separableThreshold_gt_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For local dimensions m and n at least two, the covariance tail threshold strictly exceeds 1/m squared. The proof first bounds it strictly above 1/(2m).

**Theorem 1.10 (The main spectrum gives a strict scalar gap).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.main_profile_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.main_profile_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

If 2 at most m is strictly less than n, n is at most m cubed, and 2 at most ell at most m squared, then the profile at the covariance threshold is strictly smaller than the profile at 1/sqrt(mn). This is a scalar comparison; it does not assert existence of a state with the prescribed spectrum.

**Theorem 1.11 (The uniform spectrum gives a strict scalar gap).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.uniform_profile_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.uniform_profile_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For m and n at least two and 2 at most ell at most m squared, the profile at the covariance threshold is strictly smaller than its value at 1/m squared. This scalar inequality does not impose a dimensional condition for realizing the uniform spectrum.

**Theorem 1.12 (The supported spectrum gives a strict scalar gap).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.exceptional_profile_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.exceptional_profile_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For m and n at least two and 2 at most ell at most m squared, the profile at the covariance threshold is strictly smaller than its value at 1/(m sqrt(m squared minus one)). The case m=2 is included by a separate rational comparison. This scalar inequality does not assert existence of a supported state.

**Theorem 1.13 (The exact multiset profile).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymm_cons_replicate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymm_cons_replicate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For natural N and j and arbitrary real a and b, the degree j+1 elementary symmetric function of one entry a and N copies of b equals choose(N,j+1) times b to the j+1 plus choose(N,j) times a times b to the j. Repeated and zero entries, arbitrary signs, and degrees exceeding the multiset size are included.

**Theorem 1.14 (The row Gram spectral bridge).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.singularVector_eq_sqrt_rowGram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.singularVector_eq_sqrt_rowGram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For every complex matrix on finite row and column types and every row singular index, the native row singular value equals the square root of the corresponding descending eigenvalue of its positive row Gram matrix. This common bridge serves both the separable bound and the constructed witness spectra.

**Theorem 1.15 (The universal separable realignment bound).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separable_esymm_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separable_esymm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Commentary.*

For natural dimensions 2 at most m strictly less than n, order ell from two through m squared, and every separable complex density matrix on their tensor product, the elementary symmetric singular-value function of its realignment is at most the profile at the covariance threshold. The live proof combines the real Hermitian-coordinate spectral transport and covariance tail constraints with the Newton and Maclaurin induction.

**Theorem 1.16 (The sharp elementary-symmetric tail-budget bound).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymmVec_le_schurProfile_fin`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymmVec_le_schurProfile_fin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze (2011). *A note on the realignment criterion*. DOI: [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304). URL: <https://arxiv.org/abs/1103.2499v2>.

*Acknowledgement.* Terence Tao (2026). *The Newton and Maclaurin inequalities for symmetric polynomials*. URL: <https://github.com/leanprover-community/mathlib4/blob/e3c1793d0e097d9b8d782a323e91c99c2ef0d64c/Mathlib/Analysis/MeanInequalitiesSymmetric.lean>.

*Commentary.*

Let k be at least two and let ell lie from two through k. Suppose a nonnegative real vector s of length k has total mass at most one, the sum of all coordinates except index zero is at most 1-delta, and delta lies from 1/k through one. Then the degree ell elementary symmetric function of s is at most the one-heavy-coordinate profile at delta. No ordering hypothesis is required.

Increase coordinate zero until the total mass is one, keeping the remaining entries fixed. Coordinate monotonicity does not decrease the symmetric function. The completed first coordinate a is at least delta. Splitting the symmetric function according to whether coordinate zero is selected leaves two elementary symmetric functions of the tail.

Newton's inequality bounds every adjacent normalized coefficient ratio by the first ratio. Induction gives Maclaurin's bound: the degree j elementary symmetric function of N nonnegative entries is at most choose(N,j) times their arithmetic mean to the j. The proof first treats strictly positive entries and then passes to nonnegative entries by continuity after adding a common positive quantity. Applying this bound to both tail terms gives the profile at a. Its derivative is ((ell-1)/(k-1)) choose(k-1,ell-1) b to the ell-2 times (b-a), with b=(1-a)/(k-1). It is strictly negative inside the interval from 1/k to one; continuity includes both endpoints. This strict decrease gives the required profile bound at delta.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymmSV`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymmVec`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymmVec_le_schurProfile_fin`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.esymm_cons_replicate`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.exceptional_profile_gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.main_profile_gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.realign`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.schurProfile`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separableThreshold`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separableThreshold_gt_uniform`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separableThreshold_lt_one`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.separable_esymm_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.singularVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.singularVector_eq_sqrt_rowGram`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.tailMean`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.uniform_profile_gap`
- Dependency: [D5/S3/Analytic/HypergeometricShiftTuran/Defs](../../../Analytic/HypergeometricShiftTuran/Defs.md)
- Dependency: [D5/S3/Analytic/RealRootedCoefficientNewton](../../../Analytic/RealRootedCoefficientNewton.md)
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance](CorrelationMinorNormCovariance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../../Information/SLDSpectralEnergy.md)
