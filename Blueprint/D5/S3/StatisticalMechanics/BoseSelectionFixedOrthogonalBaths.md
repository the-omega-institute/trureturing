# Five selected modes with fixed orthogonal baths

## Abstract

Fixed coordinate baths, actual Hamiltonians, normalized uniqueness and open matrix sets in all dimensions at least five.

Haobo Ma and Wenlin Zhang, Five Bose-selected modes with orthogonal bath projectors (10 November 2026, source release 440890785, CC BY 4.0), continue the existing Schnell–Ketzmerick–Eckardt family. The signed-Pfaffian method is credited to Knebel, Weber, Krüger and Frey (2015), Methods equation (19). This is not a second paper or a cleared priority claim.

The repository asym is used unchanged: spow(d,e(j)-e(i)) times the difference of the two normalized product weights, with the common positive prefactor suppressed. IsSelected alone does not normalize occupation. Every normalized theorem here explicitly imposes sum w=1. Labels zero and one are the source coordinate bath vectors e1 and e2.

At dimension five use the source orthogonal rows a=(1,-1,-1,-2,-3)/4 and b=(-3,11,-1,-2,-3)/12, energies 1 through 5, f=(1,1,1,4,9)/16 and g=(9,121,1,4,9)/144. The normalized occupation is (40,288,189,18,1)/536. The source displays the particular reflector Q=I-rrᵀ/12, r=(3,1,1,2,3), and H=(1/48)[[201,39,27,30,9],[39,105,5,2,-9],[27,5,145,-6,-21],[30,2,-6,164,-66],[9,-9,-21,-66,105]]. The Lean construction completes the same two rows to a basis and does not identify its choice with that particular reflector. Its energies and occupations agree exactly.

For k=n-5 positive the proof specializes the source Gram–Schmidt construction to t=1/(100k). Thus U=29/25, alpha=1/29 and V=117/116. Old weights are f=(25/464,25/464,25/464,25/116,225/464), g=(25/377,25921/30537,13/2349,52/2349,13/261); each extra level has f=4/(29k), g=25/(3393k). The positive kernel integers are (2066989123199,11682807236100,9292388902650,1489507236225,18634875975), with sum 24550327374149. Arbitrary extra energies strictly above five give the same strict negative outside-drift argument; the final simple-spectrum witness chooses 6 through n.

The source first proves existence using small positive t; the uniform certificate fixes t explicitly and proves the same all-finite-dimension result. For the extra levels f/g=468/25 exceeds 16, while every old g/f is below 16. Each old contribution to each new-row drift is therefore negative. The selected block is common to all positive k. The construction does not shrink the domain to a tested list of dimensions.

The old BS1–BS8 record is preserved. BS1 is the earlier independent-weight cubic example with F=(5,4,4,4,4), G=(6,6,3,3,3), common sum 21 and occupation (14,56,21,8,1)/100, and its positive-Pfaffian open family remains in the original refutation. BS2 records rank four and normalized uniqueness for that earlier block. For its unnormalized integer cubic matrix B, deleting the first row and column gives a four by four principal minor with determinant 504²; the corresponding minor of A=B/441 has determinant 504²/441⁴. The leading four by four minor of B instead has determinant 36². The general skew-support and minor lemmas here supply reusable mechanisms but no new named assertion silently certifies the entire earlier neighborhood.

BS3 remains the source positive/inverted bath rate statement for T1>0>T2: with delta=e(i)-e(j), R_ij=f_i f_j delta³/(exp(delta/T1)-1)-g_i g_j delta³/(exp(delta/T2)-1) off the diagonal. Its nonnegativity and R_ij-R_ji=A_ij require their own exponential-denominator proof; no experimental inverted-bath realization is inferred. BS4 is the earlier joint neighborhood in exponent, energies and independent couplings; fixed-matrix local exponent persistence here does not silently finish that broader joint statement.

BS5 is the earlier all-M independent-weight extension with new normalized weights 2t/(1+2kt) and t/(1+kt), appropriately rescaled old weights, distinct higher energies and strict outside drift. The present all-M construction enforces the additional orthogonal-amplitude constraint and does not erase or substitute away that earlier parameter family.

BS6 retains the source common odd integer monomial q at least one, one or more baths, each with a nonzero signed strength and strictly positive couplings, a nonempty selected set and a one-dimensional selected kernel: M_S ≤ (q+1) M_B -1. The source also derives the one-dimensional selected kernel from uniqueness of the normalized strict solution by a small normalized kernel-direction perturbation. Its bath-power factorization, even skew rank and this nondegeneracy implication are not formalized by this return. BS7 retains the source strictly ordered energies, d>0 and any positive number of baths with strictly positive couplings and strengths of a common nonzero sign: the only selected mode is the lowest for positive signs and highest for negative signs, with the earlier single-bath attribution intact. BS8 retains the necessity of nondegeneracy (opposite identical couplings give A=0) and the open seven-mode attainability question. None is replaced by an exponent-independent bound.

The written note turns open matrix sets into positive GOE/GUE probability using their everywhere positive Gaussian densities on the actual real symmetric and complex Hermitian spaces. The Lean source proves the open sets, not the identification of either actual law or its full support. A generic measure with an assumed positive-open-set property does not close this gap. No ensemble frequency, almost-sure typicality, dimension-uniform probability lower bound or matrix-neighborhood radius follows.

The separate uniform certificate records a proposed common closed exponent interval |d-3|≤1/128: old signed-Pfaffian terms are cubic terms times G^(d-3), 1≤G≤16; the written estimate |G^(d-3)-1|<1/40 and the exact inequalities 40p_i(3)>sum absolute cubic terms keep the signs positive. Negative old-to-new gaps retain their signed-power sign. This written all-dimension argument and matrix openness at each such exponent remain unformalized. The checked matrix-dependent local open exponent set does not prove that common interval.

The positive energy-gap entrywise multiplier depends on both indices, so the four coefficients obtained after summing over j depend on i. It therefore does not preserve the old Ohmic four-vector relation or Pfaffian signs. The Ohmic theorem, finite numerical samples, continuum, random-rate, kicked-rotor, interacting, photonic and autonomous chaotic-model questions keep their original boundaries. The artificial Lorentzian reservoir construction of Petiziol–Eckardt (2024) uses a different spectral family.

**Definition 1.1 (increasingSpectrum).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For a Hermitian matrix of any finite dimension over an RCLike field, reverse the library descending real eigenvalue enumeration. Multiplicities remain; strict monotonicity is a separate hypothesis.

**Definition 1.2 (lagrangeProjector).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.lagrangeProjector`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.lagrangeProjector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For a matrix H, real vector e and index i, multiply the Lagrange factors (H-e(j)I)/(e(i)-e(j)) for j different from i, in the fixed list order. It is a spectral projection when H has that simple spectrum; no such interpretation is claimed for repeated energies.

**Theorem 1.3 (lagrangeProjector_spectralMatrix).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.lagrangeProjector_spectralMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.lagrangeProjector_spectralMatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every dimension, RCLike field, unitary U and injective real energy vector e, the i-th polynomial Lagrange projector of U diag(e) U* equals U times the i-th coordinate projector times U*. This supplies the intrinsic spectral/physical rate bridge without choosing eigenvector phases.

**Definition 1.4 (HermitianSpace).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.HermitianSpace`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.HermitianSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

The subtype of n by n matrices satisfying IsHermitian, with the inherited ordinary matrix topology. At the real field this is the real symmetric matrix space; at the complex field it is the full Hermitian matrix space.

**Theorem 1.5 (continuous_increasingSpectrum_complex).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.continuous_increasingSpectrum_complex`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.continuous_increasingSpectrum_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

Each increasing ordered eigenvalue is continuous on the full complex Hermitian n by n matrix space. The proof uses the existing HermitianEigenvaluePerturbation entrywise perturbation bound, not continuity merely along real perturbations.

**Theorem 1.6 (continuous_increasingSpectrum_real).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.continuous_increasingSpectrum_real`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.continuous_increasingSpectrum_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

Each increasing ordered eigenvalue is continuous on the entire real symmetric n by n matrix space, including repeated eigenvalues. The proof restricts complex Hermitian eigenvalue continuity along complexification and proves agreement of ordered spectra.

**Definition 1.7 (matrixWeight).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.matrixWeight`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.matrixWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

Take the real diagonal entry at coordinate r of the Lagrange projector at ordered level i of the actual Hermitian matrix. On the simple spectrum domain this is the physical fixed-coordinate-bath weight.

**Definition 1.8 (matrixRates).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.matrixRates`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.matrixRates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For n at least five and a real exponent d, apply the original asym to the increasing spectrum and the two intrinsic matrixWeight vectors at coordinates zero and one. Under a simple ordered diagonalization matrixRates_eq identifies these rates with physical expectation rates.

**Theorem 1.9 (matrixRates_eq).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.matrixRates_eq`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.matrixRates_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every real exponent d, n at least five, Hermitian H and unitary diagonalization H=U diag(e) U* with strictly increasing e, the intrinsic matrixRates equal fixedBathRates from the actual expectations of the two fixed coordinate projections. This equality holds for all real d; the source physical exponent domain is d positive.

**Theorem 1.10 (exists_open_fixedBathHamiltonians).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.exists_open_fixedBathHamiltonians`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.exists_open_fixedBathHamiltonians` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For any RCLike field and n at least five, there exists a nonempty open set of simple-spectrum matrices. Every member has a normalized first-five cubic selection, selected rank four and global normalized uniqueness allowing all competing supports. The exported conclusion leaves strict positivity of all bath weights throughout O unspecified. Ordered-spectrum continuity is supplied inside the proof: the canonical real or complex field equivalence transports the corresponding continuity theorem above, including at repeated eigenvalues. The real symmetric conclusion is the application exists_open_fixedBathHamiltonians (𝕜 := ℝ) hn; the full complex Hermitian conclusion uses (𝕜 := ℂ). Both retain arbitrary finite n at least five and every competing support.

**Theorem 1.11 (fixedBath_local_exponent).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.fixedBath_local_exponent`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.fixedBath_local_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every dimension n at least five, RCLike field and fixed Hermitian H whose cubic rates satisfy StrictFiveCertificate on the first five indices, there is an open set I of real exponents containing three. For each d in I the same fixed matrix and baths have normalized first-five selection, rank four and global normalized uniqueness. The set may depend on H; it need not be connected or positive as stated, but intersecting with the positive reals and taking an interval about three gives the source local physical claim. No common radius or simultaneous matrix/exponent neighborhood is asserted.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.HermitianSpace`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.continuous_increasingSpectrum_complex`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.continuous_increasingSpectrum_real`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.exists_open_fixedBathHamiltonians`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.fixedBath_local_exponent`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.increasingSpectrum`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.lagrangeProjector`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.lagrangeProjector_spectralMatrix`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.matrixRates`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.matrixRates_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths.matrixWeight`
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../SpectralTopology/HermitianEigenvaluePerturbation.md)
- Dependency: [D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction](BoseSelectionFixedBathConstruction.md)
