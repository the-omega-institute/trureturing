# Fixed bath Hamiltonian construction

## Abstract

Fixed orthogonal bath realization and normalized five-mode selection in every finite dimension at least five.

Following Haobo Ma and Wenlin Zhang, Five Bose-selected modes with orthogonal bath projectors (CC BY 4.0), the same two fixed coordinate projections are realized by orthonormal bath amplitude rows. The five-dimensional rows and the higher-dimensional rational certificates give actual real symmetric and complex Hermitian Hamiltonians. The occupation is normalized explicitly, and uniqueness allows competitors on arbitrary supports. This construction uses the original cubic asymmetry and signed Pfaffian proof; the matrix topology and complete scientific scope are stated in BoseSelectionFixedOrthogonalBaths.

**Definition 1.1 (coordinateProjector).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.coordinateProjector`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.coordinateProjector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every finite dimension n, RCLike scalar field and coordinate r, this is the diagonal matrix with one at r and zero elsewhere. It is independent of the Hamiltonian.

**Definition 1.2 (coordinateWeight).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.coordinateWeight`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.coordinateWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For any coordinate r and vector v over an RCLike field, take the real part of the expectation of the fixed coordinate projection in v. For a unit eigenvector it is the squared modulus of its r-coordinate.

**Definition 1.3 (spectralMatrix).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.spectralMatrix`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.spectralMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For a unitary n by n matrix U and a real energy vector e, form U diag(ofReal(e)) U*. No ordering or simplicity is assumed in this definition.

**Theorem 1.4 (selected_support_eq).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.selected_support_eq`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.selected_support_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For any finite real skew-symmetric matrix and any two strict IsSelected solutions, their supports coincide. Neither normalization nor a preassigned support is required. The proof pairs the two nonnegative occupations against the skew matrix and rules out a missing support index by strict negativity.

**Theorem 1.5 (rank_four_of_fivePfaffian).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.rank_four_of_fivePfaffian`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.rank_four_of_fivePfaffian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

A real skew-symmetric five by five matrix whose last signed principal Pfaffian is nonzero has rank exactly four. Its leading four by four minor is the square of that Pfaffian; the original Pfaffian kernel prevents full rank.

**Theorem 1.6 (selected_normalized_unique).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.selected_normalized_unique`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.selected_normalized_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For a finite real skew matrix, an embedding of five indices and a normalized strict solution on that image, one nonzero last principal Pfaffian of the selected block forces every other normalized strict solution, on any support, to have that same support and occupation.

**Definition 1.7 (StrictFiveCertificate).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.StrictFiveCertificate`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.StrictFiveCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For any real n by n matrix A and embedding f of five indices, require positivity of all five signed Pfaffians of the selected principal block and strictly negative drifts outside the image for their zero extension. Skew symmetry is an additional premise of the consequence theorem.

**Theorem 1.8 (StrictFiveCertificate.selected).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.selected`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every finite real skew matrix and five-index embedding satisfying StrictFiveCertificate, normalize the zero-extended positive Pfaffian vector. It is selected, its selected block has rank four, and every normalized strict solution with arbitrary support is equal to it.

**Definition 1.9 (bathF).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.bathF`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.bathF` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every n at least five and RCLike field, choose the projection onto coordinate zero. This same projection is used for every Hamiltonian of that dimension.

**Definition 1.10 (bathG).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.bathG`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.bathG` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every n at least five and RCLike field, choose the projection onto coordinate one, orthogonal to the first bath.

**Theorem 1.11 (fixed_baths).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.fixed_baths`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.fixed_baths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every dimension n at least five over an RCLike field, bathF and bathG are Hermitian idempotents with product zero. This helper is consumed by the strengthened Hamiltonian existence theorem, so the projection laws are part of its actual conclusion.

**Definition 1.12 (fiveEmbedding).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.fiveEmbedding`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.fiveEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For n at least five, embed Fin 5 into Fin n by retaining the numerical index. On an increasing spectrum these are the first five levels.

**Definition 1.13 (firstFive).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.firstFive`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.firstFive` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For n at least five, the image of all five indices under fiveEmbedding. Its cardinality is five.

**Definition 1.14 (fixedBathRates).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.fixedBathRates`

*Formalization.* `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.fixedBathRates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For n at least five, any real exponent d, real energies e and unitary eigenbasis U, apply the original asym to the actual expectations of bathF and bathG in the columns of U. The original asym normalizes both weight vectors.

**Theorem 1.15 (exists_fixedBathHamiltonian).**

Lean statement: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.exists_fixedBathHamiltonian`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.exists_fixedBathHamiltonian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Schnell, Alexander; Ketzmerick, Roland; Eckardt, André (2018). *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*. DOI: [10.1103/PhysRevE.97.032136](https://doi.org/10.1103/PhysRevE.97.032136). URL: <https://arxiv.org/abs/1802.04088v2>.

*Commentary.*

For every natural n at least five over any RCLike field, there exists a Hermitian H with a full unitary eigenbasis and increasing simple spectrum e(i)=i+1. The same two fixed coordinate projections are Hermitian orthogonal idempotents. Their physical cubic rates have a normalized occupation on the first five levels, all five signed selected Pfaffians positive, selected rank four, and global uniqueness against every normalized IsSelected competitor on any support. Over the real and complex fields this gives actual real symmetric and complex Hermitian Hamiltonians. The five-dimensional and higher-dimensional rational occupations are distinct certificates.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.StrictFiveCertificate`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.bathF`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.bathG`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.coordinateProjector`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.coordinateWeight`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.exists_fixedBathHamiltonian`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.firstFive`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.fiveEmbedding`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.fixedBathRates`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.fixed_baths`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.rank_four_of_fivePfaffian`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.selected`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.selected_normalized_unique`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.selected_support_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction.spectralMatrix`
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../SpectralTopology/HermitianEigenvaluePerturbation.md)
- Dependency: [D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation](BoseSelectionCubicTwoBathRefutation.md)
