# Type-I seesaw masses and neutrino oscillations

## Abstract

Exact seesaw diagonalization and vacuum oscillation identities.

The seesaw calculation gives signed eigenvalues for one real Dirac and Majorana pair and a Schur block for several flavors. Vacuum propagation assigns a unit complex phase to each mass eigenstate. The interference of these phases yields the three-flavor CP difference.

**Definition 1.1 (Type-I seesaw matrix).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawMatrix`

*Formalization.* `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The diagonal contains zero and the Majorana mass. Both off-diagonal entries are the Dirac mass.

**Definition 1.2 (Heavy mass magnitude).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawHeavy`

*Formalization.* `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawHeavy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

Add the Majorana mass to the square root of the discriminant and halve the sum.

**Definition 1.3 (Light mass magnitude).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawLight`

*Formalization.* `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawLight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

Subtract the Majorana mass from the square root of the discriminant and halve the difference.

**Theorem 1.4 (Determinant and trace).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_det_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_det_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The determinant is minus the squared Dirac mass. The trace is the Majorana mass.

**Theorem 1.5 (Mass product and difference).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_mass_product_and_diff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_mass_product_and_diff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The two magnitudes multiply to the squared Dirac mass. The heavy magnitude minus the light magnitude equals the Majorana mass.

**Definition 1.6 (Oriented eigenvector rotation).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawRotation`

*Formalization.* `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawRotation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The eigenvectors use the heavy and Dirac masses as coordinates and are normalized by a common positive length. When the Dirac mass is zero the ordered coordinate axes give the rotation directly.

**Theorem 1.7 (Exact orthogonal diagonalization).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_orthogonal_diagonalization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_orthogonal_diagonalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The rotation has determinant one, its transpose is its inverse, and the diagonal contains the additive inverse of the light magnitude followed by the heavy magnitude.

**Theorem 1.8 (Exact hierarchy correction).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_exact_correction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_exact_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

For nonzero Majorana mass, subtracting the light magnitude from the seesaw estimate gives the squared light magnitude divided by the Majorana mass.

**Theorem 1.9 (Strict mass hierarchy).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_strict_hierarchy_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_strict_hierarchy_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

For a positive Majorana mass and a nonzero Dirac mass, the light magnitude lies strictly between zero and the seesaw estimate. The heavy magnitude exceeds the Majorana mass, and the positive error is strictly less than the fourth Dirac power divided by the third Majorana power.

**Theorem 1.10 (Large Majorana mass limit).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_asymptotic_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_asymptotic_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

At fixed Dirac mass, the light magnitude tends to zero, its product with the Majorana mass tends to the squared Dirac mass, and the heavy-to-Majorana ratio tends to one.

**Definition 1.11 (Multiflavor mass block).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.blockSeesaw`

*Formalization.* `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.blockSeesaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The leading square block is zero. The off-diagonal blocks are the Dirac matrix and its transpose. The remaining block is the Majorana matrix.

**Theorem 1.12 (Exact Schur congruence).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.block_seesaw_schur_congruence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.block_seesaw_schur_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

A triangular shear removes the off-diagonal blocks when the Majorana matrix is symmetric and invertible. The light block is minus the Dirac matrix times the Majorana inverse times the Dirac transpose.

**Theorem 1.13 (Multiflavor determinant).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.block_seesaw_det`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.block_seesaw_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The determinant is the squared Dirac determinant times minus one to the flavor count. The Schur determinant proof uses invertibility of the Majorana block.

**Definition 1.14 (Vacuum transition amplitude).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscAmp`

*Formalization.* `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscAmp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

Sum the final-flavor mixing entry times the negative-phase propagation factor times the conjugate of the initial-flavor entry over the mass indices.

**Definition 1.15 (Vacuum transition probability).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb`

*Formalization.* `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

Take the squared complex norm of the amplitude.

**Theorem 1.16 (Nonnegative probability).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The squared norm is nonnegative for every mixing matrix and baseline.

**Theorem 1.17 (Zero baseline).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_zero_baseline`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_zero_baseline` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

Row unitarity gives probability one for survival and zero for transition at zero baseline.

**Theorem 1.18 (Probability normalization).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_unitarity_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_unitarity_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The propagation matrix is unitary. Each sum over initial or final flavors is one, and each entry lies at most at one.

**Theorem 1.19 (Common mass-squared shift).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_common_shift_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_common_shift_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

A common mass-squared shift contributes the same unit phase to every summand and cancels in the squared norm.

**Definition 1.20 (Antineutrino mixing matrix).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.antiMatrix`

*Formalization.* `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.antiMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

Conjugate each entry of the mixing matrix.

**Theorem 1.21 (Vacuum CPT identity).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_cpt_symmetry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_cpt_symmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The antineutrino transition probability equals the neutrino probability for the reversed flavor pair.

**Theorem 1.22 (Survival probability under conjugation).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_survival_cp_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_survival_cp_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

Conjugating the mixing matrix leaves every survival probability unchanged.

**Definition 1.23 (Two-flavor rotation).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.rot2`

*Formalization.* `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.rot2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The two real rotation entries in each row are embedded in the complex numbers.

**Theorem 1.24 (Two-flavor vacuum probability).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.two_flavor_oscProb_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.two_flavor_oscProb_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The transition probability is the product of the squared sine of twice the mixing angle and the squared sine of half the relative phase. Survival is one minus this product.

**Definition 1.25 (CP difference).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.cpAsymmetry`

*Formalization.* `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.cpAsymmetry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

Subtract the antiparticle probability from the particle probability for the same ordered flavors.

**Theorem 1.26 (Antisymmetry of the CP difference).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.cpAsymmetry_antisymm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.cpAsymmetry_antisymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

Reversing flavors negates the CP difference. The survival difference is zero.

**Theorem 1.27 (Jarlskog sine product).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_jarlskog`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_jarlskog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

For three unitary flavors, the CP difference is sixteen times the quartet of the ordered flavors and first two mass indices times the three half-phase sines. The pairs zero-one and one-two have the same quartet sign. The pair zero-two has the opposite sign.

**Theorem 1.28 (Magnitude of the CP difference).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The magnitude is bounded by sixteen times the magnitude of the quartet because each sine has magnitude at most one.

**Theorem 1.29 (Exact zero criterion).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

The CP difference vanishes exactly when the quartet or one of the three half-phase sines vanishes.

**Theorem 1.30 (Degenerate mass pair).**

Lean statement: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_zero_of_degenerate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_zero_of_degenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Nunokawa, Stephen J. Parke and José W. F. Valle (2008). *CP Violation and Neutrino Oscillations*. DOI: [10.1016/j.ppnp.2007.10.001](https://doi.org/10.1016/j.ppnp.2007.10.001). URL: <https://arxiv.org/abs/0710.0554>.

*Commentary.*

Equality of any two distinct mass-squared entries makes the corresponding half-phase sine zero.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.antiMatrix`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.blockSeesaw`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.block_seesaw_det`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.block_seesaw_schur_congruence`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.cpAsymmetry`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.cpAsymmetry_antisymm`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscAmp`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_common_shift_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_cpt_symmetry`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_nonneg`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_survival_cp_zero`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_unitarity_sum`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.oscProb_zero_baseline`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.rot2`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawHeavy`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawLight`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawMatrix`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesawRotation`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_asymptotic_limits`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_det_trace`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_exact_correction`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_mass_product_and_diff`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_orthogonal_diagonalization`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.seesaw_strict_hierarchy_bounds`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_jarlskog`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_zero_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_zero_of_degenerate`
- Truth anchor: `D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.two_flavor_oscProb_formula`
- Dependency: [D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D](CKMFlavorJarlskog4D.md)
