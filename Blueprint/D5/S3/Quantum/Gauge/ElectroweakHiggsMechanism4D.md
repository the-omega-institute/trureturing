# Electroweak symmetry breaking

## Abstract

The Higgs vacuum stabilizer, gauge boson mass matrix and scalar fluctuation spectrum for one complex doublet.

The neutral component of a hypercharge one-half doublet acquires vacuum value v divided by the square root of two. Its electric charge is zero. The vacuum fixes the photon direction and gives equal masses to the two charged weak modes. The scalar potential gives a positive radial mass and three vanishing Goldstone masses at tree level.

**Definition 1.1 (Scalar doublet potential).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

The potential is lambda times the square of the difference between the squared doublet norm and v squared over two.

**Definition 1.2 (Neutral vacuum).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsVac`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsVac` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

The upper component is zero and the lower component is v divided by the square root of two.

**Theorem 1.3 (Lower bound).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive lambda makes the potential nonnegative.

**Theorem 1.4 (Vacuum manifold).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive lambda the potential vanishes exactly on the sphere of squared doublet norm v squared over two.

**Theorem 1.5 (Vacuum energy).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential_vacuum_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential_vacuum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chosen neutral doublet lies on the zero set of the potential.

**Definition 1.6 (Infinitesimal gauge action).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewGeneratorAction`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewGeneratorAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

The Pauli matrices divided by two give the weak action. Hypercharge acts by one half of the identity.

**Theorem 1.7 (Electric charge direction).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_vacuum_stabilizer_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_vacuum_stabilizer_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

At positive v the first two weak coordinates vanish in the stabilizer and the third weak coordinate equals the hypercharge coordinate.

**Definition 1.8 (Doublet group action).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewGroupAction`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewGroupAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

The unit pair of complex coordinates specifies the weak matrix and the unit phase multiplies both output components.

**Theorem 1.9 (Vacuum stabilizer circle).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_group_stabilizer_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_group_stabilizer_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At positive v, an element of the weak group and hypercharge circle fixes the vacuum exactly when the weak matrix is diagonal with first entry equal to the hypercharge phase. The unit phases parametrize the stabilizer.

**Definition 1.10 (Gauge term at the vacuum).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.gaugeDerivative`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.gaugeDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

The gauge term multiplies the weak coordinates by g and the hypercharge coordinate by g prime and includes the factor minus i.

**Theorem 1.11 (Gauge coupling to the doublet).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.gaugeDerivative_eq_generator_action`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.gaugeDerivative_eq_generator_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The component expression is the infinitesimal action at the vacuum after coupling substitution and multiplication by minus i.

**Definition 1.12 (Gauge mass quadratic form).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewMassQuadratic`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewMassQuadratic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

Twice the sum of the squared complex norms of the gauge term gives the real mass quadratic form.

**Theorem 1.13 (Charged and neutral terms).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_mass_quadratic_form`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_mass_quadratic_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The charged term is g²v²/4 times the sum of the first two field squares. The neutral term is v²/4 times the square of g times the third field minus g prime times the hypercharge field.

**Definition 1.14 (Weak mixing cosine).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.cosW`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.cosW` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

Divide the weak coupling by the square root of the sum of the squared couplings.

**Definition 1.15 (Weak mixing sine).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.sinW`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.sinW` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

Divide the hypercharge coupling by the square root of the sum of the squared couplings.

**Definition 1.16 (Charged weak mass squared).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.mWSq`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.mWSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

Multiply the square of the weak coupling by v squared over four.

**Definition 1.17 (Neutral weak mass squared).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.mZSq`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.mZSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

Multiply the sum of the squared couplings by v squared over four.

**Definition 1.18 (Photon coordinate).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.photonMode`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.photonMode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

Weight the third weak coordinate by the mixing sine and the hypercharge coordinate by the mixing cosine and add them.

**Definition 1.19 (Z coordinate).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.zMode`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.zMode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

Subtract the hypercharge coordinate times the mixing sine from the third weak coordinate times the mixing cosine.

**Theorem 1.20 (Orthogonal neutral rotation).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_neutral_rotation_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_neutral_rotation_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When at least one coupling is nonzero, the Z and photon coordinates preserve the sum of squares.

**Theorem 1.21 (Diagonal gauge masses).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_mass_diagonalized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_mass_diagonalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero coupling pair the two charged coordinates have coefficient M W squared and the Z coordinate has coefficient M Z squared. The photon has coefficient zero.

**Definition 1.22 (Gauge mass matrix).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewMassMatrix`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewMassMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

The symmetric matrix acts on the three real weak coordinates followed by the real hypercharge coordinate.

**Theorem 1.23 (Matrix of the gauge quadratic form).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_gauge_mass_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_gauge_mass_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Contracting the matrix with the real field vector on both sides recovers twice the squared gauge derivative norm.

**Theorem 1.24 (Charged weak eigenvectors).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_W_mass_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_W_mass_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first two coordinate vectors have the same squared mass eigenvalue.

**Theorem 1.25 (Massless photon).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_photon_massless`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_photon_massless` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero coupling pair the normalized photon direction belongs to the kernel of the mass matrix.

**Theorem 1.26 (Neutral weak eigenvector).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_Z_mass_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_Z_mass_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero coupling pair the normalized Z direction has squared mass given by the sum of the squared couplings times v squared over four.

**Theorem 1.27 (Strict mass ordering).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_mass_order`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_mass_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive couplings and positive v give positive charged mass squared and a strictly larger neutral weak mass squared.

**Theorem 1.28 (Custodial ratio).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_custodial_rho_eq_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_custodial_rho_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive g and v give a ratio of one after dividing charged mass squared by the product of Z mass squared and the squared mixing cosine.

**Theorem 1.29 (Electromagnetic coupling).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_electric_charge_relations`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_electric_charge_relations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive couplings give equal electric charge from the two neutral projections and a reciprocal squared charge equal to the sum of reciprocal squared couplings.

**Definition 1.30 (Real fluctuation coordinates).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsFluctuation`

*Formalization.* `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsFluctuation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Steven Weinberg (1967). *A Model of Leptons*. DOI: [10.1103/PhysRevLett.19.1264](https://doi.org/10.1103/PhysRevLett.19.1264). URL: <https://doi.org/10.1103/PhysRevLett.19.1264>.

*Commentary.*

The doublet is parametrized by three Goldstone coordinates and the radial coordinate h, each scaled by the inverse square root of two.

**Theorem 1.31 (Exact fluctuation potential).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_fluctuation_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_fluctuation_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The potential is lambda over four times the square of the sum of 2 v h and the four squared fluctuation coordinates.

**Theorem 1.32 (Quadratic, cubic and quartic terms).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_fluctuation_homogeneous_terms`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_fluctuation_homogeneous_terms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With q the sum of fluctuation squares, the three terms are lambda v squared h squared, lambda v h q and lambda q squared over four.

**Theorem 1.33 (Hessian quadratic form).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_hessian_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_hessian_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second directional derivative at the vacuum is 2 lambda v squared times the square of the radial component of the direction.

**Theorem 1.34 (Higgs and Goldstone masses).**

Lean statement: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_hessian_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_hessian_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The radial coordinate has positive mass squared for positive lambda and v. Each of the three Goldstone coordinate second derivatives vanishes.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.cosW`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewGeneratorAction`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewGroupAction`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewMassMatrix`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ewMassQuadratic`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_W_mass_sq`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_Z_mass_sq`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_custodial_rho_eq_one`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_electric_charge_relations`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_gauge_mass_matrix`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_mass_diagonalized`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_mass_order`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_mass_quadratic_form`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_neutral_rotation_orthogonal`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.ew_photon_massless`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.gaugeDerivative`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.gaugeDerivative_eq_generator_action`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsFluctuation`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential_eq_zero_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential_nonneg`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsPotential_vacuum_zero`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgsVac`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_fluctuation_expansion`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_fluctuation_homogeneous_terms`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_group_stabilizer_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_hessian_diagonal`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_hessian_spectrum`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.higgs_vacuum_stabilizer_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.mWSq`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.mZSq`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.photonMode`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.sinW`
- Truth anchor: `D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D.zMode`
