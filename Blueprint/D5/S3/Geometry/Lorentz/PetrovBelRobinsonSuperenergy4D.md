# Petrov invariants and Bel–Robinson superenergy

## Abstract

The Weyl quartic, its projective principal directions, and the spinor form of gravitational superenergy.

The symmetric four-spinor pairs with its complex conjugate, with one Hermitian Pauli matrix inserted in each slot. A future causal slot is a sum of two rank-one spinor matrices. Expanding all four such sums turns the combined contraction into a sum of squared moduli.

The binary quartic helper proves symmetry under each permutation of the four spinor slots, equivariance of the spinor form under the matrix action, and determinant exponents four and six for the quadratic and cubic invariants. For determinant one, both invariants and their discriminant are fixed. At a double principal direction the discriminant vanishes, and at a triple direction both invariants vanish. The finite and infinite projective charts both enter these conclusions.

The canonical D and II representatives have invariants three times the middle coefficient squared and minus its cube. The III and N representatives and the zero spinor have both invariants zero. For the symmetric I representative with end coefficient a and middle coefficient b, the discriminant is a squared times the square of a squared minus nine b squared. The I representative has nonzero discriminant when a is nonzero and differs from both three b and minus three b.

The D representative has a double direction in each of the two standard charts. The II representative with both coefficients nonzero has a double direction at infinity and two distinct simple finite directions. The III representative has a triple direction at infinity and a simple direction at zero. The N representative has a quadruple direction at infinity. The O polynomial vanishes identically.

**Theorem 1.1 (The Weyl spinor on the finite null screen).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.weyl_spinor_null_screen`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.weyl_spinor_null_screen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

The symmetric spinor induced by a Weyl curvature has the same value on four copies of the column with entries z and one as the complex null-screen tide at z.

**Theorem 1.2 (Coulomb and plane-wave spinors).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.petrov_coulomb_and_wave_spinors`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.petrov_coulomb_and_wave_spinors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

The Schwarzschild curvature in the given screen has only the middle coefficient, equal to four times mass divided by radius cubed. The plane-wave curvature after the determinant-one chart inversion has only the last coefficient, equal to minus four times the wave amplitude.

**Theorem 1.3 (Electric and magnetic curvature components).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.weyl_spinor_electric_magnetic`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.weyl_spinor_electric_magnetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

In the chosen screen orientation form the chiral matrix by subtracting the imaginary unit times the magnetic matrix from the electric matrix. Writing Q for this matrix and i for the imaginary unit, the five components in order are 2(Q00 − Q11) − 4iQ01, 2Q02 − 2iQ12, −2(Q00 + Q11), −2Q02 − 2iQ12, and 2(Q00 − Q11) + 4iQ01.

**Theorem 1.4 (Reality and symmetry in every slot).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_totally_symmetric_and_real`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_totally_symmetric_and_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

The complex contraction has zero imaginary part. Every permutation of the four vector arguments preserves it, and its real part is the evaluation of the associated real multilinear map.

**Theorem 1.5 (All metric traces vanish).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_completely_traceless`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_completely_traceless` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

For any two distinct slots, substitute each coordinate vector into both slots and sum the resulting contractions with weights minus one in the time coordinate and one in the spatial coordinates. The result is zero for all values in the other two slots.

**Theorem 1.6 (Invariance under chiral phase rotations).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_so2_duality_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_so2_duality_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

Multiplying the Weyl spinor by the exponential of the imaginary unit times a real angle preserves the contraction in all four vector arguments.

**Theorem 1.7 (Positive definite rest-frame superenergy).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_superenergy_positive_definite`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_superenergy_positive_definite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

With all four arguments the unit time vector, the superenergy is the sum of the five squared coefficient moduli with weights one, four, six, four and one. It is nonnegative and vanishes exactly when the spinor is zero.

**Theorem 1.8 (Rest energy from the Weyl matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_electric_magnetic_density`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_electric_magnetic_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

In the null-screen normalization, the density of the spinor of a Weyl curvature is sixteen times the sum of the traces of the squared electric and magnetic matrices.

**Theorem 1.9 (Rank-one decomposition on the future causal cone).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.future_causal_spinor_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.future_causal_spinor_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

If the time coordinate is nonnegative and its square dominates the squared spatial norm, the Pauli matrix of the vector admits a sum of two rank-one spinor matrices. The formula uses a positive first diagonal pivot or, for a vanishing first diagonal, the remaining single diagonal entry.

**Theorem 1.10 (The Pauli image of the future causal cone).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.pauli_positive_semidefinite_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.pauli_positive_semidefinite_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

The Hermitian Pauli matrix of a vector is positive semidefinite exactly when that vector is future causal.

**Theorem 1.11 (Dominance for independently chosen causal vectors).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_dominant_superenergy_condition`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_dominant_superenergy_condition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

When each of the four vector arguments is future causal, the real contraction is nonnegative.

**Theorem 1.12 (Sharp super-Poynting bound).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_super_poynting_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_super_poynting_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

The sum of the three squared super-Poynting components is bounded above by the square of the rest-frame superenergy.

**Theorem 1.13 (Canonical wave and Coulomb flux).**

Lean statement: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_typeN_and_typeD_flux`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_typeN_and_typeD_flux` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* José M. M. Senovilla (2000). *Super-energy tensors*. DOI: [10.1088/0264-9381/17/14/313](https://doi.org/10.1088/0264-9381/17/14/313). URL: <https://arxiv.org/abs/gr-qc/9906087>.

*Commentary.*

For the canonical type N spinor the density is the squared modulus of its coefficient. The first two flux components vanish and the third is minus the density, so the flux has norm equal to the density. The canonical type D spinor has density six times the squared modulus of its middle coefficient and zero flux.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_completely_traceless`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_dominant_superenergy_condition`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_electric_magnetic_density`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_so2_duality_invariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_super_poynting_bound`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_superenergy_positive_definite`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_totally_symmetric_and_real`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.belRobinson_typeN_and_typeD_flux`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.future_causal_spinor_decomposition`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.pauli_positive_semidefinite_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.petrov_coulomb_and_wave_spinors`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.weyl_spinor_electric_magnetic`
- Truth anchor: `D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D.weyl_spinor_null_screen`
- Dependency: [D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D](KerrSchildWeylDoubleCopy4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D](PerturbedCausalOrderWeyl4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/SL2CLorentzCover4D](SL2CLorentzCover4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
