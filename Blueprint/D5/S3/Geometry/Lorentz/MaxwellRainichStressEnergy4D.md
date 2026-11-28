# Maxwell stress, electromagnetic invariants and causal energy flux

## Abstract

Four-dimensional electromagnetic invariants, the Maxwell stress tensor and its Rainich square.

The covariant electromagnetic tensor uses signature (+,−,−,−). Its time-space row contains the electric vector and its spatial block is the matrix of cross product by the magnetic vector. The Hodge dual exchanges the electric and magnetic vectors with signs minus and plus, respectively.

**Theorem 1.1 (Antisymmetry of the field tensor).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.fieldTensor_antisym`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.fieldTensor_antisym` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transposing the covariant field tensor negates it for every pair of electric and magnetic vectors.

**Theorem 1.2 (Square of Hodge duality).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.dualFieldTensor_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.dualFieldTensor_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the Hodge dual of the pair with electric vector minus the original magnetic vector and magnetic vector the original electric vector negates the original field tensor.

**Theorem 1.3 (Electric and magnetic coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.fieldTensor_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.fieldTensor_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map from pairs of real three-vectors to antisymmetric real four-by-four matrices is bijective.

**Theorem 1.4 (Scalar and oriented contractions).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_invariants_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_invariants_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Half the contraction of the field tensor with its raised tensor is the magnetic squared length minus the electric squared length. One quarter of the contraction with the raised dual is the electric and magnetic dot product.

**Theorem 1.5 (Field determinant).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.fieldTensor_det`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.fieldTensor_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant of the covariant field tensor is the square of the electric and magnetic dot product.

**Theorem 1.6 (Lorentz invariance of both contractions).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_invariants_lorentz_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_invariants_lorentz_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a metric-preserving matrix with determinant one, the congruence by that matrix preserves both contractions after recovering the transformed electric and magnetic vectors. In coordinates it preserves the difference of squared lengths and the signed dot product.

**Theorem 1.7 (Symmetric covariant stress).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lowering the first index of the mixed Maxwell stress gives a symmetric matrix.

**Theorem 1.8 (Vanishing mixed trace).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_traceless`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_traceless` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mixed Maxwell stress has trace zero for every electromagnetic field.

**Theorem 1.9 (Energy, Poynting vector and spatial stress).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_energy_and_poynting`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_energy_and_poynting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mixed time-time entry is half the sum of the squared electric and magnetic lengths. Its time-space row is minus the Poynting vector, which is the cross product of the electric and magnetic vectors in that order. The fully raised time-space row is the Poynting vector, and the fully raised spatial block is the energy density times the identity minus the electric and magnetic outer products.

**Theorem 1.10 (Lorentz covariance of stress).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_lorentz_covariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_lorentz_covariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every metric-preserving matrix, the covariant stress of the transformed field is the congruence of the original covariant stress by that matrix.

**Theorem 1.11 (Invariance under duality rotation).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_duality_rotation_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_duality_rotation_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real angle, replace the electric vector by cosine times electric plus sine times magnetic, and the magnetic vector by minus sine times electric plus cosine times magnetic. Both the mixed and covariant stress remain invariant.

**Theorem 1.12 (Poynting bound and algebraically null fields).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.poynting_le_energy_density`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.poynting_le_energy_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The length of the Poynting vector is at most the energy density. Equality holds exactly when the electric and magnetic squared lengths agree and their dot product vanishes.

**Theorem 1.13 (Rainich square identity).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_rainich_square_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_rainich_square_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Y. Rainich (1925). *Electrodynamics in the General Relativity Theory*. DOI: [10.1090/S0002-9947-1925-1501302-6](https://doi.org/10.1090/S0002-9947-1925-1501302-6). URL: <https://doi.org/10.1090/S0002-9947-1925-1501302-6>.

*Commentary.*

The mixed stress squares to a scalar multiple of the identity. The scalar is the sum of one quarter of the squared difference of the magnetic and electric squared lengths and the squared electric and magnetic dot product.

**Theorem 1.14 (Vanishing stress square).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_nilpotent_iff_null`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_nilpotent_iff_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mixed stress squares to zero exactly when the electric and magnetic squared lengths agree and their dot product vanishes.

**Theorem 1.15 (Causal energy flux and nonnegative energy).**

Lean statement: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_dominant_energy_condition`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_dominant_energy_condition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any observer vector with nonnegative time coordinate and Minkowski squared norm, its quadratic pairing with the covariant stress is nonnegative. The flux obtained by applying the mixed stress has nonnegative time coordinate. Its Minkowski squared norm is the observer's Minkowski squared norm times the Rainich coefficient and is nonnegative.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.dualFieldTensor_sq`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.fieldTensor_antisym`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.fieldTensor_bijective`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.fieldTensor_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_dominant_energy_condition`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_duality_rotation_invariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_energy_and_poynting`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_invariants_explicit`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_invariants_lorentz_invariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_rainich_square_identity`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_lorentz_covariant`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_nilpotent_iff_null`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_symmetric`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.maxwell_stress_traceless`
- Truth anchor: `D5/S3/Geometry/Lorentz/MaxwellRainichStressEnergy4D.poynting_le_energy_density`
- Dependency: [D5/S3/Geometry/Lorentz/SL2CLorentzCover4D](SL2CLorentzCover4D.md)
