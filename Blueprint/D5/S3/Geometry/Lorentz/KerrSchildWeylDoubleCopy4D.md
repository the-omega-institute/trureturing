# Kerr–Schild metric algebra and the Coulomb Weyl square

## Abstract

Null Kerr–Schild updates preserve the metric determinant, and the signed Coulomb square gives the Schwarzschild Weyl quartic.

**Theorem 1.1 (The background metric squares to the identity).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.eta_square`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.eta_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal entries of the metric η are −1, 1, 1 and 1, so their squares are all one.

**Theorem 1.2 (Raising a covector).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.eta_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.eta_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying a column k by the metric negates its time coordinate and preserves its spatial coordinates.

**Theorem 1.3 (Raising a row covector).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.vec_eta`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.vec_eta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Right multiplication of k by the metric has the same coordinate effect as left multiplication.

**Theorem 1.4 (The raised contraction is the Minkowski square).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.sharp_dot`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.sharp_dot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the ordinary coordinate dot product of the raised covector with k gives −k₀²+k₁²+k₂²+k₃².

**Theorem 1.5 (Exact inverse of a null Kerr–Schild update).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.ks_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.ks_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In both multiplication orders, the cross terms of the metric and proposed inverse cancel. The quadratic term contains the contraction kᵀηk, which vanishes for a null covector. Both products are the identity for every real metric scalar.

**Theorem 1.6 (The determinant of the null update is minus one).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.ks_det`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.ks_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by η writes the updated metric as identity plus an outer product. The rank-one determinant lemma gives 1+φ kᵀηk, which is one. The determinant of η is minus one.

**Theorem 1.7 (The raw square in the negative scalar convention).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.coulomb_raw_square`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.coulomb_raw_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Benincasa and Freddy Cachazo (2007). *Consistency Conditions on the S-Matrix of Massless Particles*. DOI: [10.48550/arXiv.0705.4305](https://doi.org/10.48550/arXiv.0705.4305). URL: <https://arxiv.org/abs/0705.4305>.

*Commentary.*

For nonzero mass M, charge Q and radius r, form the trace-free outer square of the radial electric field (0,0,Q/r²). Dividing by S=−Q²/(3Mr) gives the diagonal entries M/r³, M/r³ and −2M/r³.

**Theorem 1.8 (The Coulomb square in the Schwarzschild tide convention).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.coulomb_to_schwarzschild_stf`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.coulomb_to_schwarzschild_stf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Benincasa and Freddy Cachazo (2007). *Consistency Conditions on the S-Matrix of Massless Particles*. DOI: [10.48550/arXiv.0705.4305](https://doi.org/10.48550/arXiv.0705.4305). URL: <https://arxiv.org/abs/0705.4305>.

*Commentary.*

With the curvature sign of the Schwarzschild electric tide used here, the map is the negative of the preceding scaled square. Its electric tensor is diagonal with entries −M/r³, −M/r³ and 2M/r³. The Weyl tensor is built by applying the inverse electric–magnetic equivalence to this tensor and zero magnetic part.

**Theorem 1.9 (The Schwarzschild Weyl quartic).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.schwarzschild_weylQuartic`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.schwarzschild_weylQuartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two transverse diagonal entries agree and the off-diagonal entries vanish. The Weyl-to-quartic coefficient map leaves only the coefficient of X², equal to 24M/r³.

**Theorem 1.10 (Schwarzschild screen tides).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.schwarzschild_tide_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.schwarzschild_tide_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex contraction on a finite ray z is (24M/r³)z². At infinity the contraction is the quartic coefficient of degree four and is zero. The finite contraction also vanishes at z=0.

**Theorem 1.11 (Two distinct projective double roots).**

Lean statement: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.schwarzschild_is_type_D`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.schwarzschild_is_type_D` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When M and r are nonzero, the homogeneous quartic is a nonzero scalar times z²w². The two linear factors have independent coefficient vectors, so their roots are distinct and each has multiplicity two. They are the finite origin and the point at infinity.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.coulomb_raw_square`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.coulomb_to_schwarzschild_stf`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.eta_sharp`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.eta_square`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.ks_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.ks_inverse`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.schwarzschild_is_type_D`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.schwarzschild_tide_eval`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.schwarzschild_weylQuartic`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.sharp_dot`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D.vec_eta`
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
