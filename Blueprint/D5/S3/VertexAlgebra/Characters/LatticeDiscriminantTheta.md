# Original lattice discriminant theta sectors

## Abstract

Original positive even integral lattices give finite discriminant theta sectors, exact inverse theta dissection, T multipliers and finite character resolution. The zero-sector S row uses the principal complex power. No lattice-sector VOA module or physical realization is asserted.

**Definition 1.1 (Original Gram cokernel).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.Discriminant`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.Discriminant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the original integral charge lattice M = Z^d, the discriminant carrier is the actual quotient M / range(G). No finite-group data are supplied.

**Definition 1.2 (Original dual quotient).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.dualQuotientEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.dualQuotientEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Inverse rational Gram coordinates identify M / G M with the quotient of the original dual lattice by the original integral lattice.

**Theorem 1.3 (Rational and real dual realization).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.dual_lattice_realization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.dual_lattice_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original LatticeData D with positive real Gram matrix, the rational dual agrees with the intrinsic integral-pairing dual, the discriminant cardinal is the absolute integral determinant, and every real vector pairing integrally with the original lattice is an inverse-Gram rational vector. Empty coordinates are included.

**Definition 1.4 (Faithful rational phase).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.phase`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.phase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational quotient Q / Z embeds in the real additive circle and then in the complex unit circle; its value on x is exp(2 pi i x).

**Definition 1.5 (Original quotient pairing).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.pairing`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.pairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pairing of the classes of r and s is the class of (G_Q inverse r) dot s in Q / Z. Rational inversion takes place after extending scalars.

**Definition 1.6 (Original even half norm).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.quadraticClass`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.quadraticClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quadratic value of the class of r is the class of r dot G_Q inverse r divided by two. Original lattice evenness makes this independent of representatives.

**Theorem 1.7 (Nondegenerate quadratic refinement).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.discriminant_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.discriminant_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original positive even integral Gram matrix, q(a+c) = q(a)+q(c)+b(a,c), q(k a) = k squared q(a) for every integer k, the pairing has zero radical, and the complex phase is injective on Q / Z.

**Definition 1.8 (Literal shifted Gaussian).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.representativeTheta`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.representativeTheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any integer representative r, sum exp(pi i tau Q_G(n+G_Q inverse r)) over every original integral vector n. The rational shift is embedded in the original real coordinates.

**Definition 1.9 (Discriminant theta sector).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sectorTheta`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sectorTheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sector of an actual quotient class uses a chosen representative in the literal shifted Gaussian. No additive section is asserted.

**Theorem 1.10 (Absolute convergence and representative independence).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sector_summable_representative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sector_summable_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original positive even integral lattice, every actual class a, every integer representative r of a and every tau in the upper half-plane, the literal shifted Gaussian has summable norms and equals the sector theta function.

**Theorem 1.11 (Exact inverse theta dissection).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverse_theta_dissection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverse_theta_dissection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural rank, original positive Gram matrix and upper half-plane tau, theta of the real inverse Gram matrix is the finite sum of all original quotient-sector theta functions. The actual charge bijection is (a,n) mapped to rep(a)+G n; absolute convergence precedes product reindexing.

**Theorem 1.12 (Original zero-sector S row).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.zero_sector_S`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.zero_sector_S` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original positive even integral lattice and upper half-plane tau, Theta_0(-1/tau) is (-i tau) to the principal power d/2 divided by the positive real square root of det G, times the sum of all discriminant sectors at tau. This follows from exact inverse theta dissection and matrix Gaussian inversion.

**Theorem 1.13 (Original class T law).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sector_T`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sector_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original positive even integral lattice, every discriminant class and upper half-plane tau, Theta_a(tau+1) = exp(2 pi i q(a)) Theta_a(tau). The original even charge energy removes the integral Gaussian phase.

**Definition 1.14 (Perfect original pairing).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.characterEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.characterEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nondegenerate inverse-Gram pairing and the faithful rational phase identify the actual finite discriminant carrier with its full complex character group.

**Definition 1.15 (Actual character-weighted inverse coefficients).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverseCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverseCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each discriminant class a, sum the original inverse-form integer Gaussian weighted by exp(-2 pi i b(a,[k])). The negative sign is part of this coefficient definition.

**Theorem 1.16 (Finite resolution and reconstruction).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverse_theta_fourier`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverse_theta_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original positive even lattice and upper half-plane tau, all character-weighted inverse coefficients converge absolutely. Each is the finite sum of Theta_c weighted by exp(-2 pi i b(a,c)); conversely the sum of a coefficient weighted by exp(2 pi i b(a,c)) over all a equals natAbs(det G) times Theta_c. Orthogonality is proved for this actual quotient pairing.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.Discriminant`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.characterEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.discriminant_quadratic`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.dualQuotientEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.dual_lattice_realization`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverseCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverse_theta_dissection`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverse_theta_fourier`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.pairing`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.phase`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.quadraticClass`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.representativeTheta`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sectorTheta`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sector_T`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sector_summable_representative`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.zero_sector_S`
- Dependency: [D5/S3/Fourier/MatrixGaussianTheta](../../Fourier/MatrixGaussianTheta.md)
- Dependency: [D5/S3/VertexAlgebra/LatticePositiveEnergy](../LatticePositiveEnergy.md)
