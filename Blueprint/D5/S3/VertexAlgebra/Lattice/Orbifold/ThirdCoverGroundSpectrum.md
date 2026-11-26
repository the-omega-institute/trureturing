# The Fractional Zero-Mode Spectrum

## Abstract

The complementary zero mode has point spectrum 1/9+n/3 for natural n and a one-dimensional ground eigenspace of weight 1/9.

Use the actual fractionalVirasoro(0) on ComplementFock. The ordinary vacuum slice Q maps to join(1 tensor Q), which is the polynomial renaming into the native Fock space. The split operator identity and the native PolynomialFockLZeroSpectrum.lZero_spectrum give the zero-mode action on this slice. The proof below uses these repository results and coefficient uniqueness, with the merged cover shift fixed at 1/9.

**Definition 1.1 (Native occupation weight).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.occupationEnergy`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.occupationEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finitely supported occupation vector d on the complementary variable type, sum (k.val+1) d(k) over its support. Divide this natural number by three to obtain the excitation contribution to the complementary weight.

**Theorem 1.2 (Zero occupation energy detects the vacuum occupation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.occupationEnergy_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.occupationEnergy_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identify occupationEnergy with the Finsupp weight for the positive natural weights k.val+1. Finsupp.weight_eq_zero_iff_eq_zero then gives exactly the zero occupation.

**Theorem 1.3 (Diagonal action on every monomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every occupation d and complex coefficient a, fractionalVirasoro(0)(monomial(d,a)) equals (1/9+occupationEnergy(d)/3) times that monomial. The ordinary factor has zero native energy on 1. The variable renaming is injective, and summing native energy after the exponent pushforward gives exactly occupationEnergy(d).

**Theorem 1.4 (Diagonal action on arbitrary polynomial coefficients).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient at d of the image of any polynomial Q equals (1/9+occupationEnergy(d)/3) times the coefficient at d of Q. Expand Q into its finite monomial support and use the diagonal formula.

**Theorem 1.5 (The ground eigenspace is the vacuum line).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_ground_eigenspace`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_ground_eigenspace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel of fractionalVirasoro(0) minus 1/9 times the identity is exactly the complex span of the constant polynomial 1. A nonzero coefficient of any vector in this kernel must have energy zero, so its support lies in the zero occupation. ThirdCoverComplement.fractionalVirasoro_vacuum supplies the reverse inclusion.

**Theorem 1.6 (Exact point spectrum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_eigenvalue`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_eigenvalue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a nonzero Q with fractionalVirasoro(0)(Q)=a Q exactly when a=1/9+n/3 for some natural n. A nonzero coefficient forces the stated form. Conversely the coefficient-one monomial with exponent n at complementary label 0 has occupation energy n and realizes that eigenvalue.

**Theorem 1.7 (Lower bound on eigenvalues).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_eigenvalue_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_eigenvalue_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero-state complex eigenvalue has real part at least 1/9 because its excitation shift is a natural number divided by three.

**Theorem 1.8 (The vacuum attains the minimum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Among real numbers x admitting a nonzero polynomial Q with fractionalVirasoro(0)(Q)=x Q, 1/9 is least. The constant polynomial is a nonzero witness to attainment, and the real-part lower bound applies to every such x.

These statements establish all monomial weights, the exact shifted nonnegative point spectrum, and the exact lowest eigenspace of the one-pair polynomial complementary factor. The full lattice twisted-module spectrum requires further constructions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_eigenvalue`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_eigenvalue_lower_bound`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_ground_eigenspace`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_minimum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.fractionalVirasoro_zero_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.occupationEnergy`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.occupationEnergy_eq_zero_iff`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement](ThirdCoverComplement.md)
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum](../../PolynomialFockLZeroSpectrum.md)
