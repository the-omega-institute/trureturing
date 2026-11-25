# Third-Cover Virasoro Modes and Fractional Currents

## Abstract

The order-three covering operators and fractional current brackets on the full rank-one polynomial Fock space.

All products are compositions of complex-linear endomorphisms of the full rank-one Fock space, the algebra of polynomials in countably many variables. The integer current and pointwise finite normal-ordered Sugawara operator are mode and L from PolynomialFockSugawaraSupport. There is no bound on the polynomial degree or its variable indices.

**Definition 1.1 (Covering Virasoro mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

For each integer m, the covering mode L3(m) is L(3m)/3 plus the identity divided by nine when m=0.

**Definition 1.2 (Current at frequency r/3).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.current`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.current` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For any complex scale a and integer r, J_a(r) is a times mode(r). Its frequency is r/3. The two nonintegral grids are Z+1/3 and Z+2/3.

**Theorem 1.3 (Virasoro commutator at central charge three).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

For all integers n and m, [L3(n), L3(m)] is (n-m)L3(n+m) plus 3(n^3-n)/12 times the identity when n+m=0. The scalar shifts commute. Using PolynomialFockVirasoroCentral.L_commutator at 3n and 3m gives the central polynomial ((3n)^3-3n)/108. When m=-n, the contribution (n-m)/9 from the shifted output mode leaves 3(n^3-n)/12.

**Theorem 1.4 (Normalized current bracket and complementary grid support).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.current_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.current_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every complex a with a^2=1/3 and all integers r and s, [J_a(r), J_a(s)] equals (r/3) times the identity when r+s=0 and is zero otherwise. If r has nonzero residue modulo three, the bracket is nonzero exactly when r+s=0 and the nonnegative residues of r and s sum to three. The factor a^2 rescales PolynomialFockSugawaraCommutators.mode_heisenberg, and the coefficient r/3 is nonzero for a fractional frequency. This is the opposite-frequency pairing of Bakalov and Kac, arXiv:math/0402315v1, equation (4.23), with the paired form entry normalized to one.

**Theorem 1.5 (Covering modes preserve each current grid).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode_current_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode_current_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every complex a and all integers m and r, [L3(m), J_a(r)] equals -(r/3) J_a(3m+r), and 3m+r and r have the same residue modulo three. The operator identity uses PolynomialFockSugawaraCommutators.L_mode_commutator and the scalar zero-mode shift commutes with every current. If a^2=1/3 and r has nonzero residue, the mixed bracket is nonzero. The shifted current has a nonzero bracket with its opposite-frequency current, so the shifted current itself is nonzero.

**Theorem 1.6 (The first covering vacuum descendant).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode_first_vacuum_descendant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode_first_vacuum_descendant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

On the constant vacuum 1, L3(1)L3(-1) returns (2/9) times 1. PolynomialFockLZeroSpectrum.lZero_spectrum puts the constant monomial in the native L(0) zero eigenspace. The support bound for L(3) on 1 is the open integer interval (1,2), so L3(1) kills 1. The covering commutator at 1 and -1 then reduces the composition to twice the shifted L3(0) on 1.

The oscillator pairing is relevant to the sixteen complementary eigenspace pairs in the P48q order-three anomaly calculation for the central-charge-48 extremal VOA problem. The covering calculation here includes the integral grid alongside both fractional grids. The separation of its full Virasoro action into the integral-grid and complementary-grid actions is a separate factorization problem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode_current_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.coverMode_first_vacuum_descendant`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.current`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.current_commutator`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum](../../PolynomialFockLZeroSpectrum.md)
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockVirasoroCentral](../../PolynomialFockVirasoroCentral.md)
