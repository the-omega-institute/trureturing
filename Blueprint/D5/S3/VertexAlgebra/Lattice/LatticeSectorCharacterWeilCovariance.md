# Actual lattice-sector character S transformation

## Abstract

Actual dual-coset graded traces and Weil S covariance

For any original positive definite even integral Gram matrix, every discriminant class a uses its existing representative beta and the rational dual vector G-inverse beta. The sector is the existing auxiliary-lattice module action. Its grade at rational energy e is the literal eigenspace of the original-omega operator moduleL(D,beta,H,0), for every complex inverse H satisfying both inverse identities. The normalized character sums the identity traces on these finite grades with exp(2 pi i tau (e-rank/24)). It is not defined as a theta/eta quotient.

The existing coefficient equivalence identifies the full actual grade with its finite charge/occupation fiber. The trace equals the fiber cardinality. Absolute convergence of the Gaussian and ordinary integer-frequency occupations permits regrouping by every rational energy and factoring the resulting basis sum. The occupation product evaluates to the inverse rank-th power of eta after the vacuum shift, giving the character formula Theta_a/eta^rank. Empty grades and rank zero remain included.

The existing principal-branch theta and eta S laws cancel the common weight factor. The remaining operator is exactly weilS: the kernel is pairingCharacter(a,-b), with normalization rho(D) inverse, where rho is the positive square root of the original discriminant cardinality. No unimodularity, even-rank assumption, choice of minimum, or identification of distinct sector labels is imposed. The result concerns these actual lattice modules; Monster identification, orbifold sewing and a complete CFT construction are separate obligations.

**Definition 1.1 (Actual rational-energy grades).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorGrade`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorGrade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D, complex matrix H, discriminant class a and rational energy e, sectorGrade is the eigenspace of moduleL(D,representative(D,a),H,0) with eigenvalue the complex cast of e. It uses the original conformal zero mode on the existing actual dual-coset carrier.

**Definition 1.2 (Finite-grade identity trace terms).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorTraceTerm`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorTraceTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive real Gram matrix, every complex inverse H satisfying both inverse identities, every a, complex tau and rational e, sectorTraceTerm is the trace of the identity on sectorGrade multiplied by exp(2 pi i tau (e-rank/24)). The existing finite-dimensionality theorem supplies the finite actual grade; no trace is taken on the infinite ambient carrier.

**Definition 1.3 (Normalized actual sector character).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorCharacter`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the same positivity and inverse hypotheses, sectorCharacter is the complex tsum of sectorTraceTerm over every rational energy. It is defined for every complex tau; absolute convergence and the transformation law are asserted on the upper half-plane.

**Theorem 1.4 (Absolute convergence and the normalized sector S law).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.lattice_sector_character_s_transform`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.lattice_sector_character_s_transform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every discriminant class a and every tau in the upper half-plane, the actual rational-grade trace series is absolutely summable, and its value at -1/tau is the a coordinate of the existing Weil S operator applied to the entire vector of actual sector characters at tau. The proof derives the theta/eta formula from finite actual eigenspace traces before invoking the analytic transformation laws.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.lattice_sector_character_s_transform`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorCharacter`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorGrade`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorTraceTerm`
- Dependency: [D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation](../../Combinatorics/Partitions/AnalyticIntegerOccupation.md)
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil](../Characters/LatticeDiscriminantWeil.md)
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeThetaCharacter](../Characters/LatticeThetaCharacter.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy](../Sectors/LatticeDualCosetPositiveEnergy.md)
