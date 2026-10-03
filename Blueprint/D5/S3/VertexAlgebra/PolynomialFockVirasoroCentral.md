# Polynomial Fock Virasoro Central Relation

## Abstract

The actual complex polynomial Fock Sugawara operators satisfy the central charge one relation.

The operators are the pointwise finite normal-ordered sums on complex polynomials in countably many variables. The proof is a source transplant of Kytola's bosonic Sugawara proof, specialized to these operators using their support bounds and Heisenberg-current relations.

**Theorem 1.1 (Every pair of integer Sugawara modes has the central commutator).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockVirasoroCentral.L_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockVirasoroCentral.L_commutator` (`✓ std3`). ∎

*Citation.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

For all integers m and n, L m times L n minus the reverse product equals (m-n) times L (m+n), plus (m cubed minus m)/12 times the identity when m+n=0. The central coefficient comes from the two finite integer sign intervals of the normal-ordering boundary. This is a rank-one c=1 operator relation, not a construction of a VOA, Monster modules, c=24, fusion, conformal weights or OPE coefficients.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockVirasoroCentral.L_commutator`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators](PolynomialFockSugawaraCommutators.md)
