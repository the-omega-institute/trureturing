# Polynomial Fock Mode Commutators

## Abstract

The concrete polynomial Fock modes satisfy the Heisenberg and Sugawara-current relations.

The modes and pointwise finite Sugawara operators are those of Polynomial Fock Sugawara Support. The generic Sugawara proof of Kytola supplies a reference for the commutator calculation; the concrete Heisenberg premise is established here from polynomial differentiation.

**Theorem 1.1 (Every pair of integer modes has the Heisenberg commutator).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators.mode_heisenberg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators.mode_heisenberg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

For all integer m and n, mode m times mode n minus the reverse product is m times the identity when m+n=0, and zero otherwise. The mixed sign case differentiates a variable multiplier; the two same sign cases commute.

**Theorem 1.2 (The Sugawara operator acts on every mode with weight one).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators.L_mode_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators.L_mode_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kalle Kytölä (2025). *VirasoroProject, Sugawara.lean*. URL: <https://github.com/kkytola/VirasoroProject/blob/5ff4245383b2cdd4eea7a0524bc1274c32041eb4/VirasoroProject/Sugawara.lean>.

*Commentary.*

For all integer m and r, L m times mode r minus the reverse product is minus r times mode (m+r). Commuting through the pointwise finite sum leaves two singleton contributions. This result does not assert the L-L commutator or its central term.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators.L_mode_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators.mode_heisenberg`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport](PolynomialFockSugawaraSupport.md)
