# EulerPentagonalTrisection

## Abstract

Complete pentagonal reindexing into the three weighted Jacobi sections.

The map from Fin 3 times the integers sends the three fibres to 3m, 1-3m, and 3m-1. Injectivity and surjectivity cover all integers; the three exponent equalities and parity signs are then proved exactly. The complete Euler HasSum is regrouped by this bijection. The resulting identity is consumed in EulerNineDissection. The underlying Euler pentagonal and Jacobi identities are classical and are supplied by Mathlib and the existing repository products.

**Theorem 1.1 (continuous_expand).**

Lean statement: `D5/S3/Arith/ModularForms/EulerPentagonalTrisection.continuous_expand`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/EulerPentagonalTrisection.continuous_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Positive integral expansion preserves coefficientwise limits and complete sums.

**Theorem 1.2 (pentagonal_sections).**

Lean statement: `D5/S3/Arith/ModularForms/EulerPentagonalTrisection.pentagonal_sections`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/EulerPentagonalTrisection.pentagonal_sections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The three complete integer fibres have degrees 3J4, 1+3J2, and 2+3J1.

**Theorem 1.3 (euler_three_sections).**

Lean statement: `D5/S3/Arith/ModularForms/EulerPentagonalTrisection.euler_three_sections`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/EulerPentagonalTrisection.euler_three_sections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The actual pentagonal Euler series equals J4(q^3)-qJ2(q^3)-q^2J1(q^3).

## References

- Truth anchor: `D5/S3/Arith/ModularForms/EulerPentagonalTrisection.continuous_expand`
- Truth anchor: `D5/S3/Arith/ModularForms/EulerPentagonalTrisection.euler_three_sections`
- Truth anchor: `D5/S3/Arith/ModularForms/EulerPentagonalTrisection.pentagonal_sections`
- Dependency: [D5/S3/Arith/ModularForms/WeightedJacobiSpecialization](WeightedJacobiSpecialization.md)
