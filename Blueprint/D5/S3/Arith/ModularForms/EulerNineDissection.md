# EulerNineDissection

## Abstract

The actual Euler quotient has three genuine restricted partition sections.

The Jacobi products are identified with E times Q_r by multiplying the actual restricted-partition HasProd by the Euler HasProd. Allowed geometric factors cancel exactly; each finite block of nine leaves precisely the three forbidden factors. The finite-block identity is proved for arbitrary cutoff and then passed to its true coefficientwise limit. The constant-one Euler inverse gives J_r P=Q_r. Thus R=E(q)/E(q^3) has the required signed dissection; it is not an assumed partition identity. EulerNineSquareDissection consumes R_dissection.

**Theorem 1.1 (J_eq_euler_mul_Q).**

Lean statement: `D5/S3/Arith/ModularForms/EulerNineDissection.J_eq_euler_mul_Q`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/EulerNineDissection.J_eq_euler_mul_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

For r=1,2,4, the weighted Jacobi series is E times the actual allowed-part counting series.

**Theorem 1.2 (J_mul_inverse).**

Lean statement: `D5/S3/Arith/ModularForms/EulerNineDissection.J_mul_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/EulerNineDissection.J_mul_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Multiplying by the genuine Euler inverse yields the restricted partition section.

**Definition 1.3 (R).**

Lean statement: `D5/S3/Arith/ModularForms/EulerNineDissection.R`

*Formalization.* `D5/S3/Arith/ModularForms/EulerNineDissection.R` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The actual Euler quotient E(q) times P(q^3).

**Theorem 1.4 (R_dissection).**

Lean statement: `D5/S3/Arith/ModularForms/EulerNineDissection.R_dissection`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/EulerNineDissection.R_dissection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The all-degree equality R=Q4(q^3)-qQ2(q^3)-q^2Q1(q^3).

## References

- Truth anchor: `D5/S3/Arith/ModularForms/EulerNineDissection.J_eq_euler_mul_Q`
- Truth anchor: `D5/S3/Arith/ModularForms/EulerNineDissection.J_mul_inverse`
- Truth anchor: `D5/S3/Arith/ModularForms/EulerNineDissection.R`
- Truth anchor: `D5/S3/Arith/ModularForms/EulerNineDissection.R_dissection`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaIdentities](CubicThetaIdentities.md)
- Dependency: [D5/S3/Arith/ModularForms/EulerPentagonalTrisection](EulerPentagonalTrisection.md)
- Dependency: [D5/S3/Combinatorics/Partitions/EulerNineComparison](../../Combinatorics/Partitions/EulerNineComparison.md)
