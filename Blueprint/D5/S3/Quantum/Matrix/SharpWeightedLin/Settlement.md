# Sharp weighted Lin comparison

## Abstract

Sharp weighted Lin comparison

**Definition 1.1 (Weighted arithmetic power mean).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.hiaiArithmeticMean`

*Formalization.* `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.hiaiArithmeticMean` (`✓ std3`).

*Citation.* Fumio Hiai (2025). *Various inequalities between quasi-arithmetic mean and quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2508.20309>.

*Commentary.*

For positive parameters and positive definite inputs, this is the spectral one over q power of the weighted sum of the q powers of A and B, as in Hiai Section 2.1.

**Definition 1.2 (Weighted sandwich power mean).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.hiaiRMean`

*Formalization.* `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.hiaiRMean` (`✓ std3`).

*Citation.* Fumio Hiai (2025). *Various inequalities between quasi-arithmetic mean and quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2508.20309>.

*Commentary.*

This is the spectral one over p power of A to the power (one minus alpha) p over two, times B to the power alpha p, times the same A power. It is Hiai quasi-Renyi mean from Section 2.1, used in Section 4.3.

**Theorem 1.3 (Sharp weighted spectral comparison).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.result` (`✓ std3`). ∎

*Resolves.* `Problems/hiai-2025-problem-4-15-sharp-weighted-lin` (proved) by `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hiai-2025-problem-4-15-sharp-weighted-lin","declaration_gid":"D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Various inequalities between quasi-arithmetic mean and quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2508.20309>.

*Acknowledgement.* Suvrit Sra (2026). *On Lin's Arithmetic–Geometric Means Conjecture for Singular Values*. URL: <https://suvrit.github.io/papers/linconj/linconj-v1.pdf>.

*Commentary.*

For every dimension, weight strictly between zero and one, positive p, and q at least alpha times one minus alpha times p, every descending eigenvalue of the sandwich power mean is at most the corresponding eigenvalue of the arithmetic power mean on positive definite complex inputs. Sra inertia method is reused: inverse congruence gives a rank reduction, Schur inertia turns the spectral threshold into a nonpositive compressed quadratic form, and finite spectral measures reduce that form to the sharp scalar barrier x to the power a over b times (one minus a x) at most b. Equality holds at x equal to one. With a plus b equal to one, this gives the singular value endpoint exponent two a b; homogeneity and monotonicity of arithmetic power means give the stated range. At equal weights the endpoint is Sra and Drury exponent one half. Hiai Problem 4.15 and its necessary parameter bound are the source question; the endpoint sufficiency is the repository conclusion. Weak majorization and trace consequences by summation, source necessity, the remaining source trace region q at least one, and extension to semidefinite inputs by continuity are described separately in the problem dossier; they are not additional Lean conclusions here.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.hiaiArithmeticMean`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.hiaiRMean`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.result`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound](../LinGProperty/ArithmeticBound.md)
- Dependency: [D5/S3/Quantum/Matrix/SharpWeightedLin/Generality](Generality.md)
- Dependency: [D5/S3/Quantum/Schatten/Partition](../../Schatten/Partition.md)
- Dependency: [D5/S3/Quantum/Schatten/SingularValueOrder](../../Schatten/SingularValueOrder.md)
- Dependency: [D5/S3/Weil/Pick/DiagonalSignNegativeIndex](../../../Weil/Pick/DiagonalSignNegativeIndex.md)
