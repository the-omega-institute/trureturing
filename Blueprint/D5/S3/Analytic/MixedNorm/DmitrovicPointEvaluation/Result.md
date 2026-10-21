# Refutation of the mixed-norm point evaluation conjecture

## Abstract

The constant-one point evaluation estimate fails for every finite positive p, every larger q including infinity, and every positive alpha.

**Theorem 1.1 (Failure for all exponents above the contractive range).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.fails_off_contractive_range`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.fails_off_contractive_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. Dmitrović (2024). *Norm of composition operator on mixed norm spaces*. DOI: [10.7153/oam-2024-18-42](https://doi.org/10.7153/oam-2024-18-42). URL: <https://doi.org/10.7153/oam-2024-18-42>.

*Commentary.*

For every positive real p, every positive alpha, and every extended nonnegative q strictly larger than p, there is a function holomorphic on the open unit disc with finite mixed norm and an interior point where its norm is strictly smaller than the normalized evaluation. The normalization multiplies the modulus by (1 minus the squared modulus of the point) raised to alpha plus one over p. The finite-q case uses the strict radial gap with a equal to the square root of its positive parameter; the infinite-q case uses the unit weighted supremum and strict evaluation excess. Both constructions use principal-branch powers of 1 plus a times the variable.

**Theorem 1.2 (Dmitrovic's conjecture is false).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/dmitrovic-2024-mixed-norm-point-evaluation-refutation` (refuted) by `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dmitrovic-2024-mixed-norm-point-evaluation-refutation","declaration_gid":"D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Dmitrović (2024). *Norm of composition operator on mixed norm spaces*. DOI: [10.7153/oam-2024-18-42](https://doi.org/10.7153/oam-2024-18-42). URL: <https://doi.org/10.7153/oam-2024-18-42>.

*Commentary.*

The universal constant-one point evaluation claim is false. The general failure theorem at p equal to one, q equal to two, and alpha equal to one produces a holomorphic function of finite mixed norm and an interior point contradicting the claim. This refutes the conjecture on page 705 of Dmitrovic's Norm of composition operator on mixed norm spaces. It does not determine the optimal larger constant in the failing parameter range.

## References

- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.fails_off_contractive_range`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.result`
- Dependency: [D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean](CircleMean.md)
- Dependency: [D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/FirstOrderGap](FirstOrderGap.md)
