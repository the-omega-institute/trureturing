# The coordinate kernel of a nonzero Dixon triple

## Abstract

The surviving term of the Dixon determinant modulo the sixth prime power supplies a unit three-column minor and controls both discriminant strata.

**Definition 1.1 (Primitive coordinate kernel).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiRankThreeLocal.RankThreeKernel`

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiRankThreeLocal.RankThreeKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The original three quadratic cofactors are one common multiple of a primitive polynomial. The leading cofactor is a unit modulo p. The integer discriminant factor, its real height, the two strata, and the ramified derivative gap are kept in the same statement.

**Theorem 1.2 (Saturation and the two discriminant strata).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiRankThreeLocal.nonzero_dixon_rank_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiRankThreeLocal.nonzero_dixon_rank_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The constant and linear columns after translation and common-parameter subtraction are divisible by the third and first powers of p. In the original Dixon determinant only one term of degree five survives modulo the sixth power. Its factors give the unit minor and exclude the simultaneous fourth-power value and second-power derivative divisibilities. The original coordinate heights give the bound 23328 (I J)^4 / p^2 for the discriminant factor.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiRankThreeLocal.RankThreeKernel`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiRankThreeLocal.nonzero_dixon_rank_three`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiPrimeCubeSingularCover](PascadiPrimeCubeSingularCover.md)
