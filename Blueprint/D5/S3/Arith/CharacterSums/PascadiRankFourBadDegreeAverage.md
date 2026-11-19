# The original rank-four bad-degree average

## Abstract

The rank-four factor gives the full average of the original maximum derivative-zero bad degrees.

**Theorem 1.1 (Average the original maximum bad degrees).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiRankFourBadDegreeAverage.actual_long_bad_degree_average_rank_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiRankFourBadDegreeAverage.actual_long_bad_degree_average_rank_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For each nonempty actual endpoint family, choose a baseline attaining the maximum derivative-zero bad degree. Require rank four over the rationals for its row together with every derivative-zero partner whose pencil has nonzero reduction modulo p. Empty endpoint families satisfy the stratum condition and have degree zero. The degree being averaged includes every derivative-zero partner, including those with zero reduction.

Let A=XY, C6=10319560704, and let C_rank=C6^2=106493333123540975616. For every epsilon>0 there is a positive constant C_epsilon uniform over prime p and the literal original data. Assume 1<=X<=Y, 2Y<p^3, A<2p^4, H>0, H^2=A and p<=H. The original middle and endpoint families satisfy the reduced basis, long chart, physical anchor, word, box and unit conditions. Under C_rank*(32*A/p^3)^13<p^10, the sum of the actual maximum degrees over the finite middle family is bounded by C_epsilon*p^epsilon*(A+(A/p)*(1+log(2p)/log(2))+A^2/p^4).

The reduced long basis supplies I>=J>=1 and IJ=32*A/p^3. The height gap implies the three rank-four bounds and the sixth-height bound using J^2<=IJ. The original word gives the common value modulo p^3, and the selected derivative-zero pencils give the common derivative modulo p. At the rational root of the common factor, division by the nonzero baseline linear value gives Q=chi L for every selected row. The Dixon matrix of any triple annihilates (1,theta,theta^2), so its determinant is zero. The same maximizing baseline therefore satisfies the existing zero Dixon condition, and its average supplies the bound over the original finite middle set.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiRankFourBadDegreeAverage.actual_long_bad_degree_average_rank_four`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiRankFourFactor](PascadiRankFourFactor.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiZeroDBadDegreeAverage](PascadiZeroDBadDegreeAverage.md)
