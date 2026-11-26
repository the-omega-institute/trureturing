# An optimal rank-nine Ferrers code

## Abstract

An optimal dimension-27 rank-nine code for the fixed twelve-column Ferrers diagram.

**Definition 1.1 (Column heights).**

$$\forall j \in \operatorname{Fin}\left(12\right),\; ((\operatorname{val}\left(j\right) < 3) \Rightarrow ((\operatorname{height}\left(j\right) : \mathbb{N}) = 6)) \land ((((3 \le \operatorname{val}\left(j\right)) \land (\operatorname{val}\left(j\right) < 6)) \Rightarrow ((\operatorname{height}\left(j\right) : \mathbb{N}) = 9)) \land ((6 \le \operatorname{val}\left(j\right)) \Rightarrow ((\operatorname{height}\left(j\right) : \mathbb{N}) = 12)))$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.height` (`✓ std3`).

*Citation.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

Notation 2.10 (p. 6) and Example 3.5 (p. 11) specify the block size three and the height profile. The same diagram is named in Section 4, Problem 1, p. 18. https://arxiv.org/pdf/2611.19070v1

**Definition 1.2 (Ferrers support).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] \forall C \in \operatorname{Submodule}\left(F, \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right)\right),\; \operatorname{Supported}\left(C\right) \Leftrightarrow (\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \Rightarrow (\forall i \in \operatorname{Fin}\left(12\right),\; \forall j \in \operatorname{Fin}\left(12\right),\; (\operatorname{height}\left(j\right) \le \operatorname{val}\left(i\right)) \Rightarrow (M(i,j) = 0)))$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Supported` (`✓ std3`).

*Citation.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

Definition 2.1 (p. 3) defines the diagram’s support as its dot positions. The matrix-shape definition (p. 4) requires zeros outside those positions. Example 3.5 (p. 11) shows the fixed diagram with top-aligned columns. Row indices here start at zero. https://arxiv.org/pdf/2611.19070v1

**Definition 1.3 (The example's claim).**

$$Problem1RankNine \Leftrightarrow (\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)], (\operatorname{Odd}\left(\operatorname{card}\left(F\right)\right)) \Rightarrow ((3 < \operatorname{card}\left(F\right)) \Rightarrow ((\exists C \in \operatorname{Submodule}\left(F, \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right)\right),\; (\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \Rightarrow (\forall i \in \operatorname{Fin}\left(12\right),\; \forall j \in \operatorname{Fin}\left(12\right),\; (\operatorname{height}\left(j\right) \le \operatorname{val}\left(i\right)) \Rightarrow (M(i,j) = 0))) \land ((\operatorname{finrank}\left(F, C\right) = 27) \land ((\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \Rightarrow ((M \ne 0) \Rightarrow (9 \le \operatorname{rank}\left(M\right)))) \land (\exists M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \land ((M \ne 0) \land (\operatorname{rank}\left(M\right) = 9)))))) \land (\forall D \in \operatorname{Submodule}\left(F, \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right)\right),\; (\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in D) \Rightarrow (\forall i \in \operatorname{Fin}\left(12\right),\; \forall j \in \operatorname{Fin}\left(12\right),\; (\operatorname{height}\left(j\right) \le \operatorname{val}\left(i\right)) \Rightarrow (M(i,j) = 0))) \Rightarrow ((\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in D) \Rightarrow ((M \ne 0) \Rightarrow (9 \le \operatorname{rank}\left(M\right)))) \Rightarrow (\operatorname{finrank}\left(F, D\right) \le 27))))))$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Problem1RankNine` (`✓ std3`).

*Citation.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

Section 4, Problem 1, p. 18, arXiv v1. https://arxiv.org/pdf/2611.19070v1#page=18

“For example, does there exist an optimal Ferrers diagram rank-metric code for $\mathcal{D} = [[2,3,4,4]]_{3}$ and $d = 9$ when $q > 3$ is an odd prime power?”

**Definition 1.4 (Dimension and minimum rank condition).**

$$SupportedDimension27WithRankLowerBound \Leftrightarrow (\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)], (\operatorname{Odd}\left(\operatorname{card}\left(F\right)\right)) \Rightarrow ((3 < \operatorname{card}\left(F\right)) \Rightarrow (\exists C \in \operatorname{Submodule}\left(F, \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right)\right),\; (\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \Rightarrow (\forall i \in \operatorname{Fin}\left(12\right),\; \forall j \in \operatorname{Fin}\left(12\right),\; (\operatorname{height}\left(j\right) \le \operatorname{val}\left(i\right)) \Rightarrow (M(i,j) = 0))) \land ((\operatorname{finrank}\left(F, C\right) = 27) \land (\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \Rightarrow ((M \ne 0) \Rightarrow (9 \le \operatorname{rank}\left(M\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.SupportedDimension27WithRankLowerBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

This condition supplies the code used in the projection argument.

**Theorem 1.5 (The two column projections).**

$$Problem1RankNine \Leftrightarrow (SupportedDimension27WithRankLowerBound)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1RankNine_iff_exists_supported_dim27` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

The first four columns have 27 allowed entries. A matrix in their projection kernel has rank at most eight, so projection onto those entries bounds any competing code’s dimension by 27. On a dimension-27 code with nonzero ranks at least nine, the first three columns give a projection onto 18 allowed entries. Each nonzero matrix in its nonzero kernel has rank exactly nine.

**Theorem 1.6 (The rank-nine example in Problem 1).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)], (\operatorname{Odd}\left(\operatorname{card}\left(F\right)\right)) \Rightarrow ((3 < \operatorname{card}\left(F\right)) \Rightarrow ((\exists C \in \operatorname{Submodule}\left(F, \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right)\right),\; (\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \Rightarrow (\forall i \in \operatorname{Fin}\left(12\right),\; \forall j \in \operatorname{Fin}\left(12\right),\; (\operatorname{height}\left(j\right) \le \operatorname{val}\left(i\right)) \Rightarrow (M(i,j) = 0))) \land ((\operatorname{finrank}\left(F, C\right) = 27) \land ((\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \Rightarrow ((M \ne 0) \Rightarrow (9 \le \operatorname{rank}\left(M\right)))) \land (\exists M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \land ((M \ne 0) \land (\operatorname{rank}\left(M\right) = 9)))))) \land (\forall D \in \operatorname{Submodule}\left(F, \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right)\right),\; (\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in D) \Rightarrow (\forall i \in \operatorname{Fin}\left(12\right),\; \forall j \in \operatorname{Fin}\left(12\right),\; (\operatorname{height}\left(j\right) \le \operatorname{val}\left(i\right)) \Rightarrow (M(i,j) = 0))) \Rightarrow ((\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in D) \Rightarrow ((M \ne 0) \Rightarrow (9 \le \operatorname{rank}\left(M\right)))) \Rightarrow (\operatorname{finrank}\left(F, D\right) \le 27)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1_rank_nine` (`✓ std3`). ∎

*Resolves.* `Problems/jin-ning-xu-duan-2026-ferrers-rank-nine-example` (proved) by `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1_rank_nine`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jin-ning-xu-duan-2026-ferrers-rank-nine-example","declaration_gid":"D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1_rank_nine","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

Inside a degree-twelve extension E of the finite base field F, take nested subfields K and L of degrees three and six over F. Use the same ordered tower basis for the input and output. Evaluation on K lands in L, and evaluation on bK lands in L plus the K-line generated by the third vector of the upper basis. These exhaust the support constraints on the first two blocks of three columns.

The coefficient tuple determines the parameters in L⁴ × K. A nonzero tuple gives a nonzero polynomial of degree at most q³, so its evaluation kernel has dimension at most three and its matrix has rank at least nine. Together these facts give an injective map from the parameter space to the matrix space and a code of dimension 27.

The projection onto the first three columns yields a nonzero rank-nine matrix. The projection onto the first four columns gives the dimension bound for competing codes. This is the fixed example from Section 4, Problem 1.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Problem1RankNine`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Supported`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.SupportedDimension27WithRankLowerBound`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.height`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1RankNine_iff_exists_supported_dim27`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1_rank_nine`
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients](FerrersCoefficients.md)
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction](MRDDensityColumnReduction.md)
