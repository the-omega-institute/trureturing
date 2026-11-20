# An optimal rank-nine Ferrers code

## Abstract

An optimal dimension-27 rank-nine code for the fixed twelve-column Ferrers diagram.

**Definition 1.1 (Ambient matrices).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Mat`

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Mat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

Rows and columns of the matrices over F are both indexed by Fin 12.

**Definition 1.2 (Column heights).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.height`

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.height` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

A zero-based column j has height 6 for j < 3, height 9 for 3 ≤ j < 6, and height 12 for 6 ≤ j.

**Definition 1.3 (Ferrers support).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Supported`

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Supported` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

Every matrix in the code vanishes in each column at row indices at least that column's height.

**Definition 1.4 (The example's claim).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Problem1RankNine`

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Problem1RankNine` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

For each finite field of odd order greater than three, the fixed diagram admits a supported code of dimension 27 with nonzero ranks at least nine and a nonzero matrix of rank nine. The same dimension is an upper bound for all supported codes with nonzero ranks at least nine.

**Definition 1.5 (Dimension and minimum rank condition).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.SupportedDimension27WithRankLowerBound`

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.SupportedDimension27WithRankLowerBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

Every finite field of odd order greater than three admits a supported code of dimension 27 whose nonzero matrices have rank at least nine.

**Theorem 1.6 (The two column projections).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1RankNine_iff_exists_supported_dim27`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1RankNine_iff_exists_supported_dim27` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

The claim is equivalent to the dimension and minimum rank condition. The first four columns have 27 allowed entries. A matrix in their projection kernel has rank at most eight, so projection onto those entries bounds the dimension of any competing code by 27. The first three columns have 18 allowed entries, so their projection has a nonzero kernel on a dimension-27 code. Each nonzero matrix in that kernel has rank exactly nine.

**Theorem 1.7 (The rank-nine example in Problem 1).**

$$\forall F \in Type,\; [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)], (\operatorname{Odd}\left(\operatorname{card}\left(F\right)\right)) \Rightarrow ((3 < \operatorname{card}\left(F\right)) \Rightarrow ((\exists C \in \operatorname{Submodule}\left(F, \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right)\right),\; (\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \Rightarrow (\forall i \in \operatorname{Fin}\left(12\right),\; \forall j \in \operatorname{Fin}\left(12\right),\; (\operatorname{height}\left(j\right) \le \operatorname{val}\left(i\right)) \Rightarrow (M(i,j) = 0))) \land ((\operatorname{finrank}\left(F, C\right) = 27) \land ((\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \Rightarrow ((M \ne 0) \Rightarrow (9 \le \operatorname{rank}\left(M\right)))) \land (\exists M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in C) \land ((M \ne 0) \land (\operatorname{rank}\left(M\right) = 9)))))) \land (\forall D \in \operatorname{Submodule}\left(F, \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right)\right),\; (\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in D) \Rightarrow (\forall i \in \operatorname{Fin}\left(12\right),\; \forall j \in \operatorname{Fin}\left(12\right),\; (\operatorname{height}\left(j\right) \le \operatorname{val}\left(i\right)) \Rightarrow (M(i,j) = 0))) \Rightarrow ((\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), F\right),\; (M \in D) \Rightarrow ((M \ne 0) \Rightarrow (9 \le \operatorname{rank}\left(M\right)))) \Rightarrow (\operatorname{finrank}\left(F, D\right) \le 27)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1_rank_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yong Jin, Yuhao Ning, Dengming Xu and Chengming Duan (2026). *New constructions of optimal Ferrers diagram rank-metric codes for quasi-block monotone Ferrers diagrams*. URL: <https://arxiv.org/abs/2611.19070v1>.

*Commentary.*

Inside a degree-twelve extension E of the finite base field F, take nested subfields K and L of degrees three and six over F. Use the same ordered tower basis for the input and output. Evaluation on K lands in L, and evaluation on bK lands in L plus the K-line generated by the third vector of the upper basis. These exhaust the support constraints on the first two blocks of three columns.

The coefficient tuple determines the parameters in L⁴ × K. A nonzero tuple gives a nonzero polynomial of degree at most q³, so its evaluation kernel has dimension at most three and its matrix has rank at least nine. Together these facts give an injective map from the parameter space to the matrix space and a code of dimension 27.

The projection onto the first three columns yields a nonzero rank-nine matrix. The projection onto the first four columns gives the dimension bound for competing codes. This is the fixed example from Section 4, Problem 1.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Mat`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Problem1RankNine`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.Supported`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.SupportedDimension27WithRankLowerBound`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.height`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1RankNine_iff_exists_supported_dim27`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersRankNine.problem1_rank_nine`
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients](FerrersCoefficients.md)
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction](MRDDensityColumnReduction.md)
