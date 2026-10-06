# PanSkanderaWangAllSplitsReverse

## Abstract

The defining submatrix expression reverses both rows and columns.

**Definition 1.1 (reverseMatrix).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \operatorname{reverseMatrix}\left(A\right) = \operatorname{submatrix}\left(A, \operatorname{FinRev}\left(n\right), \operatorname{FinRev}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsReverse.reverseMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The defining submatrix expression reverses both rows and columns. FinRev(n) is the function Fin.rev on Fin n.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsReverse.reverseMatrix`
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding](PanSkanderaWangAllSplitsPermanentPadding.md)
