# Strict adjacent ascents of words

## Abstract

Strict adjacent-ascent count shared by natural-valued word families.

**Definition 1.1 (Strict adjacent-ascent count).**

$$\forall w \in \operatorname{List}\left(\mathbb{N}\right),\; \operatorname{asc}\left(w\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{range}\left(\operatorname{length}\left(w\right) - 1\right), (i:\mathbb{N})\mapsto\operatorname{getD}\left(w, i, 0\right) < \operatorname{getD}\left(w, i + 1, 0\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/WordAscents.asc` (`✓ std3`).

*Citation.* Per Alexandersson, Aryaman Jal, and Maena Quemener (2025). *Real-rootedness of rook-Eulerian polynomials*. DOI: [10.48550/arXiv.2502.05939](https://doi.org/10.48550/arXiv.2502.05939). URL: <https://arxiv.org/abs/2502.05939v1>.

*Commentary.*

For every list w of natural numbers, count the indices i in range(length(w) minus one) for which getD(w,i,0) < getD(w,i+1,0). Both queried positions exist for each counted index. Natural subtraction is truncated: empty words and singletons have count zero. Equality is not an ascent. Section 2, page 4 of the cited source uses this strict adjacent comparison. This is the unchanged statistic shared by the multiset rook-Eulerian polynomials and the ordinary ascent-sequence, Dyck and Narayana constructions; it imposes no Ferrers-board, content, avoidance or monotonicity hypothesis.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/WordAscents.asc`
