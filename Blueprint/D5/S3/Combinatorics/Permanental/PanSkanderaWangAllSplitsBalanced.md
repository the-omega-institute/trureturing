# PanSkanderaWangAllSplitsBalanced

## Abstract

For every order at least four, the alternating principal permanent product is at most the product for the balanced initial split.

**Theorem 1.1 (balanced).**

$$\forall n \in \mathbb {N},\; (4 \le n) \Rightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{TNN}\left(A\right)) \Rightarrow (\operatorname{principalPermanent}\left(A, \operatorname{evenIndices}\left(n\right)\right) \cdot \operatorname{principalPermanent}\left(A, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right) \setminus \operatorname{evenIndices}\left(n\right)\right) \le \operatorname{principalPermanent}\left(A, \operatorname{prefixIndices}\left(n, \operatorname{natDiv}\left(n, 2\right)\right)\right) \cdot \operatorname{principalPermanent}\left(A, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right) \setminus \operatorname{prefixIndices}\left(n, \operatorname{natDiv}\left(n, 2\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBalanced.balanced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

For every order at least four, the alternating principal permanent product is at most the product for the balanced initial split. natDiv is natural-number division, so natDiv(n,2) is the floor of n/2. The recursive bijection pairs the terms, and the rank-to-chain construction proves each paired monomial inequality.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBalanced.balanced`
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBijection](PanSkanderaWangAllSplitsBijection.md)
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock](PanSkanderaWangAllSplitsBlock.md)
