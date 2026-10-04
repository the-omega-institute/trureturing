# PanSkanderaWangAllSplits

## Abstract

All-split permanental inequality for totally nonnegative real matrices.

**Definition 1.1 (claim).**

$$claim = \left(\forall n \in \mathbb {N},\; (2 \le n) \Rightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{TNN}\left(A\right)) \Rightarrow (\forall h \in \mathbb {N},\; (1 \le h) \Rightarrow ((h \le n - 1) \Rightarrow (\operatorname{principalPermanent}\left(A, \operatorname{evenIndices}\left(n\right)\right) \cdot \operatorname{principalPermanent}\left(A, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right) \setminus \operatorname{evenIndices}\left(n\right)\right) \le \operatorname{principalPermanent}\left(A, \operatorname{prefixIndices}\left(n, h\right)\right) \cdot \operatorname{principalPermanent}\left(A, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right) \setminus \operatorname{prefixIndices}\left(n, h\right)\right)))))\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.claim` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Source (EPTCS 445, p. 139, abstract): “We also conjecture the inequalities (∗) to hold for all TNN matrices and all h = 1, …, n−1.” Section 1 (p. 140): “We conjecture the inequalities to hold for all totally nonnegative matrices and I = [h].” Mathematical glyphs and whitespace follow the displayed source; the prose is verbatim. Lean uses zero-based Fin indices and the paper uses one-based indices. TNN quantifies over every increasing square-minor selection. Each principal permanent is Mathlib Matrix.permanent, with the empty-block permanent equal to one.

**Theorem 1.2 (result).**

$$\forall n \in \mathbb {N},\; (2 \le n) \Rightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{TNN}\left(A\right)) \Rightarrow (\forall h \in \mathbb {N},\; (1 \le h) \Rightarrow ((h \le n - 1) \Rightarrow (\operatorname{principalPermanent}\left(A, \operatorname{evenIndices}\left(n\right)\right) \cdot \operatorname{principalPermanent}\left(A, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right) \setminus \operatorname{evenIndices}\left(n\right)\right) \le \operatorname{principalPermanent}\left(A, \operatorname{prefixIndices}\left(n, h\right)\right) \cdot \operatorname{principalPermanent}\left(A, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right) \setminus \operatorname{prefixIndices}\left(n, h\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.result` (`✓ std3`). ∎

*Resolves.* `Problems/psw-all-split-permanental-inequality` (proved) by `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"psw-all-split-permanental-inequality","declaration_gid":"D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Every real TNN matrix of order at least two satisfies the quoted inequality at each split between one and n-1. The balanced pairing argument, left identity padding and simultaneous reversal give the full range.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.claim`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.result`
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBalanced](PanSkanderaWangAllSplitsBalanced.md)
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsReverse](PanSkanderaWangAllSplitsReverse.md)
