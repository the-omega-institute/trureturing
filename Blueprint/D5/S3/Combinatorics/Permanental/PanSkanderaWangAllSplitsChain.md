# PanSkanderaWangAllSplitsChain

## Abstract

TNN means that every square submatrix selected by increasing row and column embeddings has nonnegative determinant.

**Definition 1.1 (TNN).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{TNN}\left(A\right)) \Leftrightarrow (\forall k \in \mathbb {N},\; \forall r \in \operatorname{OrderEmbedding}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right),\; \forall c \in \operatorname{OrderEmbedding}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right),\; 0 \le \operatorname{det}\left(\operatorname{submatrix}\left(A, r, c\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.TNN` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Source, Section 1 (p. 139): “We call A ∈ Matₙ×ₙ(ℝ) totally nonnegative if each of its minors is negative.” The next sentence specifies the defining inequalities det(Aᵢ,ⱼ) ≥ 0. The word negative in the first sentence conflicts with those displayed inequalities; TNN uses the displayed nonnegative inequalities. Every square submatrix selected by increasing row and column embeddings has nonnegative determinant. OrderEmbedding denotes the increasing order embeddings in the Lean statement, including the empty minor.

**Definition 1.2 (principalPermanent).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \forall s \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{principalPermanent}\left(A, s\right) = \operatorname{permanent}\left(\operatorname{submatrix}\left(A, fun (i : s) \mapsto \operatorname{val}\left(i\right), fun (j : s) \mapsto \operatorname{val}\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.principalPermanent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The principal permanent uses Matrix.permanent on the literal subtype of indices belonging to s. Here val on a subtype is its underlying Fin n index; an empty principal permanent is one.

**Definition 1.3 (evenIndices).**

$$\forall n \in \mathbb {N},\; \operatorname{evenIndices}\left(n\right) = \operatorname{filter}\left(\operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), fun (i : \operatorname{Fin}\left(n\right)) \mapsto \left(\operatorname{val}\left(i\right) + 1\right) \bmod 2 = 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.evenIndices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Lean indices start at zero. Filtering by (val i + 1) mod 2 = 0 therefore selects the even indices printed in the paper.

**Definition 1.4 (prefixIndices).**

$$\forall n \in \mathbb {N},\; \forall h \in \mathbb {N},\; \operatorname{prefixIndices}\left(n, h\right) = \operatorname{filter}\left(\operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), fun (i : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{val}\left(i\right) < h\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.prefixIndices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The initial h indices are selected by val i < h, with no restriction on h in this definition.

**Definition 1.5 (monomial).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \forall w \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{monomial}\left(A, w\right) = \operatorname{prod}\left(fun (k : \operatorname{Fin}\left(n\right)) \mapsto A\left(k, w\left(k\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.monomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The operator prod multiplies its function over every element of the finite domain. The monomial places the permutation value in the column index.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.TNN`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.evenIndices`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.monomial`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.prefixIndices`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain.principalPermanent`
