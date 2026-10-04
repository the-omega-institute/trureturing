# PanSkanderaWangAllSplitsPadding

## Abstract

The defining FinCases expression places one in the new first diagonal position, zero in the rest of its row and column, and A in the remaining block.

**Definition 1.1 (padOne).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \forall i \in \operatorname{Fin}\left(n + 1\right),\; \forall j \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{padOne}\left(A\right)\left(i, j\right) = \operatorname{FinCases}\left(\operatorname{FinCases}\left(1, \operatorname{const}\left(0\right), j\right), fun (x : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{FinCases}\left(0, fun (y : \operatorname{Fin}\left(n\right)) \mapsto A\left(x, y\right), j\right), i\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding.padOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The defining FinCases expression places one in the new first diagonal position, zero in the rest of its row and column, and A in the remaining block. FinCases uses the zero and successor branches; const(0) is the anonymous constant-zero function.

**Theorem 1.2 (tnn padOne).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{TNN}\left(A\right)) \Rightarrow (\operatorname{TNN}\left(\operatorname{padOne}\left(A\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding.tnn_padOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Adding the first identity entry preserves every increasing square minor. A minor selecting both first indices reduces to the old minor; selecting only one gives a zero row or column; selecting neither gives an old minor of the same size.

**Definition 1.3 (padLeft).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{padLeft}\left(A, 0\right) = A) \land (\forall d \in \mathbb {N},\; \operatorname{padLeft}\left(A, d + 1\right) = \operatorname{padOne}\left(\operatorname{padLeft}\left(A, d\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding.padLeft` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Repeated left padding is defined by these two recursion equations. After d steps the matrix has order n+d.

**Theorem 1.4 (tnn padLeft).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{TNN}\left(A\right)) \Rightarrow (\forall d \in \mathbb {N},\; \operatorname{TNN}\left(\operatorname{padLeft}\left(A, d\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding.tnn_padLeft` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Every number of left identity-padding steps preserves the literal ordered-minor predicate, by induction on the number of steps.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding.padLeft`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding.padOne`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding.tnn_padLeft`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding.tnn_padOne`
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock](PanSkanderaWangAllSplitsBlock.md)
