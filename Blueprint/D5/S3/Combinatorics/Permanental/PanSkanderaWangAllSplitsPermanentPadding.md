# PanSkanderaWangAllSplitsPermanentPadding

## Abstract

The defining filter pulls an index set back along Fin.succ, extracting precisely its old matrix indices..

**Definition 1.1 (oldIndices).**

$$\forall n \in \mathbb {N},\; \forall s \in \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right),\; \operatorname{oldIndices}\left(s\right) = \operatorname{filter}\left(\operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), fun (i : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{succ}\left(i\right) \in s\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.oldIndices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The defining filter pulls an index set back along Fin.succ, extracting precisely its old matrix indices.

**Theorem 1.2 (principal padOne).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \forall s \in \operatorname{Finset}\left(\operatorname{Fin}\left(n + 1\right)\right),\; \operatorname{principalPermanent}\left(\operatorname{padOne}\left(A\right), s\right) = \operatorname{principalPermanent}\left(A, \operatorname{oldIndices}\left(s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.principal_padOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Every selected principal permanent loses only the newly adjoined identity coordinate. If that coordinate is present, decomposing permutations of an Option type leaves precisely the permutations that fix it; all other summands contain a zero entry.

**Definition 1.3 (splitProduct).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \forall h \in \mathbb {N},\; \operatorname{splitProduct}\left(A, h\right) = \operatorname{principalPermanent}\left(A, \operatorname{prefixIndices}\left(n, h\right)\right) \cdot \operatorname{principalPermanent}\left(A, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right) \setminus \operatorname{prefixIndices}\left(n, h\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.splitProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

This is the product of the two complementary principal permanents for the literal initial split.

**Definition 1.4 (parityProduct).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \operatorname{parityProduct}\left(A\right) = \operatorname{principalPermanent}\left(A, \operatorname{evenIndices}\left(n\right)\right) \cdot \operatorname{principalPermanent}\left(A, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right) \setminus \operatorname{evenIndices}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.parityProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

This is the product of the principal permanents on the even and odd one-based indices.

**Theorem 1.5 (split padLeft).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \forall d \in \mathbb {N},\; \forall h \in \mathbb {N},\; \operatorname{splitProduct}\left(\operatorname{padLeft}\left(A, d\right), h + d\right) = \operatorname{splitProduct}\left(A, h\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.split_padLeft` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

After d left identity coordinates, the split at h+d has the same permanent product as the original split at h. Induction tracks the literal initial index set through each padding step.

**Theorem 1.6 (parity padLeft).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \forall d \in \mathbb {N},\; \operatorname{parityProduct}\left(\operatorname{padLeft}\left(A, d\right)\right) = \operatorname{parityProduct}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.parity_padLeft` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Left identity padding preserves the alternating permanent product. Each step swaps the two old parity classes, and multiplication makes the product invariant under that swap.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.oldIndices`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.parityProduct`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.parity_padLeft`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.principal_padOne`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.splitProduct`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.split_padLeft`
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding](PanSkanderaWangAllSplitsPadding.md)
