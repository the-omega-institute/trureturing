# Pan-Skandera-Wang Selection Invariant

## Abstract

Selection positions and their invariance under reverse-complementation and matched insertion.

**Definition 1.1 (Selection positions).**

$$\forall p \in \mathbb {N}, d \in \mathbb {N},\; \operatorname{selectionPositions}\left(p, d\right) = \operatorname{append}\left(\operatorname{range}\left(p - d\right), \operatorname{map}\left(\Lambda k \mapsto p - d + 2 \cdot k + 1, \operatorname{range}\left(d\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.selectionPositions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The selected zero-based positions consist of an initial interval followed by every other position in a window of width twice d.

**Definition 1.2 (Selected entries).**

$$\forall x \in \operatorname{List}\left(\mathbb {N}\right), p \in \mathbb {N}, d \in \mathbb {N},\; \operatorname{selection}\left(x, p, d\right) = \operatorname{map}\left(\Lambda i \mapsto \operatorname{getD}\left(x, i, 0\right), \operatorname{selectionPositions}\left(p, d\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.selection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The selection is the list of entries at the selected positions, with zero used outside the word.

**Definition 1.3 (Threshold count).**

$$\forall q \in \mathbb {N}, x \in \operatorname{List}\left(\mathbb {N}\right),\; \operatorname{countGE}\left(q, x\right) = \operatorname{countP}\left(x, \Lambda v \mapsto q \le v\right)$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.countGE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The threshold count records how many entries in a word are at least q.

**Definition 1.4 (Selection invariant).**

$$\forall n \in \mathbb {N}, x \in \operatorname{List}\left(\mathbb {N}\right), y \in \operatorname{List}\left(\mathbb {N}\right),\; (\operatorname{SelectionInvariant}\left(n, x, y\right)) \Leftrightarrow (\forall p \in \mathbb {N}, d \in \mathbb {N}, q \in \mathbb {N},\; ((p \le n) \land \left((d \le p) \land \left((d \le n - p) \land \left((1 \le q) \land (q \le n + 1)\right)\right)\right)) \Rightarrow (\operatorname{countGE}\left(q, \operatorname{take}\left(x, p\right)\right) \le \operatorname{countGE}\left(q, \operatorname{selection}\left(y, p, d\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.SelectionInvariant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The invariant compares threshold counts in the first p source entries with every legal selection of the target word.

**Theorem 1.5 (Reverse-complement preserves permutations).**

$$\forall n \in \mathbb {N}, x \in \operatorname{List}\left(\mathbb {N}\right),\; (\operatorname{IsPerm}\left(n, x\right)) \Rightarrow (\operatorname{IsPerm}\left(n, \operatorname{RU}\left(n, x\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.ru_isPerm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Reverse-complementation sends every permutation of the interval from one through n to another permutation of that interval.

**Theorem 1.6 (Reverse-complement preserves the invariant).**

$$\forall n \in \mathbb {N}, x \in \operatorname{List}\left(\mathbb {N}\right), y \in \operatorname{List}\left(\mathbb {N}\right),\; ((\operatorname{IsPerm}\left(n, x\right)) \land \left((\operatorname{IsPerm}\left(n, y\right)) \land (\operatorname{SelectionInvariant}\left(n, x, y\right))\right)) \Rightarrow (\operatorname{SelectionInvariant}\left(n, \operatorname{RU}\left(n, x\right), \operatorname{RU}\left(n, y\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.selectionInvariant_ru` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The selection invariant is unchanged when both words are reverse-complemented.

**Definition 1.7 (Ordinary maximum insertion).**

$$\forall n \in \mathbb {N}, r \in \mathbb {N}, a \in \operatorname{List}\left(\mathbb {N}\right),\; \operatorname{insertMax}\left(n, r, a\right) = \operatorname{append}\left(\operatorname{take}\left(a, r - 1\right), \operatorname{cons}\left(n, \operatorname{drop}\left(a, r - 1\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.insertMax` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Ordinary insertion places the new maximum n at the one-based position r.

**Theorem 1.8 (Matched insertion preserves the invariant).**

$$\forall n \in \mathbb {N}, m \in \mathbb {N}, r \in \mathbb {N}, s \in \mathbb {N}, a \in \operatorname{List}\left(\mathbb {N}\right), b \in \operatorname{List}\left(\mathbb {N}\right),\; ((n = m + 1) \land \left((\operatorname{IsPerm}\left(m, a\right)) \land \left((\operatorname{IsPerm}\left(m, b\right)) \land \left((\operatorname{SelectionInvariant}\left(m, a, b\right)) \land \left((1 \le r) \land \left((r \le n) \land \left((s = 2 \cdot r - n) \land (1 \le s)\right)\right)\right)\right)\right)\right)) \Rightarrow (\operatorname{SelectionInvariant}\left(n, \operatorname{insertMax}\left(n, r, a\right), \operatorname{inss}\left(s, b\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.selectionInvariant_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Matched ordinary insertion and suffix-swapping insertion preserve the full selection invariant under the stated parity and position conditions.

## References

- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.SelectionInvariant`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.countGE`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.insertMax`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.ru_isPerm`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.selection`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.selectionInvariant_insert`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.selectionInvariant_ru`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.selectionPositions`
- Dependency: [D5/S3/Combinatorics/PanSkanderaWangBruhatDefs](PanSkanderaWangBruhatDefs.md)
