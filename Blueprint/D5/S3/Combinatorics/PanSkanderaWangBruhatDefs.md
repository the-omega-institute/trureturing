# Pan-Skandera-Wang Bruhat Definitions

## Abstract

Definitions of the Pan-Skandera-Wang map, its source family, and its Bruhat claim.

**Definition 1.1 (Rank tableau count).**

$$\forall x \in \operatorname{List}\left(\mathbb {N}\right), p \in \mathbb {N}, q \in \mathbb {N},\; \operatorname{rank}\left(x, p, q\right) = \operatorname{countGE}\left(q, \operatorname{take}\left(x, p\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.rank` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The rank counts entries at least q among the first p positions.

**Definition 1.2 (Permutation predicate).**

$$\forall n \in \mathbb {N}, x \in \operatorname{List}\left(\mathbb {N}\right),\; (\operatorname{IsPerm}\left(n, x\right)) \Leftrightarrow (\operatorname{Perm}\left(x, \operatorname{rangePrime}\left(1, n\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.IsPerm` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

A word is a permutation when it is a rearrangement of the interval from one through n.

**Definition 1.3 (Bruhat tableau order).**

$$\forall n \in \mathbb {N}, x \in \operatorname{List}\left(\mathbb {N}\right), y \in \operatorname{List}\left(\mathbb {N}\right),\; (\operatorname{BruhatLE}\left(n, x, y\right)) \Leftrightarrow ((\operatorname{IsPerm}\left(n, x\right)) \land \left((\operatorname{IsPerm}\left(n, y\right)) \land (\forall p \in \mathbb {N}, q \in \mathbb {N},\; \operatorname{rank}\left(x, p, q\right) \le \operatorname{rank}\left(y, p, q\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.BruhatLE` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The strong Bruhat order is given by the tableau criterion of Björner and Brenti, Theorem 2.1.5.

**Definition 1.4 (The source family A).**

$$\forall n \in \mathbb {N}, w \in \operatorname{List}\left(\mathbb {N}\right),\; (\operatorname{A}\left(n, w\right)) \Leftrightarrow ((\operatorname{IsPerm}\left(n, w\right)) \land (\operatorname{Perm}\left(\operatorname{take}\left(w, \operatorname{floorHalf}\left(n\right)\right), \operatorname{rangePrime}\left(1, \operatorname{floorHalf}\left(n\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.A` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The first half of the word permutes the initial interval while the whole word is a permutation.

**Definition 1.5 (Reverse-complement map).**

$$\forall n \in \mathbb {N}, w \in \operatorname{List}\left(\mathbb {N}\right),\; \operatorname{RU}\left(n, w\right) = \operatorname{map}\left(\Lambda v \mapsto n + 1 - v, \operatorname{reverse}\left(w\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.RU` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The reverse-complement map reverses a word and replaces each value v by n plus one minus v.

**Definition 1.6 (Pair swapping).**

$$(\operatorname{swapPairs}\left(\operatorname{nil}\left(\right)\right) = \operatorname{nil}\left(\right)) \land \left((\operatorname{swapPairs}\left(\operatorname{singleton}\left(a\right)\right) = \operatorname{singleton}\left(a\right)) \land (\forall a \in \mathbb {N}, b \in \mathbb {N}, t \in \operatorname{List}\left(\mathbb {N}\right),\; \operatorname{swapPairs}\left(\operatorname{cons}\left(a, \operatorname{cons}\left(b, t\right)\right)\right) = \operatorname{cons}\left(b, \operatorname{cons}\left(a, \operatorname{swapPairs}\left(t\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.swapPairs` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Pair swapping exchanges adjacent entries and leaves a final unpaired entry fixed.

**Definition 1.7 (Suffix-swapping insertion).**

$$\forall q \in \mathbb {N}, w \in \operatorname{List}\left(\mathbb {N}\right),\; \operatorname{inss}\left(q, w\right) = \operatorname{append}\left(\operatorname{take}\left(w, q - 1\right), \operatorname{cons}\left(\operatorname{length}\left(w\right) + 1, \operatorname{swapPairs}\left(\operatorname{drop}\left(w, q - 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.inss` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The operation inserts the new maximum at position q and swaps successive pairs in the suffix.

**Definition 1.8 (Base map).**

$$\forall w \in \operatorname{List}\left(\mathbb {N}\right),\; \operatorname{f4}\left(w\right) = \operatorname{if}\left(w = \operatorname{list}\left(1, 2, 3, 4\right), \operatorname{list}\left(1, 2, 3, 4\right), \operatorname{if}\left(w = \operatorname{list}\left(1, 2, 4, 3\right), \operatorname{list}\left(1, 4, 3, 2\right), \operatorname{if}\left(w = \operatorname{list}\left(2, 1, 3, 4\right), \operatorname{list}\left(3, 2, 1, 4\right), \operatorname{if}\left(w = \operatorname{list}\left(2, 1, 4, 3\right), \operatorname{list}\left(3, 4, 1, 2\right), w\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.f4` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The base map is specified on the four words of size four and fixes every other input at that size.

**Definition 1.9 (Recursive Pan-Skandera-Wang map).**

$$(\forall w \in \operatorname{List}\left(\mathbb {N}\right),\; \operatorname{f}\left(0, w\right) = w) \land (\forall m \in \mathbb {N}, w \in \operatorname{List}\left(\mathbb {N}\right),\; \operatorname{f}\left(m + 1, w\right) = \operatorname{if}\left(m + 1 \le 4, \operatorname{f4}\left(w\right), \operatorname{if}\left(\operatorname{mod}\left(m, 2\right) = 0, \operatorname{inss}\left(2 \cdot \left(\operatorname{idxOf}\left(w, m + 1\right) + 1 - \operatorname{floorHalf}\left(m\right)\right) - 1, \operatorname{f}\left(m, \operatorname{eraseIdx}\left(w, \operatorname{idxOf}\left(w, m + 1\right)\right)\right)\right), \operatorname{inss}\left(2 \cdot \left(\operatorname{idxOf}\left(w, m + 1\right) + 1 - \operatorname{floorHalf}\left(m\right) - 1\right), \operatorname{RU}\left(m, \operatorname{f}\left(m, \operatorname{RU}\left(m, \operatorname{eraseIdx}\left(w, \operatorname{idxOf}\left(w, m + 1\right)\right)\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.f` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The recursive map uses the base cases, the position of the maximum, insertion, and reverse-complementation according to parity.

**Definition 1.10 (Bruhat monotonicity claim).**

$$\forall n \in \mathbb {N},\; (4 \le n) \Rightarrow (\forall w \in \operatorname{List}\left(\mathbb {N}\right),\; (\operatorname{A}\left(n, w\right)) \Rightarrow (\operatorname{BruhatLE}\left(n, w, \operatorname{f}\left(n, w\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.claim` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

For every size at least four, each source word is below its image in the strong Bruhat order.

## References

- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.A`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.BruhatLE`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.IsPerm`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.RU`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.f`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.f4`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.inss`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.rank`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.swapPairs`
