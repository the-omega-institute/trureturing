# PanSkanderaWangAllSplitsBruhat

## Abstract

The operator sum adds over the finite domain of its function.

**Definition 1.1 (rankF).**

$$\forall n \in \mathbb {N},\; \forall w \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall p \in \mathbb {N},\; \forall q \in \mathbb {N},\; \operatorname{rankF}\left(w, p, q\right) = \operatorname{sum}\left(fun (k : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{ite}\left((\operatorname{val}\left(k\right) < p) \land (q \le \operatorname{val}\left(w\left(k\right)\right)), (1 : \mathbb {Z}), (0 : \mathbb {Z})\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.rankF` (`✓ std3`).

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The operator sum adds over the finite domain of its function. This integer-valued prefix rank counts positions below p whose zero-based permutation values are at least q.

**Definition 1.2 (RankLE).**

$$\forall n \in \mathbb {N},\; \forall w \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall u \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{RankLE}\left(w, u\right)) \Leftrightarrow (\forall p \in \mathbb {N},\; \forall q \in \mathbb {N},\; \operatorname{rankF}\left(w, p, q\right) \le \operatorname{rankF}\left(u, p, q\right))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.RankLE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Rank domination compares every prefix length and every value threshold.

**Definition 1.3 (UpStep).**

$$\forall n \in \mathbb {N},\; \forall w \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall v \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{UpStep}\left(w, v\right)) \Leftrightarrow (\exists i \in \operatorname{Fin}\left(n\right),\; \exists j \in \operatorname{Fin}\left(n\right),\; (i < j) \land \left((w\left(i\right) < w\left(j\right)) \land (v = w \cdot \operatorname{swap}\left(i, j\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.UpStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

A generating upward edge swaps increasing positions whose values are increasing. Multiplication is permutation composition in the Lean convention.

**Theorem 1.4 (rank lifting step).**

$$\forall n \in \mathbb {N},\; \forall w \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall u \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; ((i < j) \land \left((w\left(i\right) < w\left(j\right)) \land \left((w\left(j\right) \le u\left(i\right)) \land \left((\forall k \in \operatorname{Fin}\left(n\right),\; (k < i) \Rightarrow (w\left(k\right) = u\left(k\right))) \land \left((\forall k \in \operatorname{Fin}\left(n\right),\; (i < k) \Rightarrow ((k < j) \Rightarrow (\neg ((w\left(i\right) < w\left(k\right)) \land (w\left(k\right) \le u\left(i\right)))))) \land (\operatorname{RankLE}\left(w, u\right))\right)\right)\right)\right)) \Rightarrow (\operatorname{RankLE}\left(w \cdot \operatorname{swap}\left(i, j\right), u\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.rank_lifting_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

If the earlier positions agree and no intervening source value lies in the stated interval, the indicated upward transposition remains below u in every prefix rank. The rank-gap count supplies the extra unit when a threshold crosses the swapped values.

**Theorem 1.5 (exists lifting step).**

$$\forall n \in \mathbb {N},\; \forall w \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall u \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{RankLE}\left(w, u\right)) \Rightarrow ((w \ne u) \Rightarrow (\exists v \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{UpStep}\left(w, v\right)) \land (\operatorname{RankLE}\left(v, u\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.exists_lifting_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Distinct rank-comparable permutations admit an upward transposition that preserves domination by the upper permutation. The first differing position and the first admissible later value determine the step.

**Theorem 1.6 (rank to chain).**

$$\forall n \in \mathbb {N},\; \forall w \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall u \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{RankLE}\left(w, u\right)) \Rightarrow (\operatorname{ReflTransGen}\left(UpStep, w, u\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.rank_to_chain` (`✓ std3`). ∎

*Citation.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

Every rank comparison is realized by a finite reflexive transitive chain of upward swaps. The position-value score decreases strictly at each chosen lifting step, which terminates the construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.RankLE`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.UpStep`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.exists_lifting_step`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.rankF`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.rank_lifting_step`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.rank_to_chain`
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsChain](PanSkanderaWangAllSplitsChain.md)
