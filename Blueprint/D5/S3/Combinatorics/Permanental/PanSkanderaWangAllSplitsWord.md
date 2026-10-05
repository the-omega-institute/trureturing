# PanSkanderaWangAllSplitsWord

## Abstract

ListOfFn lists the function values in increasing Fin order.

**Definition 1.1 (word).**

$$\forall n \in \mathbb {N},\; \forall w \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{word}\left(w\right) = \operatorname{ListOfFn}\left(fun (i : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{val}\left(w\left(i\right)\right) + 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord.word` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

ListOfFn lists the function values in increasing Fin order. Adding one converts the zero-based permutation to the paper's one-based word.

**Definition 1.2 (ofWord).**

$$\forall n \in \mathbb {N},\; \forall x \in \operatorname{List}\left(\mathbb {N}\right),\; \forall hx \in \operatorname{IsPerm}\left(n, x\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{val}\left(\operatorname{ofWord}\left(x, hx\right)\left(i\right)\right) = \operatorname{getElem}\left(x, \operatorname{val}\left(i\right)\right) - 1$$

*Formalization.* `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord.ofWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

ofWord is Equiv.ofBijective of the function i mapped to the Fin n value x[val i] - 1. The displayed equation is its defining value expression; getElem uses the index bound obtained from hx. Permutation membership gives positive bounded entries and verifies injectivity and surjectivity. Subtraction on natural numbers is truncated.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord.ofWord`
- Truth anchor: `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord.word`
- Dependency: [D5/S3/Combinatorics/PanSkanderaWangBruhat](../PanSkanderaWangBruhat.md)
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat](PanSkanderaWangAllSplitsBruhat.md)
