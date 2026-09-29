# Pan-Skandera-Wang Bruhat Theorem

## Abstract

The Pan-Skandera-Wang map raises every source permutation in the strong Bruhat order.

**Theorem 1.1 (Reverse-complement source membership).**

$$\forall m \in \mathbb {N}, a \in \operatorname{List}\left(\mathbb {N}\right),\; ((\operatorname{IsPerm}\left(m, a\right)) \land \left((\operatorname{mod}\left(m, 2\right) = 1) \land (\operatorname{Perm}\left(\operatorname{take}\left(a, \operatorname{floorHalf}\left(m\right) + 1\right), \operatorname{rangePrime}\left(1, \operatorname{floorHalf}\left(m\right) + 1\right)\right))\right)) \Rightarrow (\operatorname{A}\left(m, \operatorname{RU}\left(m, a\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PanSkanderaWangBruhat.ru_mem_A_of_longPrefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

For an odd size, a permutation whose initial long prefix is the initial interval becomes a member of A after reverse-complementation.

**Theorem 1.2 (Pan-Skandera-Wang Bruhat theorem).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PanSkanderaWangBruhat.result` (`✓ std3`). ∎

*Resolves.* `Problems/psw-bruhat-increasing-bijection` (proved) by `D5/S3/Combinatorics/PanSkanderaWangBruhat.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"psw-bruhat-increasing-bijection","declaration_gid":"D5/S3/Combinatorics/PanSkanderaWangBruhat.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sihong Pan, Mark Skandera, Jiayuan Wang (2026). *Permanental Inequalities and Unit Interval Orders*. DOI: [10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17). URL: <https://arxiv.org/abs/2606.13162v1>.

*Commentary.*

The recursive map satisfies the Bruhat monotonicity claim for every size at least four, as proved by the selection invariant and the four base words.

## References

- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhat.result`
- Truth anchor: `D5/S3/Combinatorics/PanSkanderaWangBruhat.ru_mem_A_of_longPrefix`
- Dependency: [D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant](PanSkanderaWangBruhatInvariant.md)
