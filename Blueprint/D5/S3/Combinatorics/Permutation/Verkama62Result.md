# Verkama Conjecture 6.2

## Abstract

Verkama Conjecture 6.2.

**Theorem 1.1 (Existence of a complete run).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Result.complete_run`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Result.complete_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For every n at least three and permutation pi of Fin n, assume the value-labelled inversion graph is connected and its induced complement of every singleton is connected. Then there is a northeast ear run ending at every point. An anchored triangle or 3412 square starts the construction. Induction on the number of missing points uses the anchored extension and the deletion connectivity of every run. This proof uses no pattern avoidance.

**Theorem 1.2 (The exact inversion bound).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; ((3 \le n) \land (\neg \operatorname{ContainsOneBased}\left(p\right)) \land (\operatorname{Connected}\left(\operatorname{valueGraph}\left(p\right)\right)) \land (\forall v \in \operatorname{Fin}\left(n\right),\; \operatorname{Connected}\left(\operatorname{delete}\left(\operatorname{valueGraph}\left(p\right), v\right)\right))) \Rightarrow (\frac{7}{4} \cdot n - 3 \le \operatorname{inv}\left(\operatorname{word}\left(p\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/verkama-2026-conjecture-62` (proved) by `D5/S3/Combinatorics/Permutation/Verkama62Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"verkama-2026-conjecture-62","declaration_gid":"D5/S3/Combinatorics/Permutation/Verkama62Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For every integer n at least zero and every permutation pi of {1,...,n}, suppose pi classically avoids 351624 and its inversion graph has at least three vertices, is connected, and remains connected after deletion of each vertex. Then inv(pi) is at least (7/4)n - 3, with comparison in the rationals. In the formula, delete(G,v) is the graph induced on all vertices other than v. In Lean the graph vertices are values in Fin n, the source label of i is i.val+1, and the graph is defined by the strictly negative integer product of the difference of value labels and the difference of their inverse-position labels. The at-least-three-vertices condition is 3 <= n. An occurrence uses six increasing positions and the relative value order [3,5,1,6,2,4], corresponding to [2,4,0,5,1,3] in Fin 6. The inversion statistic is the existing list counter on the one-based permutation word, proved equal to the number of increasing-position inversions, each counted once. A complete ear run and avoidance imply 7n <= 4 inv(pi)+12, which is equivalent to the displayed rational bound. No further avoidance, bipartiteness, asymptotic qualification, or assumed ear decomposition is used.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Result.complete_run`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Result.result`
- Dependency: [D5/S3/Combinatorics/Permutation/Verkama62Run](Verkama62Run.md)
