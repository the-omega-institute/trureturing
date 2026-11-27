# Garber et al. Question 6.2

## Abstract

Maximum Boolean antichains have Tamari order with exact comparison boundaries.

**Definition 1.1 (Dyck paths carrying Tamari order).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.TamariDyckPaths`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.TamariDyckPaths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This carrier contains the same semilength-n Dyck paths as DyckPaths(n).

**Definition 1.2 (Transported Tamari order).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.tamariDyckOrder`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.tamariDyckOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compare the trees corresponding to the paths under Mathlib’s fixed-size Dyck-word equivalence, using contextual right-rotation reachability on the trees.

**Theorem 1.3 (The order and both comparison boundaries).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow (\operatorname{IsGreatest}\left(\{k \in \mathbb{N} \mid \exists C \in \operatorname{Set}\left(\operatorname{Trees}\left(n + 1\right)\right),\; \operatorname{IsBooleanFamily}\left(C\right) \land \operatorname{ncard}\left(C\right) = k\}, n\right) \land \left(\operatorname{Nonempty}\left(\operatorname{OrderIso}\left(\operatorname{MaximumFamilies}\left(\operatorname{Trees}\left(n + 1\right), n\right), \operatorname{Trees}\left(n\right)\right)\right) \land \left((\operatorname{Nonempty}\left(\operatorname{OrderIso}\left(\operatorname{MaximumFamilies}\left(\operatorname{Trees}\left(n + 1\right), n\right), \operatorname{NoncrossingPartitions}\left(n\right)\right)\right) \Leftrightarrow (n \le 2)) \land \left((\operatorname{Nonempty}\left(\operatorname{OrderIso}\left(\operatorname{MaximumFamilies}\left(\operatorname{Trees}\left(n + 1\right), n\right), \operatorname{DyckPaths}\left(n\right)\right)\right) \Leftrightarrow (n \le 2)) \land \operatorname{Nonempty}\left(\operatorname{OrderIso}\left(\operatorname{MaximumFamilies}\left(\operatorname{Trees}\left(n + 1\right), n\right), \operatorname{TamariDyckPaths}\left(n\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.result` (`✓ std3`). ∎

*Resolves.* `Problems/garber-et-al-2026-tamari-boolean-antichains` (proved) by `D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"garber-et-al-2026-tamari-boolean-antichains","declaration_gid":"D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Julien Garber, Lina S. Goltermann, Daniel Horiatakis, Dennis König and Tal Gottesman (2026). *Counting Boolean antichains*. DOI: [10.48550/arXiv.2608.27126](https://doi.org/10.48550/arXiv.2608.27126). URL: <https://arxiv.org/html/2608.27126v2#S6.Thmtheorem2>.

*Commentary.*

Garber, Goltermann, Horiatakis, König and Gottesman ask in Question 6.2 of Counting Boolean antichains (2026), “Is the order on Boolean antichains of maximal size in the Tamari lattice equivalent to the Tamari order, the order on non-crossing partitions, or the order on Dyck paths?” For every n ≥ 1 the maximum size in Tamari rank n + 1 is n, and generated lower-set inclusion is order-isomorphic to contextual right rotations at rank n. Noncrossing refinement and Dyck height dominance each give an isomorphic order exactly at n = 1 and n = 2. The Dyck paths with transported Tamari order give an isomorphism for every n ≥ 1. The order of families on arbitrary lattices lies outside the first sentence.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.TamariDyckPaths`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.result`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.tamariDyckOrder`
- Dependency: [D5/S3/Combinatorics/Lattices/Tamari/DyckHeight](DyckHeight.md)
- Dependency: [D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement](NoncrossingRefinement.md)
