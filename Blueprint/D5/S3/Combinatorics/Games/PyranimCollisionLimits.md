# Root and zero limits for Pyranim collisions

## Abstract

Root and zero limits for Pyranim collisions

**Definition 1.1 (Bound for words avoiding a prescribed block).**

$$\forall n \in \mathbb{N},\; \forall L \in \mathbb{N},\; \operatorname{unmarkedBound}\left(n, L\right) = (2^{2 \cdot (L + 1)} - 1)^{\operatorname{floor}\left(\frac{2 \cdot (n + 1)}{2 \cdot (L + 1)}\right)} \cdot 2^{\operatorname{mod}\left(2 \cdot (n + 1), 2 \cdot (L + 1)\right)}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimCollisionLimits.unmarkedBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

At each width-n encoding there are q complete slots of length M and a tail of length r. M is 2(L+1), q is the floor of 2(n+1)/M and r is its remainder. The letter equivalence with Bool and Mathlib’s fixed-length vector count give 2^M words in a slot and 2^r words in the tail. Mathlib’s Set.card_ne_eq counts the words unequal to the prescribed block, giving 2^M−1 slot choices. Splitting off the first slot gives an injection into a nonpivot block and a shorter avoiding word.

**Theorem 1.2 (Uniform collision-class bound).**

$$\forall n \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall I \in \operatorname{Stable}\left(n\right),\; (\operatorname{Nat}.\operatorname{card}\left(\{J:\operatorname{Stable}\left(n\right)\mid \operatorname{GameIso}\left(I, J\right)\}\right):\mathbb{R}) \le \frac{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{Stable}\left(n\right)\right):\mathbb{R})}{(L:\mathbb{R}) + 1} + (\operatorname{unmarkedBound}\left(n, L\right):\mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimCollisionLimits.gameIso_class_card_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Equivalent games have the same maximum complete legal path length, equal to chip count. In each marked position, changing the first marked slot produces L+1 different counts and preserves the identity of the slot. The remaining words avoid a prescribed pattern in every complete slot.

**Theorem 1.3 (Decay for independent draws).**

$$\operatorname{Tendsto}\left(\operatorname{collisionProbability}, atTop, \operatorname{nhds}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimCollisionLimits.tendsto_collisionProbability_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Sum the uniform class bound over all first draws. At fixed L the unmarked fraction goes to zero because the loss in each slot is exponential in the number of slots, whereas the Catalan denominator differs from 4^(n+1) by at most a polynomial factor. The remaining bound is 1/(L+1), which tends to zero.

**Theorem 1.4 (Decay for uniformly sampled distinct pairs).**

$$\operatorname{Tendsto}\left(\operatorname{distinctCollisionProbability}, atTop, \operatorname{nhds}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimCollisionLimits.tendsto_distinctCollisionProbability_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The distinct-pair probability is bounded by the independent probability at every positive width, so it tends to zero as well.

**Theorem 1.5 (Root and zero limits for both distributions).**

$$(\operatorname{Tendsto}\left((\lambda (n:\mathbb{N})\mapsto(\operatorname{collisionProbability}\left(n\right))^{\frac{1}{(n:\mathbb{R})}}), atTop, \operatorname{nhds}\left(1\right)\right)) \land ((\operatorname{Tendsto}\left(\operatorname{collisionProbability}, atTop, \operatorname{nhds}\left(0\right)\right)) \land ((\operatorname{Tendsto}\left((\lambda (n:\mathbb{N})\mapsto(\operatorname{distinctCollisionProbability}\left(n\right))^{\frac{1}{(n:\mathbb{R})}}), atTop, \operatorname{nhds}\left(1\right)\right)) \land (\operatorname{Tendsto}\left(\operatorname{distinctCollisionProbability}, atTop, \operatorname{nhds}\left(0\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimCollisionLimits.result` (`✓ std3`). ∎

*Resolves.* `Problems/binyamin-kniffen-2026-pyranim-collision-limits` (proved) by `D5/S3/Combinatorics/Games/PyranimCollisionLimits.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"binyamin-kniffen-2026-pyranim-collision-limits","declaration_gid":"D5/S3/Combinatorics/Games/PyranimCollisionLimits.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The root tends to one and the probability tends to zero at all widths tending to infinity, for independent uniform draws and for uniform distinct pairs. A sharp decay rate, random-start expectations, and the full reverse reconstruction are open within this result’s scope.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionLimits.gameIso_class_card_upper`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionLimits.result`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionLimits.tendsto_collisionProbability_zero`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionLimits.tendsto_distinctCollisionProbability_zero`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionLimits.unmarkedBound`
- Dependency: [D5/S3/Combinatorics/Games/PyranimCollisionRoot](PyranimCollisionRoot.md)
