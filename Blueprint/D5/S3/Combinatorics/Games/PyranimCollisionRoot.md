# All-width root limits for Pyranim collisions

## Abstract

All-width root limits for Pyranim collisions

**Definition 1.1 (Ordered collision event).**

$$\forall n \in \mathbb{N},\; \operatorname{CollisionPairs}\left(n\right) = \{p:\operatorname{Stable}\left(n\right)\times \operatorname{Stable}\left(n\right)\mid \operatorname{GameIso}\left(p.1, p.2\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimCollisionRoot.CollisionPairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

On an ordered pair of width-n stable positions the event is recursive game isomorphism.

**Definition 1.2 (Independent uniform collision probability).**

$$\forall n \in \mathbb{N},\; \operatorname{collisionProbability}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{CollisionPairs}\left(n\right)\right):\mathbb{R})}{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{Stable}\left(n\right)\right):\mathbb{R})^{2}}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimCollisionRoot.collisionProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Independent draws with replacement give equal mass to every ordered pair. Every stable position of width n is eligible.

**Lemma 1.3 (Nonempty sample space).**

$$\forall n \in \mathbb{N},\; 0 < \operatorname{Nat}.\operatorname{card}\left(\operatorname{Stable}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimCollisionRoot.stable_card_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The empty stable position belongs to the sample space at every width.

**Theorem 1.4 (All-width root limit for independent draws).**

$$\operatorname{Tendsto}\left((\lambda (n:\mathbb{N})\mapsto(\operatorname{collisionProbability}\left(n\right))^{\frac{1}{(n:\mathbb{R})}}), atTop, \operatorname{nhds}\left(1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimCollisionRoot.tendsto_collisionProbability_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Full blocks of width b+2 have Catalan(b+1) choices. Equal block multiplicities induce an order isomorphism and transport every legal option. Counting multiplicity vectors gives a lower bound after division by the square of the Catalan population. First let n grow through every width with b fixed, including the final remainder, and then let b grow. The probability is at most one.

**Definition 1.5 (Ordered pairs of distinct positions).**

$$\forall n \in \mathbb{N},\; \operatorname{DistinctPairs}\left(n\right) = \{p:\operatorname{Stable}\left(n\right)\times \operatorname{Stable}\left(n\right)\mid p.1\neq p.2\}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimCollisionRoot.DistinctPairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

Pairs exclude the diagonal of literal equality.

**Definition 1.6 (Distinct ordered collisions).**

$$\forall n \in \mathbb{N},\; \operatorname{DistinctCollisionPairs}\left(n\right) = \{p:\operatorname{CollisionPairs}\left(n\right)\mid p.val.1\neq p.val.2\}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimCollisionRoot.DistinctCollisionPairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

A distinct collision is an ordered collision whose two literal positions differ.

**Definition 1.7 (Uniform distinct-pair collision probability).**

$$\forall n \in \mathbb{N},\; \operatorname{distinctCollisionProbability}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{DistinctCollisionPairs}\left(n\right)\right):\mathbb{R})}{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{DistinctPairs}\left(n\right)\right):\mathbb{R})}$$

*Formalization.* `D5/S3/Combinatorics/Games/PyranimCollisionRoot.distinctCollisionProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

There are distinct ordered pairs at every positive width. Width zero uses totalized real division as its Lean convention.

**Theorem 1.8 (Removing the diagonal).**

$$\forall n \in \mathbb{N},\; (1 < \operatorname{Nat}.\operatorname{card}\left(\operatorname{Stable}\left(n\right)\right)) \Rightarrow (\operatorname{distinctCollisionProbability}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{Stable}\left(n\right)\right):\mathbb{R}) \cdot \operatorname{collisionProbability}\left(n\right) - 1}{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{Stable}\left(n\right)\right):\mathbb{R}) - 1})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimCollisionRoot.distinctCollisionProbability_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

With N stable positions the event includes all N diagonal pairs. Removing the diagonal from the numerator and denominator gives the displayed equality when N is greater than one.

**Theorem 1.9 (All-width root limit for distinct draws).**

$$\operatorname{Tendsto}\left((\lambda (n:\mathbb{N})\mapsto(\operatorname{distinctCollisionProbability}\left(n\right))^{\frac{1}{(n:\mathbb{R})}}), atTop, \operatorname{nhds}\left(1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimCollisionRoot.tendsto_distinctCollisionProbability_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

The independent collision probability eventually dominates twice the diagonal mass, by the independent root limit and the exponential size of the population. The distinct-pair probability then lies between half the independent probability and the independent probability.

**Lemma 1.10 (Transferring decay to distinct draws).**

$$(\operatorname{Tendsto}\left(\operatorname{collisionProbability}, atTop, \operatorname{nhds}\left(0\right)\right)) \Rightarrow (\operatorname{Tendsto}\left(\operatorname{distinctCollisionProbability}, atTop, \operatorname{nhds}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/PyranimCollisionRoot.tendsto_distinctCollisionProbability_zero_of` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yoav Binyamin, Evan Kniffen (2026). *Enumerating Pyranim Isomorphisms*. URL: <https://arxiv.org/abs/2611.16153v1>.

*Commentary.*

At positive widths the distinct-pair probability lies between zero and the independent probability.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionRoot.CollisionPairs`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionRoot.DistinctCollisionPairs`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionRoot.DistinctPairs`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionRoot.collisionProbability`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionRoot.distinctCollisionProbability`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionRoot.distinctCollisionProbability_eq`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionRoot.stable_card_pos`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionRoot.tendsto_collisionProbability_root`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionRoot.tendsto_distinctCollisionProbability_root`
- Truth anchor: `D5/S3/Combinatorics/Games/PyranimCollisionRoot.tendsto_distinctCollisionProbability_zero_of`
- Dependency: [D5/S3/Combinatorics/Games/PyranimPosition](PyranimPosition.md)
