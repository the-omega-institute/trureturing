# Huber's Minimum-Volume Cuboid Conjecture

## Abstract

The smallest first edge, then the smallest second edge, gives minimum cuboid volume.

**Definition 1.1 (Cuboids of a prescribed surface).**

$$\forall n \in \mathbb{N},\; cuboids\left(n\right) = \operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} p : (\mathbb{N} \times (\mathbb{N} \times \mathbb{N})) \mapsto ((p.1 \le p.2.1) \land ((p.2.1 \le p.2.2) \land (p.1 \cdot p.2.1 + p.2.1 \cdot p.2.2 + p.1 \cdot p.2.2 = 3 \cdot n^{2})))), \operatorname{Finset}.\operatorname{product}\left(\operatorname{Finset}.\operatorname{Icc}\left(1, 3 \cdot n^{2}\right), \operatorname{Finset}.\operatorname{product}\left(\operatorname{Finset}.\operatorname{Icc}\left(1, 3 \cdot n^{2}\right), \operatorname{Finset}.\operatorname{Icc}\left(1, 3 \cdot n^{2}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/OeisA375786CuboidMinimumVolume.cuboids` (`✓ std3`).

*Citation.* F. Huber (2024). *OEIS A375786: minimum volume of a cuboid with the surface of an n-cube*. URL: <https://oeis.org/A375786>.

*Commentary.*

OEIS A375786, NAME (unpaginated): "a(n) is the minimum volume of an integer-sided cuboid having the same surface as a cube with edge length n." The triple p represents edges x = p.1, y = p.2.1 and z = p.2.2, ordered x ≤ y ≤ z. The equation xy + yz + xz = 3n² says the surface is 6n². Each positive edge is at most 3n², so the three inclusive intervals contain every such cuboid. Finset.product forms the right-associated product, and Finset.filter keeps the ordered solutions.

**Definition 1.2 (Volume).**

$$\forall p \in (\mathbb{N} \times (\mathbb{N} \times \mathbb{N})),\; volume\left(p\right) = p.1 \cdot p.2.1 \cdot p.2.2$$

*Formalization.* `D5/S3/Arith/OeisA375786CuboidMinimumVolume.volume` (`✓ std3`).

*Citation.* F. Huber (2024). *OEIS A375786: minimum volume of a cuboid with the surface of an n-cube*. URL: <https://oeis.org/A375786>.

*Commentary.*

OEIS A375786, NAME (unpaginated): "a(n) is the minimum volume of an integer-sided cuboid having the same surface as a cube with edge length n." The volume of the triple is the product of its three edge lengths.

**Definition 1.3 (Huber's conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\forall p \in (\mathbb{N} \times (\mathbb{N} \times \mathbb{N})),\; (p \in cuboids\left(n\right)) \Rightarrow ((\forall q \in (\mathbb{N} \times (\mathbb{N} \times \mathbb{N})),\; (q \in cuboids\left(n\right)) \Rightarrow ((p.1 < q.1) \lor ((p.1 = q.1) \land (p.2.1 \le q.2.1)))) \Rightarrow (\forall q \in (\mathbb{N} \times (\mathbb{N} \times \mathbb{N})),\; (q \in cuboids\left(n\right)) \Rightarrow (volume\left(p\right) \le volume\left(q\right))))))$$

*Formalization.* `D5/S3/Arith/OeisA375786CuboidMinimumVolume.claim` (`✓ std3`).

*Citation.* F. Huber (2024). *OEIS A375786: minimum volume of a cuboid with the surface of an n-cube*. URL: <https://oeis.org/A375786>.

*Commentary.*

OEIS A375786, COMMENTS (unpaginated): "Conjecture: From the integer-sided cuboids with same surface 6*n^2 always the one with the smallest edge length has the minimum volume. If there are several integer-sided cuboids having the smallest edge length, then the one with the smallest second smallest edge length has the minimum volume (checked up to a(1000))." Here n is any natural number at least one. The hypothesis on p chooses the least pair (p.1, p.2.1) in lexicographic order. The conclusion compares its volume with every member of the same finite set, using a non-strict inequality.

**Theorem 1.4 (The lexicographic minimum has minimum volume).**

$$\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\forall p \in (\mathbb{N} \times (\mathbb{N} \times \mathbb{N})),\; (p \in cuboids\left(n\right)) \Rightarrow ((\forall q \in (\mathbb{N} \times (\mathbb{N} \times \mathbb{N})),\; (q \in cuboids\left(n\right)) \Rightarrow ((p.1 < q.1) \lor ((p.1 = q.1) \land (p.2.1 \le q.2.1)))) \Rightarrow (\forall q \in (\mathbb{N} \times (\mathbb{N} \times \mathbb{N})),\; (q \in cuboids\left(n\right)) \Rightarrow (volume\left(p\right) \le volume\left(q\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/OeisA375786CuboidMinimumVolume.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. Huber (2024). *OEIS A375786: minimum volume of a cuboid with the surface of an n-cube*. URL: <https://oeis.org/A375786>.

*Commentary.*

Write S = 3n². Ordered positive edges satisfy 3x² ≤ S and xS ≤ 2xyz + x³; hence x ≥ 3 forces xyz ≥ S. At x = 1 and n ≥ 2, the volume is strictly below S − 4. If no solution has first edge one, the explicit odd-n solution forces n to be even. Writing n = 2m then gives the solution (2, 2, 3m² − 1), of volume S − 4. With the first edge fixed, a smaller second edge gives no larger volume. These comparisons cover every competitor; n = 1 has only the unit cube.

## References

- Truth anchor: `D5/S3/Arith/OeisA375786CuboidMinimumVolume.claim`
- Truth anchor: `D5/S3/Arith/OeisA375786CuboidMinimumVolume.cuboids`
- Truth anchor: `D5/S3/Arith/OeisA375786CuboidMinimumVolume.result`
- Truth anchor: `D5/S3/Arith/OeisA375786CuboidMinimumVolume.volume`
