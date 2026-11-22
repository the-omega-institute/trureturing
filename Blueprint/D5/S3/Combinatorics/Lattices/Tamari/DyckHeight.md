# Dyck paths ordered by prefix height

## Abstract

Dyck height dominance has a unique coatom in the ranks with two Tamari coatoms.

**Definition 1.1 (Dyck paths of fixed semilength).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.DyckPaths`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.DyckPaths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A DyckPaths(n) value contains a Mathlib DyckWord and a proof that its semilength is n.

**Definition 1.2 (Prefix height).**

$$\forall p \in DyckWord,\; \forall i \in \mathbb{N},\; \operatorname{dyckHeight}\left(p, i\right) = \operatorname{count}\left(U, \operatorname{take}\left(i, \operatorname{toList}\left(p\right)\right)\right) - \operatorname{count}\left(D, \operatorname{take}\left(i, \operatorname{toList}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.dyckHeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The height is the integer up-step count minus down-step count in the prefix of length i. The height after the last step is zero.

**Definition 1.3 (Height dominance).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{DyckPaths}\left(n\right),\; \forall q \in \operatorname{DyckPaths}\left(n\right),\; (p \le q) \Leftrightarrow (\forall i \in \mathbb{N},\; \operatorname{dyckHeight}\left(\operatorname{val}\left(p\right), i\right) \le \operatorname{dyckHeight}\left(\operatorname{val}\left(q\right), i\right))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.dyckHeightOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A path is below another exactly when all its prefix heights are at most those of the other path.

**Definition 1.4 (The top path).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.dyckOrderTop`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.dyckOrderTop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mountain with n up-steps followed by n down-steps dominates every path.

**Definition 1.5 (The path immediately below the mountain).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.nearMountain`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.nearMountain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Enclose the valleys of the word UDUD in k matching outer pairs of steps. The path then has semilength k + 2.

**Theorem 1.6 (The nearly maximal path is proper).**

$$\forall k \in \mathbb{N},\; \operatorname{nearMountain}\left(k\right) \ne \operatorname{top}\left(\operatorname{DyckPaths}\left(k + 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.near_ne_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the middle prefix it has fewer up-steps than the mountain.

**Theorem 1.7 (Height dominance separates at rank three).**

$$\forall n \in \mathbb{N},\; 3 \le n \Rightarrow \left(\neg \operatorname{Nonempty}\left(\operatorname{OrderIso}\left(\operatorname{Trees}\left(n\right), \operatorname{DyckPaths}\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.no_tamari_dyck_height_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every proper Dyck path lies below the same near-mountain path, so there is just one coatom. Tamari order at rank n ≥ 3 has two distinct coatoms.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.DyckPaths`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.dyckHeight`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.dyckHeightOrder`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.dyckOrderTop`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.nearMountain`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.near_ne_top`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.no_tamari_dyck_height_iso`
- Dependency: [D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies](MaximumFamilies.md)
