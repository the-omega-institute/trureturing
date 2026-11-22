# Noncrossing partitions in refinement order

## Abstract

Noncrossing refinement has more atoms than Tamari order from rank three.

**Definition 1.1 (Partitions of the ordered ground set).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.Partitions`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.Partitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Partitions(n) is the Mathlib Finpartition of the universal Fin(n) set. Adding one to each element identifies its ground order with the ordered set from 1 to n.

**Definition 1.2 (Membership in one block).**

$$\forall n \in \mathbb{N},\; \forall P \in \operatorname{Partitions}\left(n\right),\; \forall x \in \operatorname{Fin}\left(n\right),\; \forall y \in \operatorname{Fin}\left(n\right),\; \operatorname{Shares}\left(P, x, y\right) \Leftrightarrow (y \in \operatorname{part}\left(P, x\right))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.Shares` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Shares(P, x, y) means y belongs to the block of the partition P that contains x.

**Definition 1.3 (The noncrossing condition).**

$$\forall n \in \mathbb{N},\; \forall P \in \operatorname{Partitions}\left(n\right),\; \operatorname{IsNoncrossing}\left(P\right) \Leftrightarrow \left(\neg (\exists a \in \operatorname{Fin}\left(n\right),\; \exists b \in \operatorname{Fin}\left(n\right),\; \exists c \in \operatorname{Fin}\left(n\right),\; \exists d \in \operatorname{Fin}\left(n\right),\; a < b \land \left(b < c \land \left(c < d \land \left(\operatorname{Shares}\left(P, a, c\right) \land \left(\operatorname{Shares}\left(P, b, d\right) \land \left(\neg \operatorname{Shares}\left(P, a, b\right)\right)\right)\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.IsNoncrossing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are no four increasing elements alternating between two distinct blocks.

**Definition 1.4 (Noncrossing partitions).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.NoncrossingPartitions`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.NoncrossingPartitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict the finite partition carrier to IsNoncrossing and retain the Mathlib refinement order.

**Definition 1.5 (The least partition).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.ncOrderBot`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.ncOrderBot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The partition into singletons is noncrossing and is the lower bound in refinement order.

**Definition 1.6 (The greatest partition).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.ncOrderTop`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.ncOrderTop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The one-block partition is noncrossing and is the upper bound in refinement order.

**Theorem 1.7 (Noncrossing refinement separates at rank three).**

$$\forall n \in \mathbb{N},\; 3 \le n \Rightarrow \left(\neg \operatorname{Nonempty}\left(\operatorname{OrderIso}\left(\operatorname{Trees}\left(n\right), \operatorname{NoncrossingPartitions}\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.no_tamari_noncrossing_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every two-element block with all other blocks singletons is an atom. Their number in rank n ≥ 3 exceeds the bound of n − 1 for Tamari atoms.

**Theorem 1.8 (Noncrossing refinement at rank one).**

$$\operatorname{Subsingleton}\left(\operatorname{NoncrossingPartitions}\left(1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.nc_one_subsingleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a one-point ground set all partitions coincide.

**Theorem 1.9 (Noncrossing refinement at rank two).**

$$\forall P \in \operatorname{NoncrossingPartitions}\left(2\right),\; (P = \perp) \lor (P = \operatorname{top})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.nc_two_bot_or_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a two-point ground set the points are either in separate blocks or together.

**Theorem 1.10 (The two partitions at rank two).**

$$\operatorname{bot}\left(\operatorname{NoncrossingPartitions}\left(2\right)\right) \ne \operatorname{top}\left(\operatorname{NoncrossingPartitions}\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.nc_two_bot_ne_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The partition into singletons and the one-block partition differ on whether the two points share a block.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.IsNoncrossing`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.NoncrossingPartitions`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.Partitions`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.Shares`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.ncOrderBot`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.ncOrderTop`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.nc_one_subsingleton`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.nc_two_bot_ne_top`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.nc_two_bot_or_top`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.no_tamari_noncrossing_iso`
- Dependency: [D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies](MaximumFamilies.md)
