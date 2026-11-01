# Finite walks and exact components of circulants

## Abstract

Actual connected components are generated additive cosets, with explicit even and odd coordinates.

All circulant graphs here keep their original additive vertices. A finite walk accumulates generator differences. Conversely, vertices reachable from zero form an additive subgroup containing the connection set. Translation supplies the native isomorphism from the generated subgroup to every actual component support.

**Theorem 1.1 (Reachability is generated membership).**

$$\forall u \in A,\; \forall v \in A,\; \operatorname{Reachable}\left(\operatorname{circulantGraph}\left(S\right), u, v\right) \Leftrightarrow \operatorname{mem}\left(\operatorname{sub}\left(v, u\right), \operatorname{AddSubgroupClosure}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CirculantComponents.circulant_reachable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This holds for every additive commutative group A and every connection set S. The forward direction inducts on an actual finite walk. The reverse direction closes reachable vertices under addition and negation, then translates the resulting walk.

**Theorem 1.2 (Exact gcd count).**

$$\forall n \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \left(\operatorname{Nonzero}\left(n\right) \land \operatorname{Divides}\left(b, n\right)\right) \Rightarrow \operatorname{NatCard}\left(\operatorname{Components}\left(\operatorname{circulantGraph}\left(\operatorname{pairSet}\left(a, b\right)\right)\right)\right) = \operatorname{gcd}\left(a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CirculantComponents.component_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertices are ZMod n, the two natural jumps are cast into that group, and b divides n. The generated subgroup is the cyclic subgroup of gcd(a,b); the existing subgroup-index supplier gives the number of additive cosets.

**Theorem 1.3 (Odd generator order).**

$$\forall p \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \operatorname{Odd}\left(\operatorname{addOrderOf}\left(\operatorname{cast}\left(a, \operatorname{ZMod}\left(\operatorname{mul}\left(2, \operatorname{add}\left(p, 2\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{gcd}\left(\operatorname{mul}\left(2, \operatorname{add}\left(p, 2\right)\right), a\right) = \operatorname{mul}\left(2, \operatorname{gcd}\left(a, \operatorname{add}\left(p, 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CirculantComponents.odd_component_number` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the generator order is odd, the antipode is absent from its cyclic subgroup. Adding the order-two antipode doubles that subgroup. The proof constructs product coordinates and derives the exact factor of two in the component count.

**Theorem 1.4 (Even generator order).**

$$\forall p \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \operatorname{Even}\left(\operatorname{addOrderOf}\left(\operatorname{cast}\left(a, \operatorname{ZMod}\left(\operatorname{mul}\left(2, \operatorname{add}\left(p, 2\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{gcd}\left(a, \operatorname{add}\left(p, 2\right)\right) = \operatorname{gcd}\left(\operatorname{mul}\left(2, \operatorname{add}\left(p, 2\right)\right), a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CirculantComponents.even_component_number` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An even-order cyclic subgroup already contains the unique antipode. Its cyclic coordinates send the antipodal jump to half its order, producing the native Mobius component graph without assuming a decomposition.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CirculantComponents.circulant_reachable_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CirculantComponents.component_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CirculantComponents.even_component_number`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CirculantComponents.odd_component_number`
