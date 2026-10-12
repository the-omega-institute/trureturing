# Induced subcubes of the Boolean hypercube

## Abstract

Induced Boolean cubes are exactly coordinate down-cubes, with unique top and direction set.

**Definition 1.1 (Coordinate erasure).**

$$\forall n \in \mathrm{Nat},\; \forall v \in Fin\left(n\right) \to Bool,\; \forall T \in Finset\left(Fin\left(n\right)\right),\; erase\left(v, T\right) = fun (q: Fin\left(n\right)) \mapsto if q \in T then false else v\left(q\right)$$

*Formalization.* `D5/S3/Combinatorics/Hamming/InducedSubcubes.erase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

erase v T changes v to false on the coordinates in T and leaves every other coordinate unchanged.

**Definition 1.2 (Coordinate down-cube).**

$$\forall n \in \mathrm{Nat},\; \forall v \in Fin\left(n\right) \to Bool,\; \forall S \in Finset\left(Fin\left(n\right)\right),\; downCube\left(v, S\right) = \{w: Fin\left(n\right) \to Bool | \exists T \in Finset\left(Fin\left(n\right)\right),\; (Finset.Subset\left(T, S\right)) \land (w = erase\left(v, T\right))\}$$

*Formalization.* `D5/S3/Combinatorics/Hamming/InducedSubcubes.downCube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

downCube v S is the set of words obtained by erasing an arbitrary subset T of S from v.

**Theorem 1.3 (Erasing no coordinates).**

$$\forall n \in \mathrm{Nat},\; \forall v \in Fin\left(n\right) \to Bool,\; erase\left(v, \emptyset\right) = v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/InducedSubcubes.erase_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Erasing the empty set leaves every Boolean word unchanged.

**Theorem 1.4 (Top vertex of a down-cube).**

$$\forall n \in \mathrm{Nat},\; \forall v \in Fin\left(n\right) \to Bool,\; \forall S \in Finset\left(Fin\left(n\right)\right),\; v \in downCube\left(v, S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/InducedSubcubes.top_mem_downCube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The top vertex belongs to its coordinate down-cube.

**Theorem 1.5 (Image of a cube map).**

$$\forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall f \in \left(Fin\left(k\right) \to Bool\right) \to \left(Fin\left(n\right) \to Bool\right),\; (Function.Injective\left(f\right)) \Rightarrow ((\forall u \in Fin\left(k\right) \to Bool,\; \forall v \in Fin\left(k\right) \to Bool,\; (hammingDist\left(u, v\right) = 1) \Rightarrow (hammingDist\left(f\left(u\right), f\left(v\right)\right) = 1)) \Rightarrow (\exists d \in Function.Embedding\left(Fin\left(k\right), Fin\left(n\right)\right),\; \forall w \in Fin\left(n\right) \to Bool,\; (w \in Set.range\left(f\right)) \Leftrightarrow (\forall q \in Fin\left(n\right),\; (\neg q \in Set.range\left(d\right)) \Rightarrow (w\left(q\right) = f\left(Function.const\left(Fin\left(k\right), false\right), q\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/InducedSubcubes.cube_map_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective map from a Boolean k-cube to a Boolean n-cube that preserves Hamming-distance-one edges has an image cut out by k distinct coordinate directions; every other coordinate is fixed to its value at the all-false source vertex.

**Theorem 1.6 (Uniqueness of the top and directions).**

$$\forall n \in \mathrm{Nat},\; \forall v \in Fin\left(n\right) \to Bool,\; \forall vPrime \in Fin\left(n\right) \to Bool,\; \forall S \in Finset\left(Fin\left(n\right)\right),\; \forall SPrime \in Finset\left(Fin\left(n\right)\right),\; ((Finset.Subset\left(S, Finset.filter\left(fun (q: Fin\left(n\right)) \mapsto v\left(q\right) = true, Finset.univ\left(\right)\right)\right)) \land ((Finset.Subset\left(SPrime, Finset.filter\left(fun (q: Fin\left(n\right)) \mapsto vPrime\left(q\right) = true, Finset.univ\left(\right)\right)\right)) \land (downCube\left(v, S\right) = downCube\left(vPrime, SPrime\right)))) \Rightarrow ((v = vPrime) \land (S = SPrime))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/InducedSubcubes.downCube_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two down-cubes have direction sets contained in the true coordinates of their respective top vertices and are equal as sets, then their top vertices and direction sets are equal.

**Theorem 1.7 (Classification of induced cubes).**

$$\forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall U \in Set\left(Fin\left(n\right) \to Bool\right),\; (Nonempty\left(SimpleGraph.Iso\left(SimpleGraph.induce\left(hypercube\left(n\right), U\right), hypercube\left(k\right)\right)\right)) \Leftrightarrow (\exists! (p: Prod\left(Fin\left(n\right) \to Bool, Finset\left(Fin\left(n\right)\right)\right)), (Finset.card\left(Prod.snd\left(p\right)\right) = k) \land ((Finset.Subset\left(Prod.snd\left(p\right), Finset.filter\left(fun (q: Fin\left(n\right)) \mapsto Prod.fst\left(p\right)\left(q\right) = true, Finset.univ\left(\right)\right)\right)) \land (U = downCube\left(Prod.fst\left(p\right), Prod.snd\left(p\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/InducedSubcubes.induced_cube_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every set U of Boolean words, the induced hypercube on U is isomorphic to hypercube k exactly when there is a unique pair (v,S) with S.card = k, S contained in the true coordinates of v, and U = downCube v S.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/InducedSubcubes.cube_map_image`
- Truth anchor: `D5/S3/Combinatorics/Hamming/InducedSubcubes.downCube`
- Truth anchor: `D5/S3/Combinatorics/Hamming/InducedSubcubes.downCube_unique`
- Truth anchor: `D5/S3/Combinatorics/Hamming/InducedSubcubes.erase`
- Truth anchor: `D5/S3/Combinatorics/Hamming/InducedSubcubes.erase_empty`
- Truth anchor: `D5/S3/Combinatorics/Hamming/InducedSubcubes.induced_cube_iff`
- Truth anchor: `D5/S3/Combinatorics/Hamming/InducedSubcubes.top_mem_downCube`
- Dependency: [D5/S3/Arith/Coding/CapacityBoxOneBitRigidity](../../Arith/Coding/CapacityBoxOneBitRigidity.md)
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube](../Graph/Hypercube.md)
