# AraujoBrauerSourceMonoids

## Abstract

Constructive results for complete mappings of diagram monoids.

**Definition 1.1 (blockSize).**

$$\forall \{n : \mathbb{N}\} , \forall (p : (Setoid (Bool \times Fin n))) , \forall (x : (Bool \times Fin n)) , blockSize p x = (Nat . card \{y : (Bool \times Fin n) \mid p . r x y\})$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.blockSize` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.2 (Brauer).**

$$\forall (n : \mathbb{N}) , Brauer n = (\{p : (Setoid (Bool \times Fin n)) \mid \forall x : (Bool \times Fin n) , blockSize p x = 2\})$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.Brauer` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.3 (PartialBrauer).**

$$\forall (n : \mathbb{N}) , PartialBrauer n = (\{p : (Setoid (Bool \times Fin n)) \mid \forall x : (Bool \times Fin n) , blockSize p x \leq 2\})$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.PartialBrauer` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.4 (firstEmbedding).**

$$\forall \{n : \mathbb{N}\} , \forall (x : (Bool \times Fin n)) , firstEmbedding x = ((if x . 1 then 1 else 0 , x . 2))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.firstEmbedding` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.5 (secondEmbedding).**

$$\forall \{n : \mathbb{N}\} , \forall (x : (Bool \times Fin n)) , secondEmbedding x = ((if x . 1 then 2 else 1 , x . 2))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.secondEmbedding` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.6 (exteriorEmbedding).**

$$\forall \{n : \mathbb{N}\} , \forall (x : (Bool \times Fin n)) , exteriorEmbedding x = ((if x . 1 then 2 else 0 , x . 2))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.exteriorEmbedding` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.7 (productGraphEdge).**

$$\forall \{n : \mathbb{N}\} , \forall (p q : (Setoid (Bool \times Fin n))) , \forall (u v : Fin 3 \times Fin n) , productGraphEdge p q u v = ((\exists x y : (Bool \times Fin n) , firstEmbedding x = u \land firstEmbedding y = v \land p . r x y) \lor (\exists x y : (Bool \times Fin n) , secondEmbedding x = u \land secondEmbedding y = v \land q . r x y))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.productGraphEdge` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.8 (partitionProduct).**

$$\forall \{n : \mathbb{N}\} , \forall (p q : (Setoid (Bool \times Fin n))) , partitionProduct p q = (Setoid . comap exteriorEmbedding (Relation . EqvGen . setoid (productGraphEdge p q)))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partitionProduct` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.9 (BrauerSourceMonoid).**

$$structure BrauerSourceMonoid (n : \mathbb{N}) where algebra : Monoid (Brauer n) multiplication : \forall a b : Brauer n , (algebra . mul a b) . val = partitionProduct a . val b . val$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.BrauerSourceMonoid` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.10 (PartialBrauerSourceMonoid).**

$$structure PartialBrauerSourceMonoid (n : \mathbb{N}) where algebra : Monoid (PartialBrauer n) multiplication : \forall a b : PartialBrauer n , (algebra . mul a b) . val = partitionProduct a . val b . val$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.PartialBrauerSourceMonoid` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.11 (involutionSetoid).**

$$\forall \{X : Type\} (p : Equiv . Perm X) (hp : Function . Involutive p) (h : Equivalence (\lambda x y \mapsto x = y \lor p x = y)) , involutionSetoid p hp = Setoid . mk (\lambda x y \mapsto x = y \lor p x = y) h$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.involutionSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.12 (involutionSetoidBlockTwo).**

$$\forall \{X : Type *\} , \forall (p : Equiv . Perm X) , \forall (hp : Function . Involutive p) , (\forall x , p x \neq x) \to (\forall (x : X) , Nat . card \{y : X \mid (involutionSetoid p hp) . r x y\} = 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.involutionSetoidBlockTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.13 (brauerOfMatching).**

$$\forall \{n : \mathbb{N}\} , \forall (p : Equiv . Perm ((Bool \times Fin n))) , \forall (hp : Function . Involutive p) , \forall (hn : \forall x , p x \neq x) , brauerOfMatching p hp hn = (\langle involutionSetoid p hp , involutionSetoidBlockTwo p hp hn \rangle)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.brauerOfMatching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.14 (brauer_matching_representation).**

$$\forall \{n : \mathbb{N}\} , \forall (a : Brauer n) , \exists p : Equiv . Perm ((Bool \times Fin n)) , \exists hp : Function . Involutive p , (\forall x , p x \neq x) \land involutionSetoid p hp = a . val$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.brauer_matching_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.15 (involutionSetoidBlockLeTwo).**

$$\forall \{X : Type *\} , \forall (p : Equiv . Perm X) , \forall (hp : Function . Involutive p) , \forall (x : X) , Nat . card \{y : X \mid (involutionSetoid p hp) . r x y\} \leq 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.involutionSetoidBlockLeTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.16 (partial_partition_involution_representation).**

$$\forall \{X : Type *\} , \forall [Finite X] , \forall (q : Setoid X) , (\forall x , Nat . card \{y : X \mid q . r x y\} \leq 2) \to (\exists p : Equiv . Perm X , \exists hp : Function . Involutive p , involutionSetoid p hp = q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partial_partition_involution_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.17 (involutionSetoid_injective).**

$$\forall \{X : Type *\} , \forall (p q : Equiv . Perm X) , \forall (hp : Function . Involutive p) , \forall (hq : Function . Involutive q) , (involutionSetoid p hp = involutionSetoid q hq) \to (p = q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.involutionSetoid_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.18 (partialPartitionEquivInvolution).**

$$\forall (X : Type) [Finite X] (h : Function . Bijective (\lambda p : \{p : Equiv . Perm X \mid Function . Involutive p\} \mapsto (\langle involutionSetoid p . val p . property , involutionSetoidBlockLeTwo p . val p . property \rangle : \{q : Setoid X \mid \forall x , Nat . card \{y : X \mid q . r x y\} \leq 2\}))) , partialPartitionEquivInvolution X = Equiv . ofBijective (\lambda p : \{p : Equiv . Perm X \mid Function . Involutive p\} \mapsto (\langle involutionSetoid p . val p . property , involutionSetoidBlockLeTwo p . val p . property \rangle : \{q : Setoid X \mid \forall x , Nat . card \{y : X \mid q . r x y\} \leq 2\})) h$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partialPartitionEquivInvolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.19 (inv_eq_self_iff_involutive).**

$$\forall \{X : Type *\} , \forall (p : Equiv . Perm X) , p ^{-1} = p \iff Function . Involutive p$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.inv_eq_self_iff_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.20 (partial_matching_card_even).**

$$\forall \{X : Type *\} , \forall [Fintype X] , (2 \leq Fintype . card X) \to (Even (Nat . card \{p : Equiv . Perm X \mid Function . Involutive p\}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partial_matching_card_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.21 (firstEmbedding_injective).**

$$\forall \{n : \mathbb{N}\} , Function . Injective (firstEmbedding n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.firstEmbedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.22 (secondEmbedding_injective).**

$$\forall \{n : \mathbb{N}\} , Function . Injective (secondEmbedding n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.secondEmbedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.23 (productGraph).**

$$\forall \{n : \mathbb{N}\} , \forall (p q : (Setoid (Bool \times Fin n))) , productGraph p q = (Relation . EqvGen . setoid (productGraphEdge p q))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.productGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.24 (partitionProduct_assoc).**

$$\forall \{n : \mathbb{N}\} , \forall (p q r : (Setoid (Bool \times Fin n))) , partitionProduct (partitionProduct p q) r = partitionProduct p (partitionProduct q r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partitionProduct_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.25 (identityPartition).**

$$\forall (n : \mathbb{N}) , identityPartition n = (Setoid . ker Prod . snd)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.identityPartition` (`✓ std3`).

*Citation.* João Araújo; Wolfram Bentz; Peter J. Cameron; Kevin Hendrey; Michael Kinyon (2026). *Complete Mappings of Semigroups, Problem 15.11*. URL: <https://arxiv.org/abs/2608.25092v1>.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.26 (partitionProduct_identity_left).**

$$\forall \{n : \mathbb{N}\} , \forall (p : (Setoid (Bool \times Fin n))) , partitionProduct (identityPartition n) p = p$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partitionProduct_identity_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.27 (identityPartition_brauer).**

$$\forall (n : \mathbb{N}) , \forall (x : (Bool \times Fin n)) , blockSize (identityPartition n) x = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.identityPartition_brauer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.28 (partitionProductPartialClosed).**

$$\forall \{n : \mathbb{N}\} , \forall (a b : PartialBrauer n) , \forall (x : (Bool \times Fin n)) , blockSize (partitionProduct a . val b . val) x \leq 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partitionProductPartialClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.29 (source_monoids_exist).**

$$\forall (n : \mathbb{N}) , (\exists : BrauerSourceMonoid n , True) \land (\exists : PartialBrauerSourceMonoid n , True)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.source_monoids_exist` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.Brauer`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.BrauerSourceMonoid`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.PartialBrauer`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.PartialBrauerSourceMonoid`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.blockSize`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.brauerOfMatching`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.brauer_matching_representation`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.exteriorEmbedding`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.firstEmbedding`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.firstEmbedding_injective`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.identityPartition`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.identityPartition_brauer`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.inv_eq_self_iff_involutive`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.involutionSetoid`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.involutionSetoidBlockLeTwo`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.involutionSetoidBlockTwo`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.involutionSetoid_injective`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partialPartitionEquivInvolution`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partial_matching_card_even`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partial_partition_involution_representation`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partitionProduct`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partitionProductPartialClosed`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partitionProduct_assoc`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.partitionProduct_identity_left`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.productGraph`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.productGraphEdge`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.secondEmbedding`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.secondEmbedding_injective`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.source_monoids_exist`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing](FiniteEndpointPairing.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit](InvolutionOrbitSplit.md)
