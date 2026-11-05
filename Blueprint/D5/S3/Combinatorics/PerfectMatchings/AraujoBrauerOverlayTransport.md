# AraujoBrauerOverlayTransport

## Abstract

Constructive results for complete mappings of diagram monoids.

**Definition 1.1 (halfTransportSign).**

$$\forall \{n r : \mathbb{N}\} (D E : HalfDiagram n r) (w : OverlayTransport (halfPermutation D) (halfPermutation E)) , halfTransportSign D E w = Equiv . Perm . sign (((((Equiv . subtypeEquivRight (halfPermutationFixed D)) . trans (D . 1 . val . orderIsoOfFin D . 1 . property) . toEquiv . symm) . symm) . trans w . transport) . trans ((Equiv . subtypeEquivRight (halfPermutationFixed E)) . trans (E . 1 . val . orderIsoOfFin E . 1 . property) . toEquiv . symm))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfTransportSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.2 (SignedHalfCycles).**

$$structure SignedHalfCycles (n r : \mathbb{N}) where cycles : OneTrianglePermutation (HalfDiagram n r) transport : \forall D , OverlayTransport (halfPermutation D) (halfPermutation (cycles . perm D)) twoSign : \forall D , D \neg \in cycles . triangle \to halfTransportSign D (cycles.perm D) (transport D) * halfTransportSign (cycles . perm D) (cycles.perm (cycles . perm D)) (transport (cycles . perm D)) = 1 threeSign : \forall D , D \in cycles . triangle \to halfTransportSign D (cycles.perm D) (transport D) * halfTransportSign (cycles . perm D) (cycles.perm (cycles . perm D)) (transport (cycles . perm D)) * halfTransportSign (cycles . perm (cycles . perm D)) (cycles.perm (cycles . perm (cycles . perm D))) (transport (cycles . perm (cycles . perm D))) = - 1$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.SignedHalfCycles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.3 (rank_two_signed_half_cycles).**

$$\forall (k : \mathbb{N}) , Nonempty (SignedHalfCycles (6 + 4 * k) 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.rank_two_signed_half_cycles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.4 (rank_three_signed_half_cycles).**

$$\forall (k : \mathbb{N}) , Nonempty (SignedHalfCycles (7 + 4 * k) 3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.rank_three_signed_half_cycles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.5 (Overlay).**

$$\forall \{X : Type *\} , \forall (p q : Equiv . Perm X) , Overlay p q = (Relation . EqvGen (\lambda u v \mapsto p u = v \lor q u = v))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.Overlay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.6 (involution_card_mod_two).**

$$\forall \{X : Type *\} , \forall [Fintype X] , \forall [DecidableEq X] , \forall (f : Function . End X) , (Function . Involutive f) \to (Nat . ModEq 2 (Nat . card X) (Nat . card (Function . fixedPoints f)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.involution_card_mod_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.7 (OverlayTransport).**

$$structure OverlayTransport \{X : Type *\} (p q : Equiv . Perm X) where transport : Function . fixedPoints p \equiv Function . fixedPoints q connected : \forall x : Function . fixedPoints p , Overlay p q x (transport x) unique : \forall (x : Function . fixedPoints p) (y : Function . fixedPoints q) , Overlay p q x y \to transport x = y$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.OverlayTransport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.8 (halfPermutation).**

$$\forall \{n r : \mathbb{N}\} , \forall (D : HalfDiagram n r) , halfPermutation D = (Equiv . Perm . subtypeCongr (Equiv . refl \{x : Fin n \mid x \in D . 1 . val\}) D . 2 . val)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.9 (halfPermutationFixed).**

$$\forall \{n r : \mathbb{N}\} , \forall (D : HalfDiagram n r) , \forall (x : Fin n) , halfPermutation D x = x \iff x \in D . 1 . val$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfPermutationFixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.10 (halfPermutationInvolutive).**

$$\forall \{n r : \mathbb{N}\} , \forall (D : HalfDiagram n r) , Function . Involutive (halfPermutation D)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfPermutationInvolutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.Overlay`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.OverlayTransport`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.SignedHalfCycles`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfPermutation`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfPermutationFixed`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfPermutationInvolutive`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfTransportSign`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.involution_card_mod_two`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.rank_three_signed_half_cycles`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.rank_two_signed_half_cycles`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles](AraujoBrauerHalfTriangles.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing](AraujoBrauerSubsetPairing.md)
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](../../Zeros/Convolution/PerfectMatchingCount.md)
