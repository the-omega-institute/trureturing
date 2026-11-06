# AraujoBrauerHalfTriangles

## Abstract

Constructive results for complete mappings of diagram monoids.

**Theorem 1.1 (card_matching_fibre_odd).**

$$\forall \{X : Type *\} , \forall [Fintype X] , \forall [DecidableEq X] , \forall (h : \mathbb{N}) , (Fintype . card X = 2 * h) \to (Odd (Fintype . card (FixedPointFreeInvolution X)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.card_matching_fibre_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.2 (OneTrianglePermutation).**

$$structure OneTrianglePermutation (X : Type *) where perm : Equiv . Perm X triangle : Set X triangleCard : Nat . card triangle = 3 triangleInvariant : \forall x , x \in triangle \iff perm x \in triangle noFixed : \forall x , perm x \neq x triangleCube : \forall x , x \in triangle \to perm (perm (perm x)) = x outsideSquare : \forall x , x \neg \in triangle \to perm (perm x) = x$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.OneTrianglePermutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.3 (ThroughSets).**

$$\forall (n r : \mathbb{N}) , ThroughSets n r = (\{T : Finset (Fin n) \mid T . card = r\})$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.ThroughSets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.4 (HalfDiagram).**

$$\forall (n r : \mathbb{N}) , HalfDiagram n r = ((T : ThroughSets n r) \times FixedPointFreeInvolution \{x : Fin n \mid x \neg \in T . val\})$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.HalfDiagram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.5 (complement_card).**

$$\forall \{n r : \mathbb{N}\} , \forall (T : ThroughSets n r) , Fintype . card \{x : Fin n \mid x \neg \in T . val\} = n - r$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.complement_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.6 (halfDiagramEquiv).**

$$\forall (n r : \mathbb{N}) (hCard : \forall T : ThroughSets n r , Fintype . card \{x : Fin n \mid x \neg \in T . val\} = Fintype . card (Fin (n - r))) , let e : \forall T : ThroughSets n r , \{x : Fin n \mid x \neg \in T . val\} \equiv Fin (n - r) := \lambda T \mapsto Fintype . equivOfCardEq (hCard T) ; \forall (hForward : \forall (T : ThroughSets n r) (q : FixedPointFreeInvolution \{x : Fin n \mid x \neg \in T . val\}) , Function . Involutive (((e T) . symm . trans q . val) . trans (e T)) \land \forall x , (((e T) . symm . trans q . val) . trans (e T)) x \neq x) (hBackward : \forall (T : ThroughSets n r) (q : FixedPointFreeInvolution (Fin (n - r))) , Function . Involutive (((e T) . trans q . val) . trans (e T) . symm) \land \forall x , (((e T) . trans q . val) . trans (e T) . symm) x \neq x) , let forward : \forall T : ThroughSets n r , FixedPointFreeInvolution \{x : Fin n \mid x \neg \in T . val\} \to FixedPointFreeInvolution (Fin (n - r)) := \lambda T q \mapsto \langle ((e T) . symm . trans q . val) . trans (e T) , hForward T q \rangle ; let backward : \forall T : ThroughSets n r , FixedPointFreeInvolution (Fin (n - r)) \to FixedPointFreeInvolution \{x : Fin n \mid x \neg \in T . val\} := \lambda T q \mapsto \langle ((e T) . trans q . val) . trans (e T) . symm , hBackward T q \rangle ; \forall (hLeft : \forall T : ThroughSets n r , Function . LeftInverse (backward T) (forward T)) (hRight : \forall T : ThroughSets n r , Function . RightInverse (backward T) (forward T)) , halfDiagramEquiv n r = (Equiv . sigmaCongrRight (\lambda T \mapsto Equiv . mk (forward T) (backward T) (hLeft T) (hRight T))) . trans (Equiv . sigmaEquivProd (ThroughSets n r) (FixedPointFreeInvolution (Fin (n - r))))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.halfDiagramEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.7 (ThroughCompatible).**

$$\forall \{n r : \mathbb{N}\} , \forall (T U : ThroughSets n r) , ThroughCompatible T U = (T . val = U . val \lor (Finset . inter T . val U . val) . card + 1 = r)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.ThroughCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.8 (half_diagram_supported_triangle_structure).**

$$\forall \{n r : \mathbb{N}\} , \forall \{tri : Finset (Finset (Fin n))\} , (SubsetPairing (Fin n) r tri) \to ((tri . card = 3) \to ((\forall T \in tri , T . card = r) \to ((Even (n - r)) \to ((\forall T \in tri , \forall U \in tri , T = U \lor (Finset . inter T U) . card + 1 = r) \to (\exists w : OneTrianglePermutation (HalfDiagram n r) , (\forall D , ThroughCompatible D . 1 (w . perm D) . 1) \land (\forall D \in w . triangle , D . 1 . val \in tri) \land (\forall D \in w . triangle , \forall E \in w . triangle , D . 1 = E . 1 \to D = E))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.half_diagram_supported_triangle_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.9 (triangle_image_adjacent).**

$$\forall \{n m r : \mathbb{N}\} , \forall (tri : Finset (Finset (Fin n))) , \forall (e : Function . Embedding (Fin n) (Fin m)) , (\forall T \in tri , \forall U \in tri , T = U \lor (Finset . inter T U) . card + 1 = r) \to (\forall T \in tri . image (\lambda s \mapsto s . map e) , \forall U \in tri . image (\lambda s \mapsto s . map e) , T = U \lor (Finset . inter T U) . card + 1 = r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.triangle_image_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.10 (baseTwo_triangle_data).**

$$baseTwoTriangle . card = 3 \land (\forall T \in baseTwoTriangle , T . card = 2) \land (\forall T \in baseTwoTriangle , \forall U \in baseTwoTriangle , T = U \lor (Finset . inter T U) . card + 1 = 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.baseTwo_triangle_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.11 (baseThree_triangle_data).**

$$baseThreeTriangle . card = 3 \land (\forall T \in baseThreeTriangle , T . card = 3) \land (\forall T \in baseThreeTriangle , \forall U \in baseThreeTriangle , T = U \lor (Finset . inter T U) . card + 1 = 3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.baseThree_triangle_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.12 (triangle_image_card_rank).**

$$\forall \{n m r : \mathbb{N}\} , \forall (tri : Finset (Finset (Fin n))) , \forall (e : Function . Embedding (Fin n) (Fin m)) , (tri . card = 3) \to ((\forall T \in tri , T . card = r) \to ((tri . image (\lambda s \mapsto s . map e)) . card = 3 \land \forall T \in tri . image (\lambda s \mapsto s . map e) , T . card = r))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.triangle_image_card_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.HalfDiagram`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.OneTrianglePermutation`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.ThroughCompatible`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.ThroughSets`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.baseThree_triangle_data`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.baseTwo_triangle_data`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.card_matching_fibre_odd`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.complement_card`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.halfDiagramEquiv`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.half_diagram_supported_triangle_structure`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.triangle_image_adjacent`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles.triangle_image_card_rank`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids](AraujoBrauerSourceMonoids.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSubsetPairing](AraujoBrauerSubsetPairing.md)
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](../../Zeros/Convolution/PerfectMatchingCount.md)
