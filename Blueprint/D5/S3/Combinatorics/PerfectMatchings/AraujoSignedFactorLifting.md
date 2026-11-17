# AraujoSignedFactorLifting

## Abstract

Constructive results for complete mappings of diagram monoids.

**Definition 1.1 (coordinatePartition).**

$$\forall \{n : \mathbb{N}\} , \forall (d : DiagramCoordinates (Fin n)) , coordinatePartition d = (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinatePartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.2 (coordinatePartition_injective).**

$$\forall \{n : \mathbb{N}\} , Function . Injective (coordinatePartition : DiagramCoordinates (Fin n) \to (Setoid (Bool \times Fin n)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinatePartition_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.3 (coordinateMul).**

$$\forall \{n : \mathbb{N}\} , \forall (d e : DiagramCoordinates (Fin n)) , coordinateMul d e = ((partialBrauerCoordinateEquiv n) . symm \langle partitionProduct (coordinatePartition d) (coordinatePartition e) , partitionProductPartialClosed \langle coordinatePartition d , involutionSetoidBlockLeTwo (coordinatePerm d) (coordinateMateInvolutive d) \rangle \langle coordinatePartition e , involutionSetoidBlockLeTwo (coordinatePerm e) (coordinateMateInvolutive e) \rangle \rangle)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinateMul` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.4 (coordinateMul_spec).**

$$\forall \{n : \mathbb{N}\} , \forall (d e : DiagramCoordinates (Fin n)) , partitionProduct (coordinatePartition d) (coordinatePartition e) = coordinatePartition (coordinateMul d e)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinateMul_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.5 (rankedDiagram_mul).**

$$\forall \{n r : \mathbb{N}\} , \forall (A D E : RankedHalf (Fin n) r) , \forall (g h : Equiv . Perm (Fin r)) , coordinateMul (rankedDiagram A g D) (rankedDiagram D h E) = rankedDiagram A (g * h) E$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.rankedDiagram_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.6 (rankedDiagram_group_injective).**

$$\forall \{n r : \mathbb{N}\} , \forall (A D : RankedHalf (Fin n) r) , Function . Injective (\lambda g : Equiv . Perm (Fin r) \mapsto rankedDiagram A g D)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.rankedDiagram_group_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.7 (coordinateSandwich).**

$$\forall \{n r : \mathbb{N}\} (O D E : RankedHalf (Fin n) r) , coordinateSandwich O D E = (if h : \exists p : Equiv . Perm (Fin r) , coordinateMul (rankedDiagram O 1 D) (rankedDiagram E 1 O) = rankedDiagram O p O then some (Classical . choose h) else none)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinateSandwich` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.8 (coordinateSandwich_diagonal).**

$$\forall \{n r : \mathbb{N}\} , \forall (O D : RankedHalf (Fin n) r) , coordinateSandwich O D D = some 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinateSandwich_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.9 (coordinateSandwich_product).**

$$\forall \{n r : \mathbb{N}\} , \forall (O A D E F : RankedHalf (Fin n) r) , \forall (g h p : Equiv . Perm (Fin r)) , (coordinateSandwich O D E = some p) \to (coordinateMul (rankedDiagram A g D) (rankedDiagram E h F) = rankedDiagram A (g * p * h) F)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinateSandwich_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.10 (partialBrauerRankEquiv).**

$$\forall (n r : \mathbb{N}) (h : \forall d : DiagramCoordinates (Fin n) , diagramRank d = r \iff partialBrauerRank (partialBrauerCoordinateEquiv n d) = r) , partialBrauerRankEquiv n r = (rankedCoordinatesEquiv (Fin n) r) . trans ((partialBrauerCoordinateEquiv n) . subtypeEquiv h)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.partialBrauerRankEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.11 (brauerRankHalfDiagramEquiv).**

$$\forall (n r : \mathbb{N}) , let GoodHalf := \{H : MarkedHalf (Fin n) \mid Nat . card H . through = r \land \forall x \neg \in H . through , H . mate x \neq x\} ; \forall (hNoExtra : \forall (D : HalfDiagram n r) (x : Fin n) , x \neg \in (halfRanked D) . val . through \to (halfRanked D) . val . mate x \neq x) , let halfForward : HalfDiagram n r \to GoodHalf := \lambda D \mapsto \langle (halfRanked D) . val , (halfRanked D) . property , hNoExtra D \rangle ; \forall (hHalf : Function . Bijective halfForward) , let halfEquiv := Equiv . ofBijective halfForward hHalf ; let GoodTriple := \{v : RankedHalf (Fin n) r \times Equiv . Perm (Fin r) \times RankedHalf (Fin n) r \mid (\forall x \neg \in v . 1 . val . through , v . 1 . val . mate x \neq x) \land (\forall x \neg \in v . 2 . 2 . val . through , v . 2 . 2 . val . mate x \neq x)\} ; let tripleForward : (GoodHalf \times Equiv . Perm (Fin r) \times GoodHalf) \to GoodTriple := \lambda v \mapsto \langle (\langle v . 1 . val , v . 1 . property . 1 \rangle , v . 2 . 1 , \langle v . 2 . 2 . val , v . 2 . 2 . property . 1 \rangle) , v . 1 . property . 2 , v . 2 . 2 . property . 2 \rangle ; let tripleBackward : GoodTriple \to (GoodHalf \times Equiv . Perm (Fin r) \times GoodHalf) := \lambda v \mapsto (\langle v . val . 1 . val , v . val . 1 . property , v . property . 1 \rangle , v . val . 2 . 1 , \langle v . val . 2 . 2 . val , v . val . 2 . 2 . property , v . property . 2 \rangle) ; \forall (hTL : Function . LeftInverse tripleBackward tripleForward) (hTR : Function . RightInverse tripleBackward tripleForward) , let tripleEquiv := Equiv . mk tripleForward tripleBackward hTL hTR ; \forall (hPerfect : \forall v : (RankedHalf (Fin n) r \times Equiv . Perm (Fin r) \times RankedHalf (Fin n) r) , ((\forall x \neg \in v . 1 . val . through , v . 1 . val . mate x \neq x) \land (\forall x \neg \in v . 2 . 2 . val . through , v . 2 . 2 . val . mate x \neq x)) \iff (\forall z , coordinatePerm ((rankedCoordinatesEquiv (Fin n) r v) . val) z \neq z)) , let perfectEquiv := (rankedCoordinatesEquiv (Fin n) r) . subtypeEquiv hPerfect ; let swapForward : \{d : \{d : DiagramCoordinates (Fin n) \mid diagramRank d = r\} \mid \forall z , coordinatePerm d . val z \neq z\} \to \{d : BrauerCoordinates n \mid diagramRank d . val = r\} := \lambda d \mapsto \langle \langle d . val . val , d . property \rangle , d . val . property \rangle ; let swapBackward : \{d : BrauerCoordinates n \mid diagramRank d . val = r\} \to \{d : \{d : DiagramCoordinates (Fin n) \mid diagramRank d = r\} \mid \forall z , coordinatePerm d . val z \neq z\} := \lambda d \mapsto \langle \langle d . val . val , d . property \rangle , d . val . property \rangle ; \forall (hSL : Function . LeftInverse swapBackward swapForward) (hSR : Function . RightInverse swapBackward swapForward) (hRank : \forall d : BrauerCoordinates n , diagramRank d . val = r \iff brauerRank (brauerCoordinateEquiv n d) = r) , let swapEquiv := Equiv . mk swapForward swapBackward hSL hSR ; brauerRankHalfDiagramEquiv n r = (Equiv . prodCongr halfEquiv (Equiv . prodCongr (Equiv . refl (Equiv . Perm (Fin r))) halfEquiv)) . trans (tripleEquiv . trans (perfectEquiv . trans (swapEquiv . trans ((brauerCoordinateEquiv n) . subtypeEquiv hRank))))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.brauerRankHalfDiagramEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.12 (halfRanked).**

$$\forall \{n r : \mathbb{N}\} (D : HalfDiagram n r) (h : Nat . card \{x : Fin n \mid x \in D . 1 . val\} = r) , halfRanked D = (\langle MarkedHalf . mk \{x | x \in D . 1 . val\} (halfPermutation D) (halfPermutationInvolutive D) (\lambda x hx \mapsto (halfPermutationFixed D x) . mpr hx) , h \rangle : RankedHalf (Fin n) r)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.halfRanked` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.13 (halfMatrix).**

$$\forall \{n r : \mathbb{N}\} , \forall (O : RankedHalf (Fin n) r) , halfMatrix O = (\lambda D E \mapsto coordinateSandwich O (halfRanked D) (halfRanked E))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.halfMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.14 (rank_two_signed_factor).**

$$\forall (k : \mathbb{N}) , \forall (O : RankedHalf (Fin (6 + 4 * k)) 2) , Nonempty (ReesTransversal (halfMatrix O))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.rank_two_signed_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.15 (rank_three_signed_factor).**

$$\forall (k : \mathbb{N}) , \forall (O : RankedHalf (Fin (7 + 4 * k)) 3) , Nonempty (ReesTransversal (halfMatrix O))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.rank_three_signed_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.brauerRankHalfDiagramEquiv`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinateMul`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinateMul_spec`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinatePartition`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinatePartition_injective`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinateSandwich`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinateSandwich_diagonal`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.coordinateSandwich_product`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.halfMatrix`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.halfRanked`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.partialBrauerRankEquiv`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.rank_three_signed_factor`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.rank_two_signed_factor`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.rankedDiagram_group_injective`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting.rankedDiagram_mul`
- Dependency: [D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings](../../../S0/Certificates/Groups/AraujoSymmetricCompleteMappings.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates](AraujoBrauerCoordinates.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles](AraujoBrauerHalfTriangles.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport](AraujoBrauerOverlayTransport.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids](AraujoBrauerSourceMonoids.md)
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](../../Zeros/Convolution/PerfectMatchingCount.md)
