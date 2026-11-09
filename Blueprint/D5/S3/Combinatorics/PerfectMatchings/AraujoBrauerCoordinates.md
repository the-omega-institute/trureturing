# AraujoBrauerCoordinates

## Abstract

Constructive results for complete mappings of diagram monoids.

**Definition 1.1 (MarkedHalf).**

$$structure MarkedHalf (X : Type) where through : Set X mate : Equiv . Perm X involutive : Function . Involutive mate fixes : \forall x \in through , mate x = x$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.MarkedHalf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.2 (DiagramCoordinates).**

$$structure DiagramCoordinates (X : Type) where upper : MarkedHalf X lower : MarkedHalf X transport : upper . through \equiv lower . through$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.DiagramCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.3 (half_mate_mem).**

$$\forall \{X : Type\} , \forall (H : MarkedHalf X) , \forall (x : X) , H . mate x \in H . through \iff x \in H . through$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.half_mate_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.4 (coordinateMate).**

$$\forall \{X : Type\} (d : DiagramCoordinates X) , coordinateMate d = (\lambda | (false , x) \mapsto if h : x \in d . upper . through then (true , (d . transport \langle x , h \rangle) . val) else (false , d . upper . mate x) | (true , x) \mapsto if h : x \in d . lower . through then (false , (d . transport . symm \langle x , h \rangle) . val) else (true , d . lower . mate x))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinateMate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.5 (coordinateMateInvolutive).**

$$\forall \{X : Type\} , \forall (d : DiagramCoordinates X) , Function . Involutive (coordinateMate d)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinateMateInvolutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.6 (coordinatePerm).**

$$\forall \{X : Type\} , \forall (d : DiagramCoordinates X) , coordinatePerm d = Function.Involutive.toPerm (coordinateMate d) (coordinateMateInvolutive d)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinatePerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.7 (coordinatePerm_apply).**

$$\forall \{X : Type\} , \forall (d : DiagramCoordinates X) , \forall (v : Bool \times X) , coordinatePerm d v = coordinateMate d v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinatePerm_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.8 (markedHalf_ext).**

$$\forall \{X : Type\} , \forall \{A B : MarkedHalf X\} , (A . through = B . through) \to ((A . mate = B . mate) \to (A = B))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.markedHalf_ext` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.9 (coordinatePerm_injective).**

$$\forall \{X : Type\} , Function . Injective (coordinatePerm : DiagramCoordinates X \to Equiv . Perm (Bool \times X))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinatePerm_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.10 (partialBrauerCoordinateEquiv).**

$$\forall (n : \mathbb{N}) (h : Function . Bijective (\lambda d : DiagramCoordinates (Fin n) \mapsto (\langle coordinatePerm d , coordinateMateInvolutive d \rangle : \{p : Equiv . Perm (Bool \times Fin n) \mid Function . Involutive p\}))) , partialBrauerCoordinateEquiv n = (Equiv . ofBijective (\lambda d : DiagramCoordinates (Fin n) \mapsto (\langle coordinatePerm d , coordinateMateInvolutive d \rangle : \{p : Equiv . Perm (Bool \times Fin n) \mid Function . Involutive p\})) h) . trans (partialPartitionEquivInvolution (Bool \times Fin n))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.partialBrauerCoordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.11 (diagramRank).**

$$\forall \{X : Type\} , \forall [Finite X] , \forall (d : DiagramCoordinates X) , diagramRank d = (Nat . card d . upper . through)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.diagramRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.12 (diagramRank_lower).**

$$\forall \{X : Type\} , \forall [Finite X] , \forall (d : DiagramCoordinates X) , diagramRank d = Nat . card d . lower . through$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.diagramRank_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.13 (partialBrauerRank).**

$$\forall \{n : \mathbb{N}\} , \forall (d : PartialBrauer n) , partialBrauerRank d = (diagramRank ((partialBrauerCoordinateEquiv n) . symm d))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.partialBrauerRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.14 (BrauerCoordinates).**

$$\forall (n : \mathbb{N}) , BrauerCoordinates n = (\{d : DiagramCoordinates (Fin n) \mid \forall v , coordinatePerm d v \neq v\})$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.BrauerCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.15 (coordinate_fixed_point_free_iff).**

$$\forall \{X : Type\} , \forall (d : DiagramCoordinates X) , (\forall v , coordinatePerm d v \neq v) \iff (\forall x \neg \in d . upper . through , d . upper . mate x \neq x) \land (\forall x \neg \in d . lower . through , d . lower . mate x \neq x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinate_fixed_point_free_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.16 (brauerCoordinateEquiv).**

$$\forall (n : \mathbb{N}) (h : Function . Bijective (\lambda d : BrauerCoordinates n \mapsto brauerOfMatching (coordinatePerm d . val) (coordinateMateInvolutive d . val) d . property)) , brauerCoordinateEquiv n = Equiv . ofBijective (\lambda d : BrauerCoordinates n \mapsto brauerOfMatching (coordinatePerm d . val) (coordinateMateInvolutive d . val) d . property) h$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.brauerCoordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.17 (brauerRank).**

$$\forall \{n : \mathbb{N}\} , \forall (a : Brauer n) , brauerRank a = (diagramRank ((brauerCoordinateEquiv n) . symm a) . val)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.brauerRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.18 (RankedHalf).**

$$\forall (X : Type) , \forall [Finite X] , \forall (r : \mathbb{N}) , RankedHalf X r = (\{H : MarkedHalf X \mid Nat . card H . through = r\})$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.RankedHalf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.19 (rankedLabels).**

$$\forall \{X : Type\} [Finite X] \{r : \mathbb{N}\} (A : RankedHalf X r) , (letI : Fintype A . val . through := Fintype . ofFinite A . val . through ; \forall (h : Fintype . card A . val . through = r) , rankedLabels A = Fintype . equivFinOfCardEq h)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.rankedLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.20 (rankedDiagram).**

$$\forall \{X : Type\} [Finite X] \{r : \mathbb{N}\} (A : RankedHalf X r) (g : Equiv . Perm (Fin r)) (D : RankedHalf X r) , rankedDiagram A g D = DiagramCoordinates . mk A . val D . val (((rankedLabels A) . trans g . symm) . trans (rankedLabels D) . symm)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.rankedDiagram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.21 (rankedDiagram_rank).**

$$\forall \{X : Type\} , \forall [Finite X] , \forall \{r : \mathbb{N}\} , \forall (A : RankedHalf X r) , \forall (g : Equiv . Perm (Fin r)) , \forall (D : RankedHalf X r) , diagramRank (rankedDiagram A g D) = r$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.rankedDiagram_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.22 (rankedCoordinatesEquiv).**

$$\forall (X : Type) [Finite X] (r : \mathbb{N}) (hRank : \forall (A : RankedHalf X r) (g : Equiv . Perm (Fin r)) (D : RankedHalf X r) , diagramRank (rankedDiagram A g D) = r) (hLower : \forall d : DiagramCoordinates X , Nat . card d . lower . through = diagramRank d) , let f : (RankedHalf X r \times Equiv . Perm (Fin r) \times RankedHalf X r) \to \{d : DiagramCoordinates X \mid diagramRank d = r\} := \lambda a \mapsto \langle rankedDiagram a . 1 a . 2 . 1 a . 2 . 2 , hRank a . 1 a . 2 . 1 a . 2 . 2 \rangle ; let g : \{d : DiagramCoordinates X \mid diagramRank d = r\} \to (RankedHalf X r \times Equiv . Perm (Fin r) \times RankedHalf X r) := \lambda d \mapsto (\langle d . val . upper , d . property \rangle , (((rankedLabels \langle d . val . upper , d . property \rangle) . symm . trans d . val . transport) . trans (rankedLabels \langle d . val . lower , (hLower d . val) . trans d . property \rangle)) . symm , \langle d . val . lower , (hLower d . val) . trans d . property \rangle) ; \forall (hLeft : Function . LeftInverse g f) (hRight : Function . RightInverse g f) , rankedCoordinatesEquiv X r = Equiv . mk f g hLeft hRight$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.rankedCoordinatesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.23 (middleOverlay).**

$$\forall \{X : Type\} , \forall (D E : MarkedHalf X) , middleOverlay D E = (Relation . EqvGen . setoid (\lambda x y \mapsto D . mate x = y \lor E . mate x = y))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.middleOverlay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.24 (coordinateConcat).**

$$\forall \{X : Type\} (d e : DiagramCoordinates X) (w : d . lower . through \equiv e . upper . through) , coordinateConcat d e w = DiagramCoordinates . mk d . upper e . lower ((d . transport . trans w) . trans e . transport)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinateConcat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.25 (coordinate_product_preserving).**

$$\forall \{n : \mathbb{N}\} , \forall (d e : DiagramCoordinates (Fin n)) , \forall (w : d . lower . through \equiv e . upper . through) , (\forall x : d . lower . through , (middleOverlay d . lower e . upper) . r x (w x)) \to (partitionProduct (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)) (involutionSetoid (coordinatePerm e) (coordinateMateInvolutive e)) = involutionSetoid (coordinatePerm (coordinateConcat d e w)) (coordinateMateInvolutive (coordinateConcat d e w)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinate_product_preserving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.26 (coordinate_product_upper_subset).**

$$\forall \{n : \mathbb{N}\} , \forall (d e t : DiagramCoordinates (Fin n)) , (partitionProduct (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)) (involutionSetoid (coordinatePerm e) (coordinateMateInvolutive e)) = involutionSetoid (coordinatePerm t) (coordinateMateInvolutive t)) \to (t . upper . through \subseteq d . upper . through)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinate_product_upper_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.27 (coordinate_product_lower_subset).**

$$\forall \{n : \mathbb{N}\} , \forall (d e t : DiagramCoordinates (Fin n)) , (partitionProduct (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)) (involutionSetoid (coordinatePerm e) (coordinateMateInvolutive e)) = involutionSetoid (coordinatePerm t) (coordinateMateInvolutive t)) \to (t . lower . through \subseteq e . lower . through)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinate_product_lower_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.BrauerCoordinates`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.DiagramCoordinates`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.MarkedHalf`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.RankedHalf`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.brauerCoordinateEquiv`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.brauerRank`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinateConcat`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinateMate`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinateMateInvolutive`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinatePerm`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinatePerm_apply`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinatePerm_injective`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinate_fixed_point_free_iff`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinate_product_lower_subset`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinate_product_preserving`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.coordinate_product_upper_subset`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.diagramRank`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.diagramRank_lower`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.half_mate_mem`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.markedHalf_ext`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.middleOverlay`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.partialBrauerCoordinateEquiv`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.partialBrauerRank`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.rankedCoordinatesEquiv`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.rankedDiagram`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.rankedDiagram_rank`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates.rankedLabels`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids](AraujoBrauerSourceMonoids.md)
