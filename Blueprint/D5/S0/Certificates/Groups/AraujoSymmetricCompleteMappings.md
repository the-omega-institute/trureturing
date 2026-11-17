# AraujoSymmetricCompleteMappings

## Abstract

Constructive results for complete mappings of diagram monoids.

**Theorem 1.1 (complete_mapping_of_idempotent).**

$$\forall \{S : Type\} , \forall [Semigroup S] , (\forall x : S , x * x = x) \to (CompleteMapping (id : S \to S))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.complete_mapping_of_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.2 (complete_mapping_transport).**

$$\forall \{S T : Type\} , \forall [Semigroup S] , \forall [Semigroup T] , \forall (e : S \equiv* T) , \forall \{a : S \to S\} , (CompleteMapping a) \to (CompleteMapping (\lambda y : T \mapsto e (a (e . symm y))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.complete_mapping_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.3 (symmetric_two_no_complete).**

$$\neg \exists a : Equiv . Perm (Fin 2) \to Equiv . Perm (Fin 2) , CompleteMapping a$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.symmetric_two_no_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.4 (symmetric_three_no_complete).**

$$\neg \exists a : Equiv . Perm (Fin 3) \to Equiv . Perm (Fin 3) , CompleteMapping a$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.symmetric_three_no_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.5 (complete_mapping_restrict_units).**

$$\forall \{M : Type\} , \forall [Monoid M] , \forall [Finite M] , \forall \{a : M \to M\} , (CompleteMapping a) \to (\exists aU : M ^{\times} \to M ^{\times} , CompleteMapping aU)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.complete_mapping_restrict_units` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Theorem 1.6 (symmetric_small_or_large).**

$$\forall (r : \mathbb{N}) , (r \neq 2 \land r \neq 3) \to (\exists a : Equiv . Perm (Fin r) \to Equiv . Perm (Fin r) , CompleteMapping a)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.symmetric_small_or_large` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

**Definition 1.7 (DiagonalTransversal).**

$$structure DiagonalTransversal (I G : Type) [Group G] where alpha : Equiv . Perm ((I \times G \times I)) theta : Equiv . Perm ((I \times G \times I)) alphaFirst : \forall x , (alpha x) . 1 = x . 2 . 2 thetaFirst : \forall x , (theta x) . 1 = x . 1 thetaLast : \forall x , (theta x) . 2 . 2 = (alpha x) . 2 . 2 thetaGroup : \forall x , (theta x) . 2 . 1 = x . 2 . 1 * (alpha x) . 2 . 1$$

*Formalization.* `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.DiagonalTransversal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.8 (diagonalTransversalS2).**

$$\forall (hG : \forall i : Fin 2 , Function . Bijective ((! [(! [0 , 1] : Fin 2 \to Fin 2) , (! [1 , 0] : Fin 2 \to Fin 2)] : Fin 2 \to (Fin 2 \to Fin 2)) i)) , let q := \lambda i : Fin 2 \mapsto Equiv . ofBijective ((! [(! [0 , 1] : Fin 2 \to Fin 2) , (! [1 , 0] : Fin 2 \to Fin 2)] : Fin 2 \to (Fin 2 \to Fin 2)) i) (hG i) ; let enumeration := (! [(0 , q 0 , 0) , (0 , q 0 , 1) , (0 , q 1 , 0) , (0 , q 1 , 1) , (1 , q 0 , 0) , (1 , q 0 , 1) , (1 , q 1 , 0) , (1 , q 1 , 1)] : Fin 8 \to (Fin 2 \times Equiv . Perm (Fin 2) \times Fin 2)) ; \forall (hE : Function . Bijective enumeration) (hA : Function . Bijective (! [0 , 5 , 1 , 4 , 2 , 7 , 3 , 6] : Fin 8 \to Fin 8)) (hT : Function . Bijective (! [0 , 1 , 3 , 2 , 6 , 7 , 5 , 4] : Fin 8 \to Fin 8)) , let e := Equiv . ofBijective enumeration hE ; let a := Equiv . ofBijective ! [0 , 5 , 1 , 4 , 2 , 7 , 3 , 6] hA ; let t := Equiv . ofBijective ! [0 , 1 , 3 , 2 , 6 , 7 , 5 , 4] hT ; let alpha := (e . symm . trans a) . trans e ; let theta := (e . symm . trans t) . trans e ; \forall (hAlpha : \forall x , (alpha x) . 1 = x . 2 . 2) (hFirst : \forall x , (theta x) . 1 = x . 1) (hLast : \forall x , (theta x) . 2 . 2 = (alpha x) . 2 . 2) (hGroup : \forall x , (theta x) . 2 . 1 = x . 2 . 1 * (alpha x) . 2 . 1) , diagonalTransversalS2 = DiagonalTransversal . mk alpha theta hAlpha hFirst hLast hGroup$$

*Formalization.* `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.diagonalTransversalS2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.9 (diagonalTransversalS3).**

$$\forall (hG : \forall i : Fin 6 , Function . Bijective ((! [(! [0 , 1 , 2] : Fin 3 \to Fin 3) , (! [0 , 2 , 1] : Fin 3 \to Fin 3) , (! [1 , 0 , 2] : Fin 3 \to Fin 3) , (! [1 , 2 , 0] : Fin 3 \to Fin 3) , (! [2 , 0 , 1] : Fin 3 \to Fin 3) , (! [2 , 1 , 0] : Fin 3 \to Fin 3)] : Fin 6 \to (Fin 3 \to Fin 3)) i)) , let q := \lambda i : Fin 6 \mapsto Equiv . ofBijective ((! [(! [0 , 1 , 2] : Fin 3 \to Fin 3) , (! [0 , 2 , 1] : Fin 3 \to Fin 3) , (! [1 , 0 , 2] : Fin 3 \to Fin 3) , (! [1 , 2 , 0] : Fin 3 \to Fin 3) , (! [2 , 0 , 1] : Fin 3 \to Fin 3) , (! [2 , 1 , 0] : Fin 3 \to Fin 3)] : Fin 6 \to (Fin 3 \to Fin 3)) i) (hG i) ; let enumeration := (! [(0 , q 0 , 0) , (0 , q 0 , 1) , (0 , q 1 , 0) , (0 , q 1 , 1) , (0 , q 2 , 0) , (0 , q 2 , 1) , (0 , q 3 , 0) , (0 , q 3 , 1) , (0 , q 4 , 0) , (0 , q 4 , 1) , (0 , q 5 , 0) , (0 , q 5 , 1) , (1 , q 0 , 0) , (1 , q 0 , 1) , (1 , q 1 , 0) , (1 , q 1 , 1) , (1 , q 2 , 0) , (1 , q 2 , 1) , (1 , q 3 , 0) , (1 , q 3 , 1) , (1 , q 4 , 0) , (1 , q 4 , 1) , (1 , q 5 , 0) , (1 , q 5 , 1)] : Fin 24 \to (Fin 2 \times Equiv . Perm (Fin 3) \times Fin 2)) ; \forall (hE : Function . Bijective enumeration) (hA : Function . Bijective (! [0 , 13 , 1 , 17 , 2 , 12 , 4 , 15 , 3 , 16 , 5 , 14 , 6 , 20 , 7 , 21 , 8 , 18 , 11 , 19 , 9 , 22 , 10 , 23] : Fin 24 \to Fin 24)) (hT : Function . Bijective (! [0 , 1 , 3 , 9 , 6 , 4 , 10 , 5 , 11 , 2 , 7 , 8 , 18 , 20 , 23 , 17 , 22 , 14 , 15 , 21 , 19 , 16 , 12 , 13] : Fin 24 \to Fin 24)) , let e := Equiv . ofBijective enumeration hE ; let a := Equiv . ofBijective ! [0 , 13 , 1 , 17 , 2 , 12 , 4 , 15 , 3 , 16 , 5 , 14 , 6 , 20 , 7 , 21 , 8 , 18 , 11 , 19 , 9 , 22 , 10 , 23] hA ; let t := Equiv . ofBijective ! [0 , 1 , 3 , 9 , 6 , 4 , 10 , 5 , 11 , 2 , 7 , 8 , 18 , 20 , 23 , 17 , 22 , 14 , 15 , 21 , 19 , 16 , 12 , 13] hT ; let alpha := (e . symm . trans a) . trans e ; let theta := (e . symm . trans t) . trans e ; \forall (hAlpha : \forall x , (alpha x) . 1 = x . 2 . 2) (hFirst : \forall x , (theta x) . 1 = x . 1) (hLast : \forall x , (theta x) . 2 . 2 = (alpha x) . 2 . 2) (hGroup : \forall x , (theta x) . 2 . 1 = x . 2 . 1 * (alpha x) . 2 . 1) , diagonalTransversalS3 = DiagonalTransversal . mk alpha theta hAlpha hFirst hLast hGroup$$

*Formalization.* `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.diagonalTransversalS3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.10 (diagonalTransversalFiniteGood).**

$$\forall \{I G : Type\} [Fintype I] [Nonempty I] [Group G] (a : G \to G) (ha : CompleteMapping a) [NeZero (Fintype . card I)] , let e : I \equiv Multiplicative (ZMod (Fintype . card I)) := (Fintype . equivFin I) . trans ((ZMod . finEquiv (Fintype . card I)) . toEquiv . trans Multiplicative . ofAdd) ; let ae := Equiv . ofBijective a ha . 1 ; let te := Equiv . ofBijective (\lambda g \mapsto g * a g) ha . 2 ; let af := \lambda x : (Multiplicative (ZMod (Fintype . card I)) \times G \times Multiplicative (ZMod (Fintype . card I))) \mapsto (x . 2 . 2 , ae x . 2 . 1 , x . 1 * x . 2 . 2) ; let ai := \lambda x : (Multiplicative (ZMod (Fintype . card I)) \times G \times Multiplicative (ZMod (Fintype . card I))) \mapsto (x . 2 . 2 * x . 1 ^{-1} , ae . symm x . 2 . 1 , x . 1) ; let tf := \lambda x : (Multiplicative (ZMod (Fintype . card I)) \times G \times Multiplicative (ZMod (Fintype . card I))) \mapsto (x . 1 , te x . 2 . 1 , x . 1 * x . 2 . 2) ; let ti := \lambda x : (Multiplicative (ZMod (Fintype . card I)) \times G \times Multiplicative (ZMod (Fintype . card I))) \mapsto (x . 1 , te . symm x . 2 . 1 , x . 1 ^{-1} * x . 2 . 2) ; \forall (hAL : Function . LeftInverse ai af) (hAR : Function . RightInverse ai af) (hTL : Function . LeftInverse ti tf) (hTR : Function . RightInverse ti tf) , let ac := Equiv . mk af ai hAL hAR ; let tc := Equiv . mk tf ti hTL hTR ; let change := e . symm . prodCongr ((Equiv . refl G) . prodCongr e . symm) ; let alpha := (change . symm . trans ac) . trans change ; let theta := (change . symm . trans tc) . trans change ; \forall (hAlpha : \forall x , (alpha x) . 1 = x . 2 . 2) (hFirst : \forall x , (theta x) . 1 = x . 1) (hLast : \forall x , (theta x) . 2 . 2 = (alpha x) . 2 . 2) (hGroup : \forall x , (theta x) . 2 . 1 = x . 2 . 1 * (alpha x) . 2 . 1) , diagonalTransversalFiniteGood a ha = DiagonalTransversal . mk alpha theta hAlpha hFirst hLast hGroup$$

*Formalization.* `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.diagonalTransversalFiniteGood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.11 (diagonalTransversalFiniteEven).**

$$\forall \{I G : Type\} [Fintype I] [Nonempty I] [Group G] (he : Even (Fintype . card I)) (base : DiagonalTransversal (Fin 2) G) , let m := Classical . choose he ; \forall (hn : m \neq 0) , letI : NeZero m := \langle hn \rangle ; let splitForward := \lambda x : ((Fin 2 \times Multiplicative (ZMod m)) \times G \times (Fin 2 \times Multiplicative (ZMod m))) \mapsto ((x . 1 . 1 , x . 2 . 1 , x . 2 . 2 . 1) , x . 1 . 2 , x . 2 . 2 . 2) ; let splitBackward := \lambda x : ((Fin 2 \times G \times Fin 2) \times (Multiplicative (ZMod m) \times Multiplicative (ZMod m))) \mapsto ((x . 1 . 1 , x . 2 . 1) , x . 1 . 2 . 1 , (x . 1 . 2 . 2 , x . 2 . 2)) ; let af := \lambda x : (Multiplicative (ZMod m) \times Multiplicative (ZMod m)) \mapsto (x . 2 , x . 1 * x . 2) ; let ai := \lambda x : (Multiplicative (ZMod m) \times Multiplicative (ZMod m)) \mapsto (x . 2 * x . 1 ^{-1} , x . 1) ; let tf := \lambda x : (Multiplicative (ZMod m) \times Multiplicative (ZMod m)) \mapsto (x . 1 , x . 1 * x . 2) ; let ti := \lambda x : (Multiplicative (ZMod m) \times Multiplicative (ZMod m)) \mapsto (x . 1 , x . 1 ^{-1} * x . 2) ; \forall (hSL : Function . LeftInverse splitBackward splitForward) (hSR : Function . RightInverse splitBackward splitForward) (hAL : Function . LeftInverse ai af) (hAR : Function . RightInverse ai af) (hTL : Function . LeftInverse ti tf) (hTR : Function . RightInverse ti tf) (hCard : Fintype . card (Fin 2 \times Multiplicative (ZMod m)) = Fintype . card I) , let split := Equiv . mk splitForward splitBackward hSL hSR ; let ac := Equiv . mk af ai hAL hAR ; let tc := Equiv . mk tf ti hTL hTR ; let productAlpha := (split . trans (base . alpha . prodCongr ac)) . trans split . symm ; let productTheta := (split . trans (base . theta . prodCongr tc)) . trans split . symm ; let e : (Fin 2 \times Multiplicative (ZMod m)) \equiv I := Fintype . equivOfCardEq hCard ; let change := e . prodCongr ((Equiv . refl G) . prodCongr e) ; let alpha := (change . symm . trans productAlpha) . trans change ; let theta := (change . symm . trans productTheta) . trans change ; \forall (hAlpha : \forall x , (alpha x) . 1 = x . 2 . 2) (hFirst : \forall x , (theta x) . 1 = x . 1) (hLast : \forall x , (theta x) . 2 . 2 = (alpha x) . 2 . 2) (hGroup : \forall x , (theta x) . 2 . 1 = x . 2 . 1 * (alpha x) . 2 . 1) , diagonalTransversalFiniteEven he base = DiagonalTransversal . mk alpha theta hAlpha hFirst hLast hGroup$$

*Formalization.* `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.diagonalTransversalFiniteEven` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.12 (reesProduct).**

$$\forall \{I G : Type\} , \forall [Group G] , \forall (P : I \to I \to Option G) , \forall (x y : (I \times G \times I)) , reesProduct P x y = ((P x . 2 . 2 y . 1) . map (\lambda p \mapsto (x . 1 , x . 2 . 1 * p * y . 2 . 1 , y . 2 . 2)))$$

*Formalization.* `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.reesProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Definition 1.13 (ReesTransversal).**

$$structure ReesTransversal \{I G : Type\} [Group G] (P : I \to I \to Option G) where alpha : Equiv . Perm ((I \times G \times I)) theta : Equiv . Perm ((I \times G \times I)) product : \forall x , reesProduct P x (alpha x) = some (theta x)$$

*Formalization.* `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.ReesTransversal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified defining expression.

**Theorem 1.14 (diagonalTransversal_rees).**

$$\forall \{I G : Type\} , \forall [Group G] , \forall (P : I \to I \to Option G) , (\forall i , P i i = some 1) \to ((DiagonalTransversal I G) \to (Nonempty (ReesTransversal P)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.diagonalTransversal_rees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula gives the quantified statement.

## References

- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.DiagonalTransversal`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.ReesTransversal`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.complete_mapping_of_idempotent`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.complete_mapping_restrict_units`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.complete_mapping_transport`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.diagonalTransversalFiniteEven`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.diagonalTransversalFiniteGood`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.diagonalTransversalS2`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.diagonalTransversalS3`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.diagonalTransversal_rees`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.reesProduct`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.symmetric_small_or_large`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.symmetric_three_no_complete`
- Truth anchor: `D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.symmetric_two_no_complete`
- Dependency: [D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation](../AraujoOrthodoxCompleteMappingRefutation.md)
