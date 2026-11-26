/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/OddGaussSum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/OddGaussSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The odd-slot Barnes–Wall spectator pairing gives a positive Gauss sum. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TailPauliPairing
import D5.S3.VertexAlgebra.TwistedGround.BinaryGauss
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TracePolarization
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorLift

/-!
The even word labels split by a spectator bit. In the polarization of the
quaternion trace exponent, the sum of the two preimages pairs against
the second even word by the complement rule. This module evaluates the
Gauss sum of the resulting cross term at every odd slot count.

The scaled tensor rows supply the half-Gram form. The prescribed Pauli
word lifts and the explicit displacement sections identify their phase
exponent with the cross term in every odd slot count at least five.
-/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddGaussSum

open LatticeTwistedGroundRealization (sign_sum)
open LatticeTwistedGroundRealization.SignQuotient (F₂ complexSign)
open TailPauliPairing (Word parity parity_flip complement pairing)

local notation "wordFlip" => TailPauliPairing.flip

noncomputable section

variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- Even word labels with the spectator slot fixed. -/
abbrev Half (t : ι) (b : Bool) := {u : Word ι // parity u = 0 ∧ u t = b}

omit [Fintype ι] in
private theorem complement_flip (u : Word ι) (r : ι) :
    complement (wordFlip u r) = wordFlip (complement u) r := by
  funext q
  by_cases hq : q = r <;> simp [complement, TailPauliPairing.flip, hq]

omit [Fintype ι] in
private theorem flip_twice (u : Word ι) (r : ι) : wordFlip (wordFlip u r) r = u := by
  funext q
  by_cases hq : q = r <;> simp [TailPauliPairing.flip, hq]

omit [Fintype ι] in
private theorem complement_flip_twice (u : Word ι) (r : ι) :
    complement (wordFlip (complement (wordFlip u r)) r) = u := by
  rw [← complement_flip (wordFlip u r) r, flip_twice]
  funext q
  simp [complement]

omit [LinearOrder ι] in
private theorem parity_complement_add (u : Word ι) :
    parity (complement u) + parity u = (Fintype.card ι : F₂) := by
  unfold parity
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _ : ι, (1 : F₂) := by
      apply Finset.sum_congr rfl
      intro q _
      cases h : u q <;> simp [complement, h]
    _ = _ := by simp

private theorem complement_flip_even (r : ι) (hodd : (Fintype.card ι : F₂) = 1)
    (u : Word ι) (hu : parity u = 0) : parity (complement (wordFlip u r)) = 0 := by
  apply add_right_cancel (b := (1 : F₂))
  simpa only [parity_flip, hu, zero_add] using
    (parity_complement_add (wordFlip u r)).trans hodd

private def complementFlip (r t : ι) (htr : t ≠ r)
    (hodd : (Fintype.card ι : F₂) = 1) (b : Bool) (u : Half t b) : Half t (!b) :=
  ⟨complement (wordFlip u.val r), complement_flip_even r hodd u.val u.property.1,
    by simp [complement, TailPauliPairing.flip, htr, u.property.2]⟩

/-- The main cross-pairing entry takes the slot-two bit flip and then complements
all bits. The same operation runs the permutation in the opposite direction. -/
def complementPermutation (r₂ t : ι) (ht₂ : t ≠ r₂)
    (hodd : (Fintype.card ι : F₂) = 1) : Half t false ≃ Half t true where
  toFun := complementFlip r₂ t ht₂ hodd false
  invFun := complementFlip r₂ t ht₂ hodd true
  left_inv u := Subtype.ext (complement_flip_twice u.val r₂)
  right_inv u := Subtype.ext (complement_flip_twice u.val r₂)

/-- The extra cross-pairing entry, read through the same permutation. -/
def doubleFlip (r₁ r₂ t : ι) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (u : Half t false) : Half t false :=
  ⟨wordFlip (wordFlip u.val r₁) r₂, by
    rw [parity_flip, parity_flip, u.property.1, zero_add, CharTwo.add_self_eq_zero],
    by simp [TailPauliPairing.flip, ht₁, ht₂, u.property.2]⟩

private theorem doubleFlip_first_bit (r₁ r₂ t : ι) (h₁₂ : r₁ ≠ r₂)
    (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂) (u : Half t false) :
    (doubleFlip r₁ r₂ t ht₁ ht₂ u).val r₁ = !(u.val r₁) := by
  simp [doubleFlip, TailPauliPairing.flip, h₁₂]

/-- The row indexed by `u` pairs the preimage sum
`e_(wordFlip u r₂) + [u r₁ = true] e_(wordFlip u r₁)` against `v`. -/
def preimagePairing (r₁ r₂ : ι) (u v : Word ι) : F₂ :=
  pairing (wordFlip u r₂) v + if u r₁ then pairing (wordFlip u r₁) v else 0

theorem preimagePairing_eq_sum (r₁ r₂ : ι) (u v : Word ι) :
    preimagePairing r₁ r₂ u v =
      pairing (wordFlip u r₁) v +
        (pairing (wordFlip u r₂) v + if u r₁ then 0 else pairing (wordFlip u r₁) v) := by
  cases hu : u r₁
  · simp only [preimagePairing, hu, Bool.false_eq_true, if_false, add_zero]
    rw [add_comm (pairing (wordFlip u r₂) v) (pairing (wordFlip u r₁) v), CharTwo.add_cancel_left]
  · simp [preimagePairing, hu, add_comm]

theorem preimagePairing_same_spectator (r₁ r₂ t : ι) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (u v : Word ι) (ht : v t = u t) : preimagePairing r₁ r₂ u v = 0 := by
  have hzero (r : ι) (hr : t ≠ r) : pairing (wordFlip u r) v = 0 := by
    unfold pairing
    apply if_neg
    intro h
    have hbit := congrFun h t
    rw [ht] at hbit
    cases hu : u t <;> simp [complement, TailPauliPairing.flip, hr, hu] at hbit
  rw [preimagePairing, hzero r₁ ht₁, hzero r₂ ht₂]
  simp

/-- The false-to-true spectator block of the preimage pairing. -/
def crossPairing (r₁ r₂ t : ι) : Matrix (Half t false) (Half t true) F₂ :=
  fun u v => preimagePairing r₁ r₂ u.val v.val

/-- The additional matrix entry is active only on the slot-one-true rows. -/
def shearPart (r₁ r₂ t : ι) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂) :
    (Half t false → F₂) →ₗ[F₂] (Half t false → F₂) where
  toFun y u := if u.val r₁ then y (doubleFlip r₁ r₂ t ht₁ ht₂ u) else 0
  map_add' y z := by
    funext u
    cases h : u.val r₁ <;> simp [h]
  map_smul' c y := by
    funext u
    cases h : u.val r₁ <;> simp [h]

theorem shearPart_square_zero (r₁ r₂ t : ι) (h₁₂ : r₁ ≠ r₂)
    (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂) (y : Half t false → F₂) :
    shearPart r₁ r₂ t ht₁ ht₂ (shearPart r₁ r₂ t ht₁ ht₂ y) = 0 := by
  funext u
  cases h : u.val r₁ <;>
    simp [shearPart, h, doubleFlip_first_bit r₁ r₂ t h₁₂ ht₁ ht₂]

private def shearEquiv (r₁ r₂ t : ι) (h₁₂ : r₁ ≠ r₂) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂) :
    (Half t false → F₂) ≃ₗ[F₂] (Half t false → F₂) :=
  LinearEquiv.ofInvolutive (LinearMap.id + shearPart r₁ r₂ t ht₁ ht₂) (by
    intro y
    simp only [LinearMap.add_apply, LinearMap.id_apply, map_add,
      shearPart_square_zero r₁ r₂ t h₁₂ ht₁ ht₂ y, add_zero]
    funext u
    simp [add_assoc, CharTwo.add_self_eq_zero])

/-- Column reindexing by the complementary permutation followed by the
square-zero shear. -/
def crossToDot (r₁ r₂ t : ι) (h₁₂ : r₁ ≠ r₂) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (hodd : (Fintype.card ι : F₂) = 1) :
    (Half t true → F₂) ≃ₗ[F₂] (Half t false → F₂) :=
  (LinearEquiv.funCongrLeft F₂ F₂ (complementPermutation r₂ t ht₂ hodd)).trans
    (shearEquiv r₁ r₂ t h₁₂ ht₁ ht₂)

private theorem cross_entry (r₁ r₂ t : ι) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (hodd : (Fintype.card ι : F₂) = 1) (u : Half t false) (v : Half t true) :
    crossPairing r₁ r₂ t u v =
      (if v = complementPermutation r₂ t ht₂ hodd u then 1 else 0) +
      if u.val r₁ then
        (if v = complementPermutation r₂ t ht₂ hodd (doubleFlip r₁ r₂ t ht₁ ht₂ u)
         then 1 else 0)
      else 0 := by
  classical
  have hmain : (v.val = complement (wordFlip u.val r₂)) ↔
      v = complementPermutation r₂ t ht₂ hodd u :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hlabel :
      (complementPermutation r₂ t ht₂ hodd (doubleFlip r₁ r₂ t ht₁ ht₂ u)).val =
        complement (wordFlip u.val r₁) := by
    change complement (wordFlip (wordFlip (wordFlip u.val r₁) r₂) r₂) = _
    rw [flip_twice]
  have hextra : (v.val = complement (wordFlip u.val r₁)) ↔
      v = complementPermutation r₂ t ht₂ hodd (doubleFlip r₁ r₂ t ht₁ ht₂ u) := by
    rw [← hlabel]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp only [crossPairing, preimagePairing, pairing, hmain, hextra] <;> split_ifs <;> rfl

/-- Applying the cross matrix is the explicit change of coordinates on the
right half. In the new coordinates its pairing with the left half is dot. -/
theorem cross_mulVec (r₁ r₂ t : ι) (h₁₂ : r₁ ≠ r₂) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (hodd : (Fintype.card ι : F₂) = 1) (y : Half t true → F₂) (u : Half t false) :
    (∑ v, crossPairing r₁ r₂ t u v * y v) = crossToDot r₁ r₂ t h₁₂ ht₁ ht₂ hodd y u := by
  classical
  let e := complementPermutation r₂ t ht₂ hodd
  have heval (s : Half t false) :
      (∑ v : Half t true, (if v = e s then (1 : F₂) else 0) * y v) = y (e s) := by
    simp [ite_mul]
  have hc : crossToDot r₁ r₂ t h₁₂ ht₁ ht₂ hodd y u =
      y (e u) + if u.val r₁ then y (e (doubleFlip r₁ r₂ t ht₁ ht₂ u)) else 0 := rfl
  simp_rw [cross_entry r₁ r₂ t ht₁ ht₂ hodd]
  rw [hc]
  change (∑ v : Half t true, ((if v = e u then (1 : F₂) else 0) +
    if u.val r₁ then (if v = e (doubleFlip r₁ r₂ t ht₁ ht₂ u) then 1 else 0)
    else 0) * y v) = _
  cases h : u.val r₁ <;> simp [h, add_mul, Finset.sum_add_distrib, heval]

/-- The exponent obtained from the two spectator halves in even-word coordinates. -/
def crossExponent (r₁ r₂ t : ι) (p : (Half t false → F₂) × (Half t true → F₂)) : F₂ :=
  ∑ u, p.1 u * (∑ v, crossPairing r₁ r₂ t u v * p.2 v)

private theorem half_card (r t : ι) (hrt : r ≠ t) (b : Bool) :
    Fintype.card (Half t b) = 2 ^ (Fintype.card ι - 2) := by
  let outside := ({r, t} : Finset ι)ᶜ
  have hout (q : ι) : q ∈ outside ↔ q ≠ r ∧ q ≠ t := by simp [outside]
  let base (y : ↥outside → Bool) (q : ι) : Bool :=
    if ht : q = t then b else if hr : q = r then false else y ⟨q, (hout q).2 ⟨hr, ht⟩⟩
  let restore (y : ↥outside → Bool) : Word ι :=
    if parity (base y) = 0 then base y else wordFlip (base y) r
  have heven (y : ↥outside → Bool) : parity (restore y) = 0 := by
    by_cases h : parity (base y) = 0
    · simp [restore, h]
    · have hodd : parity (base y) = 1 :=
        (show ∀ a : F₂, a ≠ 0 → a = 1 by decide) _ h
      simpa only [restore, if_neg h, parity_flip] using (CharTwo.add_eq_zero.mpr hodd)
  have hrestore (y : ↥outside → Bool) (q : ι) (hq : q ≠ r) : restore y q = base y q := by
    by_cases h : parity (base y) = 0 <;> simp [restore, h, TailPauliPairing.flip, hq]
  let e : Half t b ≃ (↥outside → Bool) :=
    { toFun := fun u q => u.val q.val
      invFun := fun y => ⟨restore y, heven y, by
        rw [hrestore y t hrt.symm]
        simp [base]⟩
      left_inv := by
        intro u
        let y : ↥outside → Bool := fun q => u.val q.val
        apply Subtype.ext
        change restore y = u.val
        have hagree (q : ι) (hq : q ≠ r) : restore y q = u.val q := by
          rw [hrestore y q hq]
          by_cases ht : q = t
          · subst q
            simp [base, u.property.2]
          · simp [base, ht, hq, y]
        by_cases hr : restore y r = u.val r
        · funext q
          by_cases hq : q = r
          · simpa only [hq] using hr
          · exact hagree q hq
        · have hbit : restore y r = !(u.val r) := by
            cases h₁ : restore y r <;> cases h₂ : u.val r <;> simp_all
          have hflip : restore y = wordFlip u.val r := by
            funext q
            by_cases hq : q = r
            · subst q
              simpa [TailPauliPairing.flip] using hbit
            · simpa [TailPauliPairing.flip, hq] using hagree q hq
          have h := heven y
          rw [hflip, parity_flip, u.property.1, zero_add] at h
          exact (one_ne_zero h).elim
      right_inv := by
        intro y
        funext q
        change restore y q.val = y q
        obtain ⟨hr, ht⟩ := (hout q.val).mp q.property
        rw [hrestore y q.val hr]
        simp [base, hr, ht] }
  have hcard : outside.card = Fintype.card ι - 2 := by
    change (({r, t} : Finset ι)ᶜ).card = _
    rw [Finset.card_compl, Finset.card_pair hrt]
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hcard]

/-- The spectator cross exponent has positive Gauss sum `2 ^ (2 ^ (m - 2))`
for every odd slot count `m` with the three designated slots distinct. -/
theorem cross_gauss_sum (r₁ r₂ t : ι) (h₁₂ : r₁ ≠ r₂) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (hodd : (Fintype.card ι : F₂) = 1) :
    (∑ p : (Half t false → F₂) × (Half t true → F₂),
      complexSign (crossExponent r₁ r₂ t p)) = (2 : ℂ) ^ (2 ^ (Fintype.card ι - 2)) := by
  classical
  have local_sum : (∑ p : F₂ × F₂, complexSign (p.1 * p.2)) = (2 : ℂ) := by
    have h := BinaryGauss.block_sum 0 1 0 (by decide)
    have hc : ZMod.χ₈ (BinaryGauss.gram 0 1 0).det = 1 := by decide
    simpa [BinaryGauss.quadratic, show BinaryGauss.residue 0 = 0 by decide,
      show BinaryGauss.residue 1 = 1 by decide, hc] using h
  have hdot : (∑ p : (Half t false → F₂) × (Half t false → F₂),
      complexSign (∑ u, p.1 u * p.2 u)) = (2 : ℂ) ^ Fintype.card (Half t false) := by
    rw [← (Equiv.arrowProdEquivProdArrow (Half t false) (fun _ => F₂) (fun _ => F₂)).sum_comp]
    change (∑ p : Half t false → F₂ × F₂, complexSign (∑ u, (p u).1 * (p u).2)) = _
    simp_rw [sign_sum Finset.univ]
    rw [← Fintype.prod_sum (fun (_ : Half t false) (p : F₂ × F₂) => complexSign (p.1 * p.2))]
    simp [local_sum]
  rw [← half_card r₂ t ht₂.symm false]
  let e := Equiv.prodCongr (Equiv.refl (Half t false → F₂))
    (crossToDot r₁ r₂ t h₁₂ ht₁ ht₂ hodd).toEquiv
  rw [← e.sum_comp
    (fun p : (Half t false → F₂) × (Half t false → F₂) =>
      complexSign (∑ u, p.1 u * p.2 u))] at hdot
  change (∑ p : (Half t false → F₂) × (Half t true → F₂),
    complexSign (∑ u, p.1 u * crossToDot r₁ r₂ t h₁₂ ht₁ ht₂ hodd p.2 u)) = _ at hdot
  simpa only [crossExponent, cross_mulVec r₁ r₂ t h₁₂ ht₁ ht₂ hodd] using hdot

private abbrev EvenIndex (t : ι) := Half t false ⊕ Half t true

private def evenLabel (t : ι) : EvenIndex t → Word ι := Sum.elim Subtype.val Subtype.val

private theorem evenLabel_parity (t : ι) (u : EvenIndex t) : parity (evenLabel t u) = 0 := by
  cases u with
  | inl u => exact u.property.1
  | inr u => exact u.property.1

private def displacementMap (t : ι) : (EvenIndex t → F₂) →ₗ[F₂] (Word ι → F₂) :=
  (Pi.basisFun F₂ (EvenIndex t)).constr F₂ fun u => Pi.single (evenLabel t u) 1

private def preimageIMap (r₁ t : ι) : (EvenIndex t → F₂) →ₗ[F₂] (Word ι → F₂) :=
  (Pi.basisFun F₂ (EvenIndex t)).constr F₂ fun u => Pi.single (wordFlip (evenLabel t u) r₁) 1

private def preimageJMap (r₁ r₂ t : ι) : (EvenIndex t → F₂) →ₗ[F₂] (Word ι → F₂) :=
  (Pi.basisFun F₂ (EvenIndex t)).constr F₂ fun u =>
    Pi.single (wordFlip (evenLabel t u) r₂) 1 +
      if evenLabel t u r₁ then 0 else Pi.single (wordFlip (evenLabel t u) r₁) 1

/-- The Gram and lift expression on the common quaternion displacement space,
written in the two spectator-bit coordinates. -/
def traceExponent (r₁ r₂ t : ι) (H : LinearMap.BilinForm F₂ (Word ι → F₂))
    (phaseI phaseJ : (Word ι → F₂) → F₂)
    (p : (Half t false → F₂) × (Half t true → F₂)) : F₂ :=
  let x : EvenIndex t → F₂ := Sum.elim p.1 p.2
  let w := displacementMap t x
  let a := preimageIMap r₁ t x
  let b := preimageJMap r₁ r₂ t x
  phaseI a + phaseJ b + H w (a + b + w)

private def pauliMap (r : ι) (isZ : Bool) : (Word ι → F₂) →ₗ[F₂] (Word ι → F₂) :=
  (Pi.basisFun F₂ (Word ι)).constr F₂ fun u => Pi.single u 1 +
    if parity u = 1 ∧ u r = isZ then Pi.single (wordFlip u r) 1 else 0

private theorem pauliMap_single (r : ι) (isZ : Bool) (u : Word ι) :
    pauliMap r isZ (Pi.single u 1) = Pi.single u 1 +
      if parity u = 1 ∧ u r = isZ then Pi.single (wordFlip u r) 1 else 0 := by
  conv_lhs => rw [← Pi.basisFun_apply, pauliMap, Module.Basis.constr_basis]

private theorem pauliMap_even (r : ι) (isZ : Bool) (u : Word ι) (hu : parity u = 0) :
    pauliMap r isZ (Pi.single u 1) = Pi.single u 1 := by
  simp [pauliMap_single, hu]

private theorem pauliMap_flip_even (r s : ι) (isZ : Bool) (u : Word ι) (hu : parity u = 1) :
    pauliMap r isZ (Pi.single (wordFlip u s) 1) = Pi.single (wordFlip u s) 1 := by
  apply pauliMap_even
  simp [parity_flip, hu, CharTwo.add_self_eq_zero]

private def actionI (r₁ : ι) : (Word ι → F₂) →ₗ[F₂] (Word ι → F₂) :=
  (pauliMap r₁ true).comp (pauliMap r₁ false)

private def actionJ (r₁ r₂ : ι) : (Word ι → F₂) →ₗ[F₂] (Word ι → F₂) :=
  (pauliMap r₂ true).comp ((pauliMap r₂ false).comp (pauliMap r₁ false))

private theorem actionI_odd (r₁ : ι) (u : Word ι) (hu : parity u = 1) :
    actionI r₁ (Pi.single u 1) = Pi.single u 1 + Pi.single (wordFlip u r₁) 1 := by
  cases h₁ : u r₁ <;>
    simp [actionI, LinearMap.comp_apply, pauliMap_single r₁ false u,
      pauliMap_single r₁ true u, hu, h₁, pauliMap_flip_even _ _ _ _ hu, map_add]

private theorem actionJ_odd (r₁ r₂ : ι) (u : Word ι) (hu : parity u = 1) :
    actionJ r₁ r₂ (Pi.single u 1) = Pi.single u 1 + Pi.single (wordFlip u r₂) 1 +
      if u r₁ then 0 else Pi.single (wordFlip u r₁) 1 := by
  cases h₁ : u r₁ <;> cases h₂ : u r₂ <;>
    simp [actionJ, LinearMap.comp_apply, pauliMap_single r₁ false u,
      pauliMap_single r₂ false u, pauliMap_single r₂ true u, hu, h₁, h₂,
      pauliMap_flip_even _ _ _ _ hu, map_add]

private theorem actual_preimageI (r₁ t : ι) (x : EvenIndex t → F₂) :
    actionI r₁ (preimageIMap r₁ t x) = preimageIMap r₁ t x + displacementMap t x := by
  have he : (actionI r₁).comp (preimageIMap r₁ t) = preimageIMap r₁ t + displacementMap t := by
    apply (Pi.basisFun F₂ (EvenIndex t)).ext
    intro u
    simp only [LinearMap.comp_apply, LinearMap.add_apply, preimageIMap, displacementMap,
      Module.Basis.constr_basis]
    rw [actionI_odd, flip_twice]
    rw [parity_flip, evenLabel_parity, zero_add]
  exact LinearMap.congr_fun he x

private theorem actual_preimageJ (r₁ r₂ t : ι) (h₁₂ : r₁ ≠ r₂) (x : EvenIndex t → F₂) :
    actionJ r₁ r₂ (preimageJMap r₁ r₂ t x) = preimageJMap r₁ r₂ t x + displacementMap t x := by
  have he : (actionJ r₁ r₂).comp (preimageJMap r₁ r₂ t) =
      preimageJMap r₁ r₂ t + displacementMap t := by
    apply (Pi.basisFun F₂ (EvenIndex t)).ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.add_apply, preimageJMap, displacementMap,
      Module.Basis.constr_basis]
    let u := evenLabel t v
    let e (v : Word ι) : Word ι → F₂ := Pi.single v 1
    change actionJ r₁ r₂ (e (wordFlip u r₂) + (if u r₁ then 0 else e (wordFlip u r₁))) =
      (e (wordFlip u r₂) + (if u r₁ then 0 else e (wordFlip u r₁))) + e u
    have odd (r : ι) : parity (wordFlip u r) = 1 := by rw [parity_flip, evenLabel_parity, zero_add]
    have hcomm : wordFlip (wordFlip u r₂) r₁ = wordFlip (wordFlip u r₁) r₂ := by
      funext r
      by_cases a : r = r₁ <;> by_cases b : r = r₂ <;>
        simp_all [TailPauliPairing.flip, Ne.symm h₁₂]
    have hflip₂ : TailPauliPairing.flip u r₂ r₁ = u r₁ := by simp [TailPauliPairing.flip, h₁₂]
    have hflip₁ : TailPauliPairing.flip u r₁ r₁ = !(u r₁) := by simp [TailPauliPairing.flip]
    dsimp only [e]
    cases h : u r₁
    · simp only [h, Bool.false_eq_true, if_false, map_add, actionJ_odd _ _ _ (odd _),
        flip_twice, hflip₂, hflip₁, Bool.not_false, if_true, add_zero, hcomm]
      have hx : e (wordFlip (wordFlip u r₁) r₂) + e (wordFlip (wordFlip u r₁) r₂) = 0 := by
        funext v
        exact CharTwo.add_self_eq_zero (e (wordFlip (wordFlip u r₁) r₂) v)
      dsimp only [e] at hx
      linear_combination (norm := abel) hx
    · simp [h, actionJ_odd _ _ _ (odd _), flip_twice, hflip₂]
  exact LinearMap.congr_fun he x

private def SupportedOnBlock (r₁ r₂ : ι) (w : Word ι) (x : Word ι → F₂) : Prop :=
  ∀ u, x u ≠ 0 → ∀ t, t ≠ r₁ → t ≠ r₂ → u t = w t

private theorem block_single (r₁ r₂ : ι) (w u : Word ι)
    (h : ∀ t, t ≠ r₁ → t ≠ r₂ → u t = w t) :
    SupportedOnBlock r₁ r₂ w (Pi.single u 1) := by
  intro v hv t ht₁ ht₂
  by_cases hvu : v = u
  · simpa [hvu] using h t ht₁ ht₂
  · exact (hv (by simp [Pi.single_apply, hvu])).elim

private theorem block_add {r₁ r₂ : ι} {w : Word ι} {x y : Word ι → F₂}
    (hx : SupportedOnBlock r₁ r₂ w x) (hy : SupportedOnBlock r₁ r₂ w y) :
    SupportedOnBlock r₁ r₂ w (x + y) := by
  intro u hu t ht₁ ht₂
  by_cases h : x u = 0
  · exact hy u (by simpa [h] using hu) t ht₁ ht₂
  · exact hx u h t ht₁ ht₂

private theorem block_flip {r₁ r₂ r : ι} {w u : Word ι}
    (hr : r = r₁ ∨ r = r₂)
    (hu : ∀ t, t ≠ r₁ → t ≠ r₂ → u t = w t) :
    SupportedOnBlock r₁ r₂ w (Pi.single (wordFlip u r) 1) := by
  apply block_single
  intro t ht₁ ht₂
  have htr : t ≠ r := by rcases hr with rfl | rfl <;> assumption
  simpa only [TailPauliPairing.flip, if_neg htr] using hu t ht₁ ht₂

private def crossMatrix (r₁ r₂ t : ι) : Matrix (EvenIndex t) (EvenIndex t) F₂
  := fun u v => match u, v with
  | .inl u, .inr v => crossPairing r₁ r₂ t u v
  | _, _ => 0

private theorem quadratic_eq_of_polar_of_single {κ : Type} [Fintype κ] [DecidableEq κ]
    (Q : (κ → F₂) → F₂) (B : LinearMap.BilinForm F₂ (κ → F₂))
    (hpolar : ∀ x y, Q (x + y) = Q x + Q y + (B x y + B y x))
    (hbasis : ∀ i : κ, Q (Pi.single i 1) = B (Pi.single i 1) (Pi.single i 1))
    (x : κ → F₂) : Q x = B x x := by
  let D : (κ → F₂) →+ F₂ :=
    AddMonoidHom.mk' (fun x => Q x - B x x) (by
      intro x y
      rw [hpolar]
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
      abel)
  have hz (i : κ) : D (Pi.single i (x i)) = 0 := by
    rcases (show ∀ a : F₂, a = 0 ∨ a = 1 by decide) (x i) with hi | hi
    · rw [hi, Pi.single_zero, map_zero]
    · simpa [D, hi] using sub_eq_zero.mpr (hbasis i)
  have hD : D x = 0 := by
    rw [← Finset.univ_sum_single x, map_sum]
    exact Finset.sum_eq_zero fun i _ => hz i
  exact sub_eq_zero.mp hD

/-- The Gram pairing and the polar law for the two actual sections determine
all cross coefficients once the basis values vanish. -/
private theorem exponent_eq_cross_of_sections (r₁ r₂ t : ι)
    (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (H : LinearMap.BilinForm F₂ (Word ι → F₂))
    (gI gJ : (Word ι → F₂) →ₗ[F₂] (Word ι → F₂))
    (phaseI phaseJ : (Word ι → F₂) → F₂)
    (hI : ∀ x y, phaseI (x + y) = phaseI x + phaseI y + (H x y + H (gI x) (gI y)))
    (hJ : ∀ x y, phaseJ (x + y) = phaseJ x + phaseJ y + (H x y + H (gJ x) (gJ y)))
    (ha : ∀ x, gI (preimageIMap r₁ t x) = preimageIMap r₁ t x + displacementMap t x)
    (hb : ∀ x, gJ (preimageJMap r₁ r₂ t x) = preimageJMap r₁ r₂ t x + displacementMap t x)
    (hgram : ∀ u v : Word ι, parity v = 0 →
      (H + H.flip) (Pi.single u 1) (Pi.single v 1) = pairing u v)
    (heven : ∀ u v : Word ι, parity u = 0 → parity v = 0 → pairing u v = 0)
    (hvalue : ∀ u : EvenIndex t,
      let x := Pi.single u 1
      phaseI (preimageIMap r₁ t x) + phaseJ (preimageJMap r₁ r₂ t x) +
        H (displacementMap t x) (preimageIMap r₁ t x + preimageJMap r₁ r₂ t x +
          displacementMap t x) = 0)
    (p : (Half t false → F₂) × (Half t true → F₂)) :
    traceExponent r₁ r₂ t H phaseI phaseJ p = crossExponent r₁ r₂ t p := by
  classical
  let a := preimageIMap r₁ t
  let b := preimageJMap r₁ r₂ t
  let w := displacementMap t
  let Q := fun x => phaseI (a x) + phaseJ (b x) + H (w x) (a x + b x + w x)
  let P := H + H.flip
  let G := P.comp (a + b + w) w
  let B := (crossMatrix r₁ r₂ t).toBilin'
  have hpol x y : Q (x + y) = Q x + Q y + G x y :=
    trace_exponent_polarization H gI gJ a b w phaseI phaseJ ha hb hI hJ x y
  have hsym x y : G x y = G y x := by
    have hx := hpol x y
    rw [add_comm x y, hpol y x, add_comm (Q y) (Q x)] at hx
    exact (add_left_cancel hx).symm
  have hentry (u v : EvenIndex t) :
      G (Pi.single u 1) (Pi.single v 1) = preimagePairing r₁ r₂ (evenLabel t u) (evenLabel t v) := by
    rw [show G (Pi.single u 1) (Pi.single v 1) =
      P ((a + b + w) (Pi.single u 1)) (w (Pi.single v 1)) from rfl]
    have hP (i j : Word ι) (hj : parity j = 0) :
        P (Pi.single i 1) (Pi.single j 1) = pairing i j := hgram i j hj
    simp only [LinearMap.add_apply, a, b, w, displacementMap, preimageIMap, preimageJMap,
      ← Pi.basisFun_apply, Module.Basis.constr_basis]
    simp only [Pi.basisFun_apply, LinearMap.BilinForm.add_left]
    have hv := evenLabel_parity t v
    have hu := evenLabel_parity t u
    rw [hP _ _ hv, hP _ _ hv, hP _ _ hv, heven _ _ hu hv,
      preimagePairing_eq_sum, add_zero]
    cases h : evenLabel t u r₁ <;> simp [h, hP _ _ hv]
  have hmatrix : G = B + B.flip := by
    apply LinearMap.BilinForm.ext_basis (Pi.basisFun F₂ (EvenIndex t))
    intro u v
    simp only [Pi.basisFun_apply, LinearMap.BilinForm.add_apply,
      LinearMap.BilinForm.flip_apply, B, Matrix.toBilin'_single]
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        simp only [hentry, evenLabel, Sum.elim_inl, Sum.elim_inr]
        rw [preimagePairing_same_spectator r₁ r₂ t ht₁ ht₂ _ _
          (v.property.2.trans u.property.2.symm)]
        simp [crossMatrix]
      | inr v => rw [hentry]; simp [crossMatrix, crossPairing, evenLabel]
    | inr u =>
      cases v with
      | inl v => rw [hsym, hentry]; simp [crossMatrix, crossPairing, evenLabel]
      | inr v =>
        simp only [hentry, evenLabel, Sum.elim_inl, Sum.elim_inr]
        rw [preimagePairing_same_spectator r₁ r₂ t ht₁ ht₂ _ _
          (v.property.2.trans u.property.2.symm)]
        simp [crossMatrix]
  have hQ (x y) : Q (x + y) = Q x + Q y + (B x y + B y x) := by
    simpa only [hmatrix, LinearMap.BilinForm.add_apply, LinearMap.BilinForm.flip_apply] using hpol x y
  have hB (u : EvenIndex t) : Q (Pi.single u 1) = B (Pi.single u 1) (Pi.single u 1) := by
    dsimp only [Q, a, b, w, B]
    rw [hvalue u, Matrix.toBilin'_single]
    cases u <;> rfl
  let x : EvenIndex t → F₂ := Sum.elim p.1 p.2
  have h := quadratic_eq_of_polar_of_single Q B hQ hB x
  change Q x = B x x at h
  change Q x = crossExponent r₁ r₂ t p
  rw [h]
  simp only [B, Matrix.toBilin'_apply, crossExponent, Fintype.sum_sum_type, crossMatrix,
    x, Sum.elim_inl, Sum.elim_inr, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [mul_assoc]

private def wordI (r₁ : ι) : List (ι × Bool) := [(r₁, false), (r₁, true)]

private def wordJ (r₁ r₂ : ι) : List (ι × Bool) := [(r₁, false), (r₂, false), (r₂, true)]

private theorem pauliMap_eq_vecMul (hodd : (Fintype.card ι : F₂) = 1)
    (r : ι) (isZ : Bool) (x : Word ι → F₂) :
    pauliMap r isZ x = x ᵥ* TensorLift.modTwo (TensorLift.generator r isZ) := by
  let M := TensorLift.modTwo (TensorLift.generator r isZ)
  let T : (Word ι → F₂) →ₗ[F₂] (Word ι → F₂) :=
    { toFun := fun y => y ᵥ* M
      map_add' := fun y z => Matrix.add_vecMul M y z
      map_smul' := by intro c y; exact Matrix.smul_vecMul c y M }
  have he : pauliMap r isZ = T := by
    apply (Pi.basisFun F₂ (Word ι)).ext
    intro u
    simp only [Pi.basisFun_apply, pauliMap_single]
    change _ = Pi.single u (1 : F₂) ᵥ* M
    rw [Matrix.single_vecMul]
    funext v
    have hz : parity u ≠ 0 ↔ parity u = 1 := (by decide : ∀ z : F₂, z ≠ 0 ↔ z = 1) (parity u)
    rw [one_smul]
    change _ = TensorLift.modTwo (TensorLift.generator r isZ) u v
    rw [TensorLift.generator_modTwo_apply hodd]
    by_cases hp : parity u = 1 <;> by_cases hb : u r = isZ <;>
      simp [Pi.single_apply, Pi.add_apply, hp, hb, hz]
  exact LinearMap.congr_fun he x

private theorem actionI_eq (hodd : (Fintype.card ι : F₂) = 1) (r₁ : ι) (x : Word ι → F₂) :
    actionI r₁ x = x ᵥ* TensorLift.modTwo (TensorLift.wordMatrix (wordI r₁)) := by
  simp [actionI, LinearMap.comp_apply, pauliMap_eq_vecMul hodd, wordI, TensorLift.wordMatrix,
    Matrix.vecMul_vecMul]

private theorem actionJ_eq (hodd : (Fintype.card ι : F₂) = 1) (r₁ r₂ : ι) (x : Word ι → F₂) :
    actionJ r₁ r₂ x = x ᵥ* TensorLift.modTwo (TensorLift.wordMatrix (wordJ r₁ r₂)) := by
  simp [actionJ, LinearMap.comp_apply, pauliMap_eq_vecMul hodd, wordJ, TensorLift.wordMatrix,
    Matrix.vecMul_vecMul, mul_assoc]

private theorem lift_phase_polar [LinearOrder (Word ι)]
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 3 ≤ Fintype.card ι) (word : List (ι × Bool))
    (x y : Word ι → F₂) :
    let q := TensorLift.wordLiftExponent word
    let g := fun z => z ᵥ* TensorLift.modTwo (TensorLift.wordMatrix word)
    let H := (TensorGram.halfGram : Matrix (Word ι) (Word ι) F₂).toBilin'
    q (x + y) = q x + q y + (H x y + H (g x) (g y)) := by
  dsimp only
  have hp := TensorLift.wordLiftExponent_polar hodd hm word x y
  rw [add_assoc, CharTwo.add_eq_iff_eq_add] at hp
  exact hp.trans (add_comm _ _)

private theorem actual_basis_trace_zero [order : LinearOrder (Word ι)]
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 5 ≤ Fintype.card ι)
    (r₁ r₂ t : ι) (u : EvenIndex t) :
    let H : LinearMap.BilinForm F₂ (Word ι → F₂) := TensorGram.halfGram.toBilin'
    let x := Pi.single u 1
    TensorLift.wordLiftExponent (wordI r₁) (preimageIMap r₁ t x) +
      TensorLift.wordLiftExponent (wordJ r₁ r₂) (preimageJMap r₁ r₂ t x) +
      H (displacementMap t x) (preimageIMap r₁ t x + preimageJMap r₁ r₂ t x + displacementMap t x) = 0 := by
  dsimp only
  simp only [preimageIMap, preimageJMap, displacementMap, ← Pi.basisFun_apply,
    Module.Basis.constr_basis]
  simp only [Pi.basisFun_apply]
  let v := evenLabel t u
  have hv : ∀ q : ι, q ≠ r₁ → q ≠ r₂ → v q = v q := fun _ _ _ => rfl
  have ha : SupportedOnBlock r₁ r₂ v (Pi.single (wordFlip v r₁) 1) :=
    block_flip (Or.inl rfl) hv
  have hb : SupportedOnBlock r₁ r₂ v (Pi.single (wordFlip v r₂) 1 +
      if v r₁ then 0 else Pi.single (wordFlip v r₁) 1) := by
    have hs : SupportedOnBlock r₁ r₂ v (Pi.single (wordFlip v r₂) 1) :=
      block_flip (Or.inr rfl) hv
    cases h : v r₁
    · simpa [h] using block_add hs ha
    · simpa [h] using hs
  have hw := block_single r₁ r₂ v v hv
  have hI := TensorLift.wordLiftExponent_eq_zero_on_block hodd hm r₁ r₂ v (wordI r₁)
    (by simp [wordI]) _ ha
  have hJ := TensorLift.wordLiftExponent_eq_zero_on_block hodd hm r₁ r₂ v (wordJ r₁ r₂)
    (by simp [wordJ]) _ hb
  have hH := TensorGram.halfGram_bilin_eq_zero_on_block hodd hm r₁ r₂ v _ _ hw
    (block_add (block_add ha hb) hw)
  rw [hI, hJ, hH, add_zero, add_zero]

set_option maxHeartbeats 900000 in
private theorem actual_trace_exponent_eq [order : LinearOrder (Word ι)]
    (r₁ r₂ t : ι) (h₁₂ : r₁ ≠ r₂) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 5 ≤ Fintype.card ι)
    (p : (Half t false → F₂) × (Half t true → F₂)) :
    let H : LinearMap.BilinForm F₂ (Word ι → F₂) := TensorGram.halfGram.toBilin'
    traceExponent r₁ r₂ t H (TensorLift.wordLiftExponent (wordI r₁))
      (TensorLift.wordLiftExponent (wordJ r₁ r₂)) p = crossExponent r₁ r₂ t p := by
  dsimp only
  let H : LinearMap.BilinForm F₂ (Word ι → F₂) := TensorGram.halfGram.toBilin'
  have hI := lift_phase_polar hodd (by omega) (wordI r₁)
  have hJ := lift_phase_polar hodd (by omega) (wordJ r₁ r₂)
  simp only [← actionI_eq hodd r₁] at hI
  simp only [← actionJ_eq hodd r₁ r₂] at hJ
  refine exponent_eq_cross_of_sections r₁ r₂ t ht₁ ht₂ H (actionI r₁) (actionJ r₁ r₂)
    (TensorLift.wordLiftExponent (wordI r₁)) (TensorLift.wordLiftExponent (wordJ r₁ r₂)) hI hJ
    (actual_preimageI r₁ t) (actual_preimageJ r₁ r₂ t h₁₂) ?_ ?_ (actual_basis_trace_zero hodd hm r₁ r₂ t) p
  · intro u v hv
    simp only [H, LinearMap.BilinForm.add_apply, LinearMap.BilinForm.flip_apply, Matrix.toBilin'_single]
    rw [TensorGram.halfGram_symmetrize hodd (by omega), TensorGram.gram_mod_two_of_even_right hodd u v hv]
  · intro u v hu hv
    rw [← TensorGram.gram_mod_two_of_even_right hodd u v hv, TensorGram.gram_mod_two_of_even_even hodd u v hu hv]

/-- The KRR quaternion-lift Gauss sum at odd slot count at least five.
The coefficients use the normalized tensor Gram and the product of the
literal Pauli generator lifts in right-action order. -/
theorem tensor_trace_gauss_sum [LinearOrder (Word ι)] (r₁ r₂ t : ι)
    (h₁₂ : r₁ ≠ r₂) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 5 ≤ Fintype.card ι) :
    let H : LinearMap.BilinForm F₂ (Word ι → F₂) := TensorGram.halfGram.toBilin'
    (∑ p : (Half t false → F₂) × (Half t true → F₂), complexSign
      (traceExponent r₁ r₂ t H
        (TensorLift.wordLiftExponent [(r₁, false), (r₁, true)])
        (TensorLift.wordLiftExponent [(r₁, false), (r₂, false), (r₂, true)]) p)) =
      (2 : ℂ) ^ (2 ^ (Fintype.card ι - 2)) := by
  dsimp only
  change (∑ p : (Half t false → F₂) × (Half t true → F₂), complexSign
    (traceExponent r₁ r₂ t TensorGram.halfGram.toBilin'
      (TensorLift.wordLiftExponent (wordI r₁)) (TensorLift.wordLiftExponent (wordJ r₁ r₂)) p)) = _
  simp_rw [actual_trace_exponent_eq r₁ r₂ t h₁₂ ht₁ ht₂ hodd hm]
  exact cross_gauss_sum r₁ r₂ t h₁₂ ht₁ ht₂ hodd

#print axioms tensor_trace_gauss_sum

end
end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddGaussSum
