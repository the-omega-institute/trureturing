/- GID: D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockFockNormalField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical current jets and joint mode support for arbitrary native fields. -/

import D5.S3.VertexAlgebra.LatticeAllStateField
import Mathlib.RingTheory.Binomial
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedCoefficients
open scoped BigOperators TensorProduct

noncomputable section

abbrev NativeField (D : LatticeData) (hu : IsUnit D.G.det) :=
  HVertexOperator ℤ ℂ (ActualTensor D hu) (ActualTensor D hu)

def jetScalar (order : ℕ) (mode : ℤ) : ℂ :=
  (∏ offset ∈ Finset.range order, (-(mode : ℂ) - 3 / 2 - (offset : ℂ))) /
    (order.factorial : ℂ)

def jetCurrent (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D)
    (mode : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  jetScalar index.2 mode •
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 mode

theorem tensor_current_same_sign (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Fin D.rank) (left right : ℤ)
    (signs : (left < 0 ∧ right < 0) ∨ (0 ≤ left ∧ 0 ≤ right))
    (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) first left
      (LatticeHalfFock.tensorCurrent D (ActualGround D hu) second right vector) =
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) second right
      (LatticeHalfFock.tensorCurrent D (ActualGround D hu) first left vector) := by
  have distinct : left + right + 1 ≠ 0 := by rcases signs with signs | signs <;> omega
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    simp only [LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
      TensorProduct.map_tmul, LinearMap.id_apply]
    congr 1
    exact sub_eq_zero.mp (by simpa [distinct] using
      LatticeHalfFock.current_heisenberg_apply D first second left right polynomial)
  | add firstVector secondVector firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]

abbrev ModeTuple (D : LatticeData) : List (Index D) → Type
  | [] => Unit
  | _ :: tail => ℤ × ModeTuple D tail

def allModes (D : LatticeData) (predicate : ℤ → Prop) :
    (word : List (Index D)) → ModeTuple D word → Prop
  | [], _ => True
  | _ :: tail, modes => predicate modes.1 ∧ allModes D predicate tail modes.2

def modeSum (D : LatticeData) : (word : List (Index D)) → ModeTuple D word → ℤ
  | [], _ => 0
  | _ :: tail, modes => modes.1 + modeSum D tail modes.2

def jetShift (D : LatticeData) : List (Index D) → ℤ
  | [] => 0
  | index :: tail => 2 * (index.2 : ℤ) + 3 + jetShift D tail

def modeBox (D : LatticeData) : (word : List (Index D)) → ℤ → ℤ → Finset (ModeTuple D word)
  | [], _, _ => {()}
  | _ :: tail, lower, upper => (Finset.Icc lower upper).product (modeBox D tail lower upper)

private theorem mem_modeBox (D : LatticeData) (word : List (Index D))
    (lower upper : ℤ) (modes : ModeTuple D word) :
    modes ∈ modeBox D word lower upper ↔ allModes D (fun mode => lower ≤ mode ∧ mode ≤ upper) word modes := by
  induction word with
  | nil => cases modes; simp [modeBox, allModes]
  | cons index tail induction =>
    rcases modes with ⟨mode, remaining⟩
    change (mode, remaining) ∈ (Finset.Icc lower upper).product (modeBox D tail lower upper) ↔
      (lower ≤ mode ∧ mode ≤ upper) ∧ allModes D (fun mode => lower ≤ mode ∧ mode ≤ upper) tail remaining
    exact (Finset.mem_product (s := Finset.Icc lower upper)
      (t := modeBox D tail lower upper) (p := (mode, remaining))).trans
        (by rw [Finset.mem_Icc, induction])

def leftAction (D : LatticeData) (hu : IsUnit D.G.det) :
    (word : List (Index D)) → ModeTuple D word → Module.End ℂ (ActualTensor D hu)
  | [], _ => 1
  | index :: tail, modes =>
    if modes.1 < 0 then jetCurrent D hu index modes.1 * leftAction D hu tail modes.2
    else leftAction D hu tail modes.2

def rightAction (D : LatticeData) (hu : IsUnit D.G.det) :
    (word : List (Index D)) → ModeTuple D word → Module.End ℂ (ActualTensor D hu)
  | [], _ => 1
  | index :: tail, modes =>
    if modes.1 < 0 then rightAction D hu tail modes.2
    else rightAction D hu tail modes.2 * jetCurrent D hu index modes.1

def flatCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (field : NativeField D hu) :
    (word : List (Index D)) → ModeTuple D word → ℤ → Module.End ℂ (ActualTensor D hu)
  | [], _, exponent => field.coeff exponent
  | index :: tail, modes, exponent =>
    if modes.1 < 0 then jetCurrent D hu index modes.1 *
      flatCoefficient D hu field tail modes.2 (exponent + 2 * modes.1 + 2 * index.2 + 3)
    else flatCoefficient D hu field tail modes.2 (exponent + 2 * modes.1 + 2 * index.2 + 3) *
      jetCurrent D hu index modes.1

def flatTerm (D : LatticeData) (hu : IsUnit D.G.det) (field : NativeField D hu)
    (word : List (Index D)) (exponent : ℤ) (vector : ActualTensor D hu)
    (modes : ModeTuple D word) : ActualTensor D hu :=
  flatCoefficient D hu field word modes exponent vector

theorem flatCoefficient_factorization (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (modes : ModeTuple D word) (exponent : ℤ) :
    flatCoefficient D hu field word modes exponent =
      leftAction D hu word modes * field.coeff (exponent + 2 * modeSum D word modes + jetShift D word) *
        rightAction D hu word modes := by
  induction word generalizing exponent with
  | nil => simp [flatCoefficient, leftAction, rightAction, modeSum, jetShift]
  | cons index tail induction =>
    simp only [flatCoefficient, leftAction, rightAction, modeSum, jetShift]
    rw [induction]
    have shift : exponent + 2 * modes.1 + 2 * index.2 + 3 + 2 * modeSum D tail modes.2 + jetShift D tail =
        exponent + 2 * (modes.1 + modeSum D tail modes.2) + (2 * (index.2 : ℤ) + 3 + jetShift D tail) := by ring
    rw [shift]
    split_ifs <;> simp only [mul_assoc]

private theorem current_bound_after_jet (D : LatticeData) (hu : IsUnit D.G.det)
    (vector : ActualTensor D hu) (cutoff : ℕ)
    (bound : ∀ colour mode, (cutoff : ℤ) ≤ mode →
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector = 0)
    (index : Index D) (mode : ℤ) (positive : 0 ≤ mode) :
    ∀ colour high, (cutoff : ℤ) ≤ high →
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour high
        (jetCurrent D hu index mode vector) = 0 := by
  intro colour high above
  simp only [jetCurrent, LinearMap.smul_apply, map_smul]
  rw [tensor_current_same_sign D hu colour index.1 high mode
    (Or.inr ⟨by omega, positive⟩), bound colour high above, map_zero, smul_zero]

private theorem flatTerm_upper (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (exponent : ℤ)
    (vector : ActualTensor D hu) (cutoff : ℕ)
    (bound : ∀ colour mode, (cutoff : ℤ) ≤ mode →
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector = 0)
    (modes : ModeTuple D word) (nonzero : flatTerm D hu field word exponent vector modes ≠ 0) :
    allModes D (fun mode => mode < (cutoff : ℤ)) word modes := by
  induction word generalizing exponent vector with
  | nil => trivial
  | cons index tail induction =>
    change (modes.1 < (cutoff : ℤ)) ∧ _
    by_cases negative : modes.1 < 0
    · refine ⟨by omega, ?_⟩
      apply induction _ vector bound modes.2
      intro zero
      apply nonzero
      simp only [flatTerm, flatCoefficient, if_pos negative, Module.End.mul_apply]
      change jetCurrent D hu index modes.1 (flatTerm D hu field tail _ vector modes.2) = 0
      rw [zero, map_zero]
    · have tailNonzero : flatTerm D hu field tail
          (exponent + 2 * modes.1 + 2 * index.2 + 3) (jetCurrent D hu index modes.1 vector) modes.2 ≠ 0 := by
        simpa only [flatTerm, flatCoefficient, if_neg negative, Module.End.mul_apply] using nonzero
      refine ⟨?_, induction _ _ (current_bound_after_jet D hu vector cutoff bound index modes.1 (by omega)) modes.2 tailNonzero⟩
      by_contra outside
      have zero : jetCurrent D hu index modes.1 vector = 0 := by
        simp [jetCurrent, bound index.1 modes.1 (by omega)]
      exact tailNonzero (by simp [flatTerm, zero])

def rightCode (D : LatticeData) : (word : List (Index D)) → ModeTuple D word → ModeTuple D word
  | [], _ => ()
  | _ :: tail, modes => (if modes.1 < 0 then -1 else modes.1, rightCode D tail modes.2)

private theorem rightAction_code (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (modes : ModeTuple D word) :
    rightAction D hu word (rightCode D word modes) = rightAction D hu word modes := by
  induction word with
  | nil => rfl
  | cons index tail induction =>
    simp only [rightCode, rightAction]
    split_ifs <;> simp_all

private theorem rightCode_mem (D : LatticeData) (word : List (Index D))
    (modes : ModeTuple D word) (cutoff : ℕ)
    (upper : allModes D (fun mode => mode < (cutoff : ℤ)) word modes) :
    rightCode D word modes ∈ modeBox D word (-1) cutoff := by
  rw [mem_modeBox]
  induction word with
  | nil => trivial
  | cons index tail induction =>
    refine ⟨?_, induction modes.2 upper.2⟩
    dsimp only [rightCode]
    split_ifs <;> have := upper.1 <;> omega

def flatLower (D : LatticeData) (hu : IsUnit D.G.det) (field : NativeField D hu)
    (word : List (Index D)) (vector : ActualTensor D hu) (cutoff : ℕ) : ℤ :=
  (insert 0 ((modeBox D word (-1) cutoff).image (fun modes =>
    ((HahnModule.of ℂ).symm (field (rightAction D hu word modes vector))).order))).min' (by simp)

private theorem modeSum_upper (D : LatticeData) (word : List (Index D))
    (modes : ModeTuple D word) (upper : ℤ)
    (bound : allModes D (fun mode => mode ≤ upper) word modes) :
    modeSum D word modes ≤ (word.length : ℤ) * upper := by
  induction word with
  | nil => simp [modeSum]
  | cons index tail induction =>
    have tailBound := induction modes.2 bound.2
    simp only [modeSum, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [bound.1]

private theorem allModes_mono (D : LatticeData) (word : List (Index D)) (modes : ModeTuple D word)
    (first second : ℤ → Prop) (implication : ∀ mode, first mode → second mode)
    (bound : allModes D first word modes) : allModes D second word modes := by
  induction word with
  | nil => trivial
  | cons index tail induction => exact ⟨implication modes.1 bound.1, induction modes.2 bound.2⟩

private theorem modeSum_lower (D : LatticeData) (word : List (Index D))
    (modes : ModeTuple D word) (upper lower : ℤ) (nonnegative : 0 ≤ upper)
    (bound : allModes D (fun mode => mode ≤ upper) word modes)
    (total : lower ≤ modeSum D word modes) :
    allModes D (fun mode => lower - (word.length : ℤ) * upper ≤ mode) word modes := by
  induction word generalizing lower with
  | nil => trivial
  | cons index tail induction =>
    have tailUpper := modeSum_upper D tail modes.2 upper bound.2
    have tailLower : lower - upper ≤ modeSum D tail modes.2 := by
      change lower ≤ modes.1 + modeSum D tail modes.2 at total
      linarith [bound.1]
    have tailBound := induction modes.2 (lower - upper) bound.2 tailLower
    change _ ∧ _
    constructor
    · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      change lower ≤ modes.1 + modeSum D tail modes.2 at total
      nlinarith
    · apply allModes_mono D tail modes.2 _ _ _ tailBound
      intro mode hypothesis
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

private theorem allModes_and (D : LatticeData) (word : List (Index D))
    (modes : ModeTuple D word) (first second : ℤ → Prop)
    (firstBound : allModes D first word modes) (secondBound : allModes D second word modes) :
    allModes D (fun mode => first mode ∧ second mode) word modes := by
  induction word with
  | nil => trivial
  | cons index tail induction =>
    exact ⟨⟨firstBound.1, secondBound.1⟩, induction modes.2 firstBound.2 secondBound.2⟩

private theorem coefficient_vanish (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (vector : ActualTensor D hu) (exponent : ℤ)
    (below : exponent < ((HahnModule.of ℂ).symm (field vector)).order) :
    field.coeff exponent vector = 0 := by
  change ((HahnModule.of ℂ).symm (field vector)).coeff exponent = 0
  exact HahnSeries.coeff_eq_zero_of_lt_order below

theorem flatTerm_support_bound (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (exponent : ℤ)
    (vector : ActualTensor D hu) (cutoff : ℕ)
    (bound : ∀ colour mode, (cutoff : ℤ) ≤ mode →
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector = 0) :
    Function.support (flatTerm D hu field word exponent vector) ⊆
      modeBox D word
        (min (flatLower D hu field word vector cutoff - exponent - jetShift D word) 0 -
          (word.length : ℤ) * cutoff) cutoff := by
  classical
  intro modes nonzero
  have upper := flatTerm_upper D hu field word exponent vector cutoff bound modes nonzero
  have weakUpper := allModes_mono D word modes _ (fun mode => mode ≤ (cutoff : ℤ))
    (fun mode hypothesis => le_of_lt hypothesis) upper
  have codeMember := rightCode_mem D word modes cutoff upper
  have orderMember : ((HahnModule.of ℂ).symm
      (field (rightAction D hu word modes vector))).order ∈
      insert 0 ((modeBox D word (-1) cutoff).image (fun modes =>
        ((HahnModule.of ℂ).symm (field (rightAction D hu word modes vector))).order)) := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨rightCode D word modes, codeMember, by rw [rightAction_code]⟩
  have orderBound := Finset.min'_le _ _ orderMember
  change flatLower D hu field word vector cutoff ≤ _ at orderBound
  have chargedBound : flatLower D hu field word vector cutoff ≤
      exponent + 2 * modeSum D word modes + jetShift D word := by
    by_contra below
    have zero := coefficient_vanish D hu field (rightAction D hu word modes vector)
      (exponent + 2 * modeSum D word modes + jetShift D word) (by omega)
    apply nonzero
    simp only [flatTerm, flatCoefficient_factorization, Module.End.mul_apply, zero, map_zero]
  have totalBound : min (flatLower D hu field word vector cutoff - exponent - jetShift D word) 0 ≤
      modeSum D word modes := by omega
  have lower := modeSum_lower D word modes cutoff _ (by omega) weakUpper totalBound
  rw [Finset.mem_coe, mem_modeBox]
  exact allModes_and D word modes _ _ lower weakUpper

end
end D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
