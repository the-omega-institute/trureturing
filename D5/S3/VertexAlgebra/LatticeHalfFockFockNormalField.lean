/- GID: D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockFockNormalField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical current jets and finite Fock-normal corrected native fields. -/

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

theorem jetCurrent_same_sign (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Index D) (left right : ℤ)
    (signs : (left < 0 ∧ right < 0) ∨ (0 ≤ left ∧ 0 ≤ right)) :
    jetCurrent D hu first left * jetCurrent D hu second right =
      jetCurrent D hu second right * jetCurrent D hu first left := by
  apply LinearMap.ext
  intro vector
  simp only [Module.End.mul_apply, jetCurrent, LinearMap.smul_apply, map_smul]
  rw [tensor_current_same_sign D hu first.1 second.1 left right signs, smul_comm]

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

def negativeTerm (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D)
    (field : NativeField D hu) (exponent : ℤ) (vector : ActualTensor D hu)
    (offset : ℕ) : ActualTensor D hu :=
  jetScalar index.2 (-(offset : ℤ) - 1) •
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 (-(offset : ℤ) - 1)
      (field.coeff (exponent - 2 * offset + 2 * index.2 + 1) vector)

def positiveTerm (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D)
    (field : NativeField D hu) (exponent : ℤ) (vector : ActualTensor D hu)
    (offset : ℕ) : ActualTensor D hu :=
  jetScalar index.2 offset •
    field.coeff (exponent + 2 * offset + 2 * index.2 + 3)
      (LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 offset vector)

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

theorem flatTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (exponent : ℤ)
    (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (flatTerm D hu field word exponent vector) := by
  have finite_of_bound (state : ActualTensor D hu) (cutoff : ℕ)
      (bound : ∀ colour mode, (cutoff : ℤ) ≤ mode →
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode state = 0) :
      Function.HasFiniteSupport (flatTerm D hu field word exponent state) :=
    (modeBox D word
      (min (flatLower D hu field word state cutoff - exponent - jetShift D word) 0 -
        (word.length : ℤ) * cutoff) cutoff).finite_toSet.subset
          (flatTerm_support_bound D hu field word exponent state cutoff bound)
  induction vector using TensorProduct.induction_on with
  | zero => exact finite_of_bound 0 0 (by intros; simp)
  | tmul polynomial ground =>
    apply finite_of_bound _ (LatticeHalfFock.bound D polynomial)
    intro colour mode above
    simp [LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
      LatticeHalfFock.current_vanish D colour polynomial mode above]
  | add first second firstProof secondProof =>
    have terms : flatTerm D hu field word exponent (first + second) =
        fun modes => flatTerm D hu field word exponent first modes +
          flatTerm D hu field word exponent second modes := by
      funext modes
      exact (flatCoefficient D hu field word modes exponent).map_add first second
    rw [terms]
    exact firstProof.add secondProof

theorem negativeTerm_finite (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D)
    (field : NativeField D hu) (exponent : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (negativeTerm D hu index field exponent vector) := by
  classical
  apply BddAbove.finite
  refine bddAbove_def.mpr ⟨(exponent + 2 * (index.2 : ℤ) + 1 -
    ((HahnModule.of ℂ).symm (field vector)).order).toNat, ?_⟩
  intro offset member
  have nonzero : field.coeff (exponent - 2 * offset + 2 * index.2 + 1) vector ≠ 0 := by
    intro zero
    apply member
    unfold negativeTerm
    rw [zero, map_zero, smul_zero]
  have order_bound : ((HahnModule.of ℂ).symm (field vector)).order ≤
      exponent - 2 * offset + 2 * index.2 + 1 :=
    HahnSeries.order_le_of_coeff_ne_zero nonzero
  omega

theorem positiveTerm_finite (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D)
    (field : NativeField D hu) (exponent : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (positiveTerm D hu index field exponent vector) := by
  obtain ⟨cutoff, bound⟩ := LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector
  apply (Finset.range cutoff).finite_toSet.subset
  intro offset member
  by_contra outside
  have high : (cutoff : ℤ) ≤ offset := by
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at outside
    exact_mod_cast outside
  exact member (by simp [positiveTerm, bound index.1 offset high])

def normalCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D)
    (field : NativeField D hu) (exponent : ℤ) : Module.End ℂ (ActualTensor D hu) where
  toFun vector := (∑ᶠ offset : ℕ, negativeTerm D hu index field exponent vector offset) +
    ∑ᶠ offset : ℕ, positiveTerm D hu index field exponent vector offset
  map_add' first second := by
    have negative : negativeTerm D hu index field exponent (first + second) =
        fun offset => negativeTerm D hu index field exponent first offset +
          negativeTerm D hu index field exponent second offset := by
      funext offset
      simp only [negativeTerm, map_add, smul_add]
    have positive : positiveTerm D hu index field exponent (first + second) =
        fun offset => positiveTerm D hu index field exponent first offset +
          positiveTerm D hu index field exponent second offset := by
      funext offset
      simp only [positiveTerm, map_add, smul_add]
    rw [negative, positive]
    rw [finsum_add_distrib (negativeTerm_finite D hu index field exponent first)
        (negativeTerm_finite D hu index field exponent second),
      finsum_add_distrib (positiveTerm_finite D hu index field exponent first)
        (positiveTerm_finite D hu index field exponent second)]
    abel
  map_smul' scalar vector := by
    have negative : negativeTerm D hu index field exponent (scalar • vector) =
        fun offset => scalar • negativeTerm D hu index field exponent vector offset := by
      funext offset
      simp only [negativeTerm, map_smul, RingHom.id_apply]
      exact smul_comm _ _ _
    have positive : positiveTerm D hu index field exponent (scalar • vector) =
        fun offset => scalar • positiveTerm D hu index field exponent vector offset := by
      funext offset
      simp only [positiveTerm, map_smul, RingHom.id_apply]
      exact smul_comm _ _ _
    rw [negative, positive, ← smul_finsum' scalar (negativeTerm_finite D hu index field exponent vector),
      ← smul_finsum' scalar (positiveTerm_finite D hu index field exponent vector), smul_add]
    rfl

theorem normalCoefficient_lower_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) (vector : ActualTensor D hu) :
    ∃ lower : ℤ, ∀ exponent : ℤ, exponent < lower →
      normalCoefficient D hu index field exponent vector = 0 := by
  classical
  obtain ⟨cutoff, bound⟩ := LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector
  let orders : Finset ℤ := (Finset.range (cutoff + 1)).image fun offset : ℕ =>
    ((HahnModule.of ℂ).symm
      (field (LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 offset vector))).order -
        2 * offset - 2 * index.2 - 3
  have nonempty : orders.Nonempty := by
    apply Finset.image_nonempty.mpr
    exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  let lower := min (((HahnModule.of ℂ).symm (field vector)).order - 2 * index.2 - 1)
    (orders.min' nonempty)
  refine ⟨lower, ?_⟩
  intro exponent below
  have negative : ∀ offset : ℕ, negativeTerm D hu index field exponent vector offset = 0 := by
    intro offset
    have vanish : field.coeff (exponent - 2 * offset + 2 * index.2 + 1) vector = 0 := by
      apply coefficient_vanish D hu field vector
      have low := lt_of_lt_of_le below (min_le_left _ _)
      omega
    unfold negativeTerm
    rw [vanish, map_zero, smul_zero]
  have positive : ∀ offset : ℕ, positiveTerm D hu index field exponent vector offset = 0 := by
    intro offset
    by_cases within : offset ≤ cutoff
    · have member : ((HahnModule.of ℂ).symm
          (field (LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 offset vector))).order -
            2 * offset - 2 * index.2 - 3 ∈ orders := by
        exact Finset.mem_image.mpr ⟨offset, Finset.mem_range.mpr (by omega), rfl⟩
      have order_bound := Finset.min'_le orders _ member
      have vanish : field.coeff (exponent + 2 * offset + 2 * index.2 + 3)
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 offset vector) = 0 := by
        apply coefficient_vanish D hu field
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 offset vector)
        have low := lt_of_lt_of_le below (min_le_right _ _)
        omega
      unfold positiveTerm
      rw [vanish, smul_zero]
    · have high : (cutoff : ℤ) ≤ offset := by omega
      unfold positiveTerm
      rw [bound index.1 offset high, map_zero, smul_zero]
  simp only [normalCoefficient, LinearMap.coe_mk, AddHom.coe_mk, negative, positive,
    finsum_zero, add_zero]

def normalInsertion (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D)
    (field : NativeField D hu) : NativeField D hu :=
  HVertexOperator.of_coeff (normalCoefficient D hu index field) (by
    intro vector
    obtain ⟨lower, bound⟩ := normalCoefficient_lower_truncation D hu index field vector
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨lower, ?_⟩
    intro exponent member
    by_contra outside
    exact member (bound exponent (by omega)))

private theorem finsum_integer_split {Value : Type*} [AddCommMonoid Value]
    (terms : ℤ → Value) (finite : Function.HasFiniteSupport terms) :
    (∑ᶠ mode : ℤ, terms mode) =
      (∑ᶠ offset : ℕ, terms (-(offset : ℤ) - 1)) + ∑ᶠ offset : ℕ, terms offset := by
  have cover : Set.range (fun offset : ℕ => -(offset : ℤ) - 1) ∪
      Set.range (fun offset : ℕ => (offset : ℤ)) = Set.univ := by
    ext mode
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    by_cases negative : mode < 0
    · exact Or.inl ⟨(-mode - 1).toNat, by omega⟩
    · exact Or.inr ⟨mode.toNat, by omega⟩
  have disjoint : Disjoint (Set.range (fun offset : ℕ => -(offset : ℤ) - 1))
      (Set.range (fun offset : ℕ => (offset : ℤ))) := by
    rw [Set.disjoint_left]
    rintro mode ⟨negative, rfl⟩ ⟨positive, equality⟩
    dsimp at equality
    omega
  rw [← finsum_mem_univ, ← cover, finsum_mem_union' disjoint
    (finite.subset Set.inter_subset_right) (finite.subset Set.inter_subset_right)]
  rw [finsum_mem_range (by intro first second equality; dsimp at equality; omega),
    finsum_mem_range (by intro first second equality; dsimp at equality; omega)]

theorem normalInsertion_integer_modes (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) (exponent : ℤ) (vector : ActualTensor D hu) :
    (normalInsertion D hu index field).coeff exponent vector =
      ∑ᶠ mode : ℤ, flatTerm D hu field [index] exponent vector (mode, ()) := by
  have finite : Function.HasFiniteSupport
      (fun mode : ℤ => flatTerm D hu field [index] exponent vector (mode, ())) :=
    (flatTerm_finite D hu field [index] exponent vector).comp_of_injective
    (show Function.Injective (fun mode : ℤ => (mode, ())) from by
      intro first second equality; exact congrArg Prod.fst equality)
  rw [finsum_integer_split _ finite]
  simp only [normalInsertion, HVertexOperator.coeff_of_coeff, normalCoefficient,
    LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  · apply finsum_congr
    intro offset
    simp only [negativeTerm, flatTerm, flatCoefficient, jetCurrent, LinearMap.smul_apply,
      Module.End.mul_apply, if_pos (show -(offset : ℤ) - 1 < 0 by omega)]
    congr 2
    ring
  · apply finsum_congr
    intro offset
    simp only [positiveTerm, flatTerm, flatCoefficient, jetCurrent, LinearMap.smul_apply,
      Module.End.mul_apply, if_neg (show ¬ (offset : ℤ) < 0 by omega), map_smul]

def normalSequence (D : LatticeData) (hu : IsUnit D.G.det) (field : NativeField D hu) :
    List (Index D) → NativeField D hu
  | [] => field
  | index :: tail => normalInsertion D hu index (normalSequence D hu field tail)

theorem normalSequence_flattened (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (exponent : ℤ) (vector : ActualTensor D hu) :
    (normalSequence D hu field word).coeff exponent vector =
      ∑ᶠ modes : ModeTuple D word, flatTerm D hu field word exponent vector modes := by
  induction word generalizing exponent vector with
  | nil => simp [normalSequence, flatTerm, flatCoefficient, ModeTuple, finsum_unique]
  | cons index tail induction =>
    rw [normalSequence, normalInsertion_integer_modes]
    rw [finsum_curry _ (flatTerm_finite D hu field (index :: tail) exponent vector)]
    apply finsum_congr
    intro mode
    by_cases negative : mode < 0
    · simp only [flatTerm, flatCoefficient, if_pos negative, Module.End.mul_apply]
      rw [induction, map_finsum _ (flatTerm_finite D hu field tail _ vector)]
      apply finsum_congr
      intro modes
      simp only [flatTerm, flatCoefficient, if_pos negative, Module.End.mul_apply]
    · simp only [flatTerm, flatCoefficient, if_neg negative, Module.End.mul_apply]
      rw [induction]
      apply finsum_congr
      intro modes
      simp only [flatTerm, flatCoefficient, if_neg negative, Module.End.mul_apply]

theorem flatCoefficient_swap (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (first second : Index D) (tail : List (Index D))
    (left right : ℤ) (modes : ModeTuple D tail) (exponent : ℤ) :
    flatCoefficient D hu field (first :: second :: tail) (left, right, modes) exponent =
      flatCoefficient D hu field (second :: first :: tail) (right, left, modes) exponent := by
  have shift : exponent + 2 * left + 2 * first.2 + 3 + 2 * right + 2 * second.2 + 3 =
      exponent + 2 * right + 2 * second.2 + 3 + 2 * left + 2 * first.2 + 3 := by ring
  by_cases leftNegative : left < 0 <;> by_cases rightNegative : right < 0
  · simp only [flatCoefficient, if_pos leftNegative, if_pos rightNegative]
    rw [shift, ← mul_assoc, jetCurrent_same_sign D hu first second left right
      (Or.inl ⟨leftNegative, rightNegative⟩), mul_assoc]
  · simp only [flatCoefficient, if_pos leftNegative, if_neg rightNegative]
    rw [shift, mul_assoc]
  · simp only [flatCoefficient, if_neg leftNegative, if_pos rightNegative]
    rw [shift, mul_assoc]
  · simp only [flatCoefficient, if_neg leftNegative, if_neg rightNegative]
    rw [shift, mul_assoc, jetCurrent_same_sign D hu second first right left
      (Or.inr ⟨by omega, by omega⟩), ← mul_assoc]

private def swapModes (D : LatticeData) (first second : Index D) (tail : List (Index D)) :
    ModeTuple D (first :: second :: tail) ≃ ModeTuple D (second :: first :: tail) where
  toFun modes := (modes.2.1, modes.1, modes.2.2)
  invFun modes := (modes.2.1, modes.1, modes.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem normalInsertion_commute (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Index D) (field : NativeField D hu) :
    normalInsertion D hu first (normalInsertion D hu second field) =
      normalInsertion D hu second (normalInsertion D hu first field) := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  change (normalSequence D hu field [first, second]).coeff exponent vector =
    (normalSequence D hu field [second, first]).coeff exponent vector
  rw [normalSequence_flattened, normalSequence_flattened]
  apply finsum_eq_of_bijective (swapModes D first second [])
    (swapModes D first second []).bijective
  intro modes
  exact congrArg (fun operator : Module.End ℂ (ActualTensor D hu) => operator vector)
    (flatCoefficient_swap D hu field first second [] modes.1 modes.2.1 modes.2.2 exponent)

def normalWord (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    List (Index D) → NativeField D hu
  | [] => chargedField D hu charge
  | index :: tail => normalInsertion D hu index (normalWord D hu charge tail)

theorem normalWord_flattened (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (word : List (Index D)) (exponent : ℤ) (vector : ActualTensor D hu) :
    (normalWord D hu charge word).coeff exponent vector =
      ∑ᶠ modes : ModeTuple D word,
        flatTerm D hu (chargedField D hu charge) word exponent vector modes := by
  have sequence : normalWord D hu charge word = normalSequence D hu (chargedField D hu charge) word := by
    induction word with
    | nil => rfl
    | cons index tail induction => simp only [normalWord, normalSequence, induction]
  rw [sequence, normalSequence_flattened]

theorem normalWord_perm (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (first second : List (Index D)) (permutation : first.Perm second) :
    normalWord D hu charge first = normalWord D hu charge second := by
  induction permutation with
  | nil => rfl
  | cons index permutation induction => simp only [normalWord, induction]
  | swap first second tail =>
    exact normalInsertion_commute D hu second first (normalWord D hu charge tail)
  | trans firstPermutation secondPermutation firstProof secondProof =>
    exact firstProof.trans secondProof

def normalPolynomial (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    Oscillator D →ₗ[ℂ] NativeField D hu :=
  (MvPolynomial.basisMonomials (Index D) ℂ).constr ℂ
    (fun exponent => normalWord D hu charge (LatticeAllStateField.occurrences D exponent))

theorem normalPolynomial_monomial_enumeration (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : Index D →₀ ℕ) (word : List (Index D))
    (enumeration : word.Perm (LatticeAllStateField.occurrences D exponent)) :
    normalPolynomial D hu charge (MvPolynomial.monomial exponent 1) = normalWord D hu charge word := by
  have basis := (MvPolynomial.basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => normalWord D hu charge (LatticeAllStateField.occurrences D exponent)) exponent
  exact basis.trans (normalWord_perm D hu charge word _ enumeration).symm

theorem normalPolynomial_enumerated_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) (words : (Index D →₀ ℕ) → List (Index D))
    (enumeration : ∀ exponent ∈ polynomial.support,
      (words exponent).Perm (LatticeAllStateField.occurrences D exponent)) :
    normalPolynomial D hu charge polynomial = ∑ exponent ∈ polynomial.support,
      MvPolynomial.coeff exponent polynomial • normalWord D hu charge (words exponent) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum polynomial]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro exponent member
  have monomial : MvPolynomial.monomial exponent (MvPolynomial.coeff exponent polynomial) =
      MvPolynomial.coeff exponent polynomial • MvPolynomial.monomial exponent (1 : ℂ) := by
    simp [MvPolynomial.smul_monomial]
  rw [monomial, map_smul, normalPolynomial_monomial_enumeration D hu charge exponent
    (words exponent) (enumeration exponent member)]

def shiftField (D : LatticeData) (hu : IsUnit D.G.det) (shift : ℕ)
    (field : NativeField D hu) : NativeField D hu :=
  HVertexOperator.of_coeff (fun exponent => field.coeff (exponent + 2 * shift)) (by
    intro vector
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨((HahnModule.of ℂ).symm (field vector)).order - 2 * shift, ?_⟩
    intro exponent member
    by_contra outside
    exact member (coefficient_vanish D hu field vector _ (by omega)))

def shiftLinear (D : LatticeData) (hu : IsUnit D.G.det) (shift : ℕ) :
    NativeField D hu →ₗ[ℂ] NativeField D hu where
  toFun := shiftField D hu shift
  map_add' first second := by
    apply HVertexOperator.coeff_inj
    ext exponent vector
    simp only [shiftField, HVertexOperator.coeff_of_coeff]
    rfl

  map_smul' scalar field := by
    apply HVertexOperator.coeff_inj
    ext exponent vector
    simp only [shiftField, HVertexOperator.coeff_of_coeff]
    rfl

private theorem halfCreation_zero_charge (D : LatticeData) :
    halfCreationExponential D 0 = 1 := by
  have series : halfCreationSeries D 0 = 0 := by
    ext degree
    simp [halfCreationSeries]
  rw [halfCreationExponential, series, PowerSeries.subst_zero_eq_C_constantCoeff,
    PowerSeries.constantCoeff_exp]
  simp

private theorem halfTranslation_zero_charge (D : LatticeData) (polynomial : Oscillator D) :
    halfTranslatedPolynomial D 0 polynomial = Polynomial.C polynomial := by
  have maps : MvPolynomial.eval₂AlgHom ℂ (halfTranslationVariable D 0) =
      (Polynomial.CAlgHom (R := ℂ) (A := Oscillator D)).comp
        (AlgHom.id ℂ (Oscillator D)) := by
    ext index
    simp [halfTranslationVariable, bilinear]
  rw [halfTranslatedPolynomial, maps]
  rfl

private theorem ground_zero_charge (D : LatticeData) (hu : IsUnit D.G.det) :
    groundAction D hu 0 = 1 := by
  have lift : groundLift D 0 = 1 := by
    apply congrArg QuotientGroup.mk
    rfl
  rw [groundAction, lift, map_one]

private theorem identity_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (exponent : ℤ) (state : ActualTensor D hu) :
    (FieldNormalProduct.identityField (V := ActualTensor D hu)).coeff exponent state =
      if exponent = 0 then state else 0 := by
  change ((HahnModule.of ℂ).symm
    ((FieldNormalProduct.identityField (V := ActualTensor D hu)) state)).coeff exponent = _
  rw [FieldNormalProduct.identityField, VertexOperator.of_coeff_apply_coeff]
  split_ifs <;> rfl

theorem charged_zero_identity (D : LatticeData) (hu : IsUnit D.G.det) :
    chargedField D hu 0 = FieldNormalProduct.identityField := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [chargedField, HVertexOperator.coeff_of_coeff]
  rw [identity_coefficient]
  have oscillator (polynomial : Oscillator D) :
      oscillatorCoefficient D 0 exponent polynomial = if exponent = 0 then polynomial else 0 := by
    change (∑ᶠ degree : ℕ, oscillatorTerm D 0 exponent polynomial degree) = _
    rw [finsum_eq_single _ 0]
    · simp only [oscillatorTerm, halfTranslation_zero_charge, Polynomial.coeff_C_zero,
        chargeNorm, bilinear, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
        zero_add, add_zero, halfCreationCoeff, halfCreation_zero_charge]
      by_cases zero : exponent = 0
      · simp [zero]
      · by_cases negative : exponent < 0
        · simp [negative, zero]
        · have positive : exponent.toNat ≠ 0 := by omega
          simp [negative, positive, zero]
    · intro degree nonzero
      simp only [oscillatorTerm, halfTranslation_zero_charge,
        Polynomial.coeff_C, if_neg nonzero, zero_mul]
  induction vector using TensorProduct.induction_on with
  | zero => simp only [map_zero, ite_self]
  | tmul polynomial ground =>
    simp only [chargedCoefficient, chargeScalar, chargeNorm, bilinear, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, neg_zero, zpow_zero, one_smul,
      ground_zero_charge, TensorProduct.map_tmul, oscillator, Module.End.one_apply]
    by_cases zero : exponent = 0
    · simp only [zero, if_true]
    · simp only [if_neg zero, TensorProduct.zero_tmul]
  | add first second inductionFirst inductionSecond =>
    simp only [map_add, inductionFirst, inductionSecond]
    split_ifs <;> simp only [add_zero]

theorem normalPolynomial_one (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) :
    normalPolynomial D hu charge 1 = chargedField D hu charge := by
  have basis := (MvPolynomial.basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => normalWord D hu charge
      (LatticeAllStateField.occurrences D exponent)) 0
  simpa [normalPolynomial, LatticeAllStateField.occurrences, normalWord] using basis

theorem normalPolynomial_X (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) :
    normalPolynomial D hu charge (MvPolynomial.X index) =
      normalInsertion D hu index (chargedField D hu charge) := by
  have basis := (MvPolynomial.basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => normalWord D hu charge
      (LatticeAllStateField.occurrences D exponent)) (Finsupp.single index 1)
  simpa [normalPolynomial, LatticeAllStateField.occurrences, normalWord,
    MvPolynomial.X] using basis

theorem shiftLinear_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) :
    shiftLinear D hu 0 field = field := by
  apply HVertexOperator.coeff_inj
  simp only [shiftLinear, shiftField, HVertexOperator.coeff_of_coeff,
    LinearMap.coe_mk, AddHom.coe_mk, Nat.cast_zero, mul_zero, add_zero]

theorem normalInsertion_identity_current (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) :
    normalInsertion D hu (colour, 0) FieldNormalProduct.identityField =
      LatticeHalfFock.tensorCurrentField D (ActualGround D hu) colour := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [normalInsertion, HVertexOperator.coeff_of_coeff,
    LatticeHalfFock.tensorCurrentField, HVertexOperator.coeff_of_coeff]
  have negative (offset : ℕ) :
      negativeTerm D hu (colour, 0) FieldNormalProduct.identityField exponent vector offset =
        if exponent - 2 * offset + 1 = 0 then
          LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour (-(offset : ℤ) - 1) vector
        else 0 := by
    simp only [negativeTerm, jetScalar, Finset.range_zero, Finset.prod_empty,
      Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, div_one, one_smul, mul_zero, add_zero,
      identity_coefficient]
    split_ifs <;> simp only [map_zero]
  have positive (offset : ℕ) :
      positiveTerm D hu (colour, 0) FieldNormalProduct.identityField exponent vector offset =
        if exponent + 2 * offset + 3 = 0 then
          LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour offset vector
        else 0 := by
    simp only [positiveTerm, jetScalar, Finset.range_zero, Finset.prod_empty,
      Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, div_one, one_smul, mul_zero, add_zero,
      identity_coefficient]
  change (∑ᶠ offset : ℕ, negativeTerm D hu (colour, 0)
      FieldNormalProduct.identityField exponent vector offset) +
      (∑ᶠ offset : ℕ, positiveTerm D hu (colour, 0)
        FieldNormalProduct.identityField exponent vector offset) = _
  simp_rw [negative, positive]
  by_cases odd : exponent % 2 = 1
  · rw [LatticeHalfFock.currentCoeff, if_pos odd]
    change _ = LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour ((-exponent - 3) / 2) vector
    by_cases creation : -1 ≤ exponent
    · let chosen := ((exponent + 1) / 2).toNat
      have exponentChosen : exponent - 2 * (chosen : ℤ) + 1 = 0 := by
        dsimp only [chosen]
        omega
      have currentChosen : -(chosen : ℤ) - 1 = (-exponent - 3) / 2 := by
        dsimp only [chosen]
        omega
      rw [finsum_eq_single _ chosen]
      · have allPositive : ∀ offset : ℕ, exponent + 2 * offset + 3 ≠ 0 := by
          intro offset
          omega
        simp only [if_pos exponentChosen, allPositive, if_false, finsum_zero, add_zero,
          currentChosen]
      · intro offset different
        have outside : exponent - 2 * (offset : ℤ) + 1 ≠ 0 := by omega
        rw [if_neg outside]
    · let chosen := ((-exponent - 3) / 2).toNat
      have exponentChosen : exponent + 2 * (chosen : ℤ) + 3 = 0 := by
        dsimp only [chosen]
        omega
      have currentChosen : (chosen : ℤ) = (-exponent - 3) / 2 := by
        dsimp only [chosen]
        omega
      have allNegative : ∀ offset : ℕ, exponent - 2 * offset + 1 ≠ 0 := by
        intro offset
        omega
      simp only [allNegative, if_false, finsum_zero, zero_add]
      rw [finsum_eq_single _ chosen]
      · rw [if_pos exponentChosen, currentChosen]
      · intro offset different
        have outside : exponent + 2 * (offset : ℤ) + 3 ≠ 0 := by omega
        rw [if_neg outside]
  · have allNegative : ∀ offset : ℕ, exponent - 2 * offset + 1 ≠ 0 := by
      intro offset
      omega
    have allPositive : ∀ offset : ℕ, exponent + 2 * offset + 3 ≠ 0 := by
      intro offset
      omega
    have zeroEnd : LatticeHalfFock.tensorEnd D (ActualGround D hu)
        (0 : Module.End ℂ (Oscillator D)) = 0 :=
      map_zero (LatticeHalfFock.tensorEndLinear D (ActualGround D hu))
    simp only [allNegative, allPositive, if_false, finsum_zero, add_zero,
      LatticeHalfFock.currentCoeff, if_neg odd, zeroEnd, LinearMap.zero_apply]


end
end D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.negativeTerm_finite
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.positiveTerm_finite
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalCoefficient_lower_truncation
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.charged_zero_identity
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalPolynomial_one
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalPolynomial_X
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.shiftLinear_zero
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalInsertion_identity_current
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.flatTerm_support_bound
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.flatTerm_finite
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalSequence_flattened
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalInsertion_commute
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalWord_flattened
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalWord_perm
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField.normalPolynomial_enumerated_expansion
