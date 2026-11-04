/- GID: D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockFockNormalField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise finite arbitrary-word normal fields and the actual finite-charge source extension. -/

/- Actual dependent ground and tensor modules use the original jet/mode conventions.
   Supplier extraction SHA256 da8469c7f1a7b7c8b9f6be6c48a7e83f9f5154d57c5309958d9806342273ecea.

The imported half-Fock current/tensor implementation retains its original notices:
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Additional actual half-integer matrix implementation copyright (c) 2026.
Released under Apache 2.0.
Finite support, contraction and induction architecture adapted from
VirasoroProject 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 through the completed
trureturing PolynomialFock sources at bfd9ff0f15397a4fb933f36d701a60d325d84b08.
DN math/9808088v1, section 3.2, pp.12--14; rank/16 on p.19, proof of 3.13(3),
attributed there to FLM. BK math/0402315v1 (4.4), pp.10--13 (4.23)--(4.38).
These are inherited supplier attributions, not a claim of authorship of this extraction.
-/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.RingTheory.MvPolynomial.Basic

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

/- A nonzero normal term forces a coefficient of the seed at or above the
finite minimum over its possible right actions. The cutoff is internal data
supplied by tensor_current_truncation, never a premise of the final field. -/
private theorem flatTerm_seed_lower (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (exponent : ℤ)
    (vector : ActualTensor D hu) (cutoff : ℕ)
    (bound : ∀ colour mode, (cutoff : ℤ) ≤ mode →
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector = 0)
    (modes : ModeTuple D word)
    (nonzero : flatTerm D hu field word exponent vector modes ≠ 0) :
    flatLower D hu field word vector cutoff ≤
      exponent + 2 * modeSum D word modes + jetShift D word := by
  classical
  have upper := flatTerm_upper D hu field word exponent vector cutoff bound modes nonzero
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
  exact chargedBound

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
  have chargedBound := flatTerm_seed_lower D hu field word exponent vector cutoff bound modes nonzero
  have totalBound : min (flatLower D hu field word vector cutoff - exponent - jetShift D word) 0 ≤
      modeSum D word modes := by omega
  have lower := modeSum_lower D word modes cutoff _ (by omega) weakUpper totalBound
  rw [Finset.mem_coe, mem_modeBox]
  exact allModes_and D word modes _ _ lower weakUpper

/- proof_shape: flatTerm_finite: content
   admission_basis: escape-witness
   escape_witness: The finite right-action code and a finite minimum of seed
   orders bound every original mode of a nonzero arbitrary-word term. This is
   support after application to one vector, not support in Module.End.
   Literature status: classical twisted normal-field construction; no novelty. -/
theorem flatTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (exponent : ℤ)
    (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (flatTerm D hu field word exponent vector) := by
  obtain ⟨cutoff, bound⟩ :=
    LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector
  exact (modeBox D word
    (min (flatLower D hu field word vector cutoff - exponent - jetShift D word) 0 -
      (word.length : ℤ) * cutoff) cutoff).finite_toSet.subset
        (flatTerm_support_bound D hu field word exponent vector cutoff bound)

/-- The mode sum is taken in the actual tensor module separately for each input.
There is deliberately no finsum with values in Module.End. -/
def wordCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (field : NativeField D hu)
    (word : List (Index D)) (exponent : ℤ) : Module.End ℂ (ActualTensor D hu) where
  toFun vector := ∑ᶠ modes : ModeTuple D word,
    flatTerm D hu field word exponent vector modes
  map_add' first second := by
    have terms : flatTerm D hu field word exponent (first + second) =
        fun modes => flatTerm D hu field word exponent first modes +
          flatTerm D hu field word exponent second modes := by
      funext modes
      exact (flatCoefficient D hu field word modes exponent).map_add first second
    rw [terms]
    exact finsum_add_distrib (flatTerm_finite D hu field word exponent first)
      (flatTerm_finite D hu field word exponent second)
  map_smul' scalar vector := by
    have terms : flatTerm D hu field word exponent (scalar • vector) =
        fun modes => scalar • flatTerm D hu field word exponent vector modes := by
      funext modes
      exact (flatCoefficient D hu field word modes exponent).map_smul scalar vector
    rw [terms]
    exact (smul_finsum' scalar (flatTerm_finite D hu field word exponent vector)).symm

private def wordLower (D : LatticeData) (hu : IsUnit D.G.det) (field : NativeField D hu)
    (word : List (Index D)) (vector : ActualTensor D hu) (cutoff : ℕ) : ℤ :=
  flatLower D hu field word vector cutoff -
    2 * (word.length : ℤ) * cutoff - jetShift D word

private theorem flatTerm_exponent_lower (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (exponent : ℤ)
    (vector : ActualTensor D hu) (cutoff : ℕ)
    (bound : ∀ colour mode, (cutoff : ℤ) ≤ mode →
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector = 0)
    (modes : ModeTuple D word)
    (nonzero : flatTerm D hu field word exponent vector modes ≠ 0) :
    wordLower D hu field word vector cutoff ≤ exponent := by
  have upper := flatTerm_upper D hu field word exponent vector cutoff bound modes nonzero
  have weakUpper := allModes_mono D word modes _ (fun mode => mode ≤ (cutoff : ℤ))
    (fun mode hypothesis => le_of_lt hypothesis) upper
  have sumUpper := modeSum_upper D word modes cutoff weakUpper
  have seedLower := flatTerm_seed_lower D hu field word exponent vector cutoff bound modes nonzero
  dsimp only [wordLower]
  linarith

private theorem wordCoefficient_vanish (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (vector : ActualTensor D hu)
    (cutoff : ℕ)
    (bound : ∀ colour mode, (cutoff : ℤ) ≤ mode →
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector = 0)
    (exponent : ℤ) (below : exponent < wordLower D hu field word vector cutoff) :
    wordCoefficient D hu field word exponent vector = 0 := by
  have zeroTerm : flatTerm D hu field word exponent vector = 0 := by
    funext modes
    by_contra nonzero
    exact (not_le_of_gt below)
      (flatTerm_exponent_lower D hu field word exponent vector cutoff bound modes nonzero)
  change (∑ᶠ modes : ModeTuple D word, flatTerm D hu field word exponent vector modes) = 0
  rw [zeroTerm]
  simp

/- proof_shape: wordCoefficient_lower_truncation: content
   admission_basis: escape-witness
   escape_witness: For each actual input, the original current cutoff and the
   finite right-action minimum give e >= flatLower - 2*length*cutoff - jetShift
   for every nonzero summand, uniformly over all mode tuples. -/
theorem wordCoefficient_lower_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (vector : ActualTensor D hu) :
    ∃ lower : ℤ, ∀ exponent : ℤ, exponent < lower →
      wordCoefficient D hu field word exponent vector = 0 := by
  obtain ⟨cutoff, bound⟩ :=
    LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector
  exact ⟨wordLower D hu field word vector cutoff,
    wordCoefficient_vanish D hu field word vector cutoff bound⟩

/-- An actual Hahn-valued linear field of every finite word and every seed. -/
def wordField (D : LatticeData) (hu : IsUnit D.G.det) (field : NativeField D hu)
    (word : List (Index D)) : NativeField D hu :=
  HVertexOperator.of_coeff (wordCoefficient D hu field word) (by
    intro vector
    obtain ⟨lower, bound⟩ := wordCoefficient_lower_truncation D hu field word vector
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨lower, ?_⟩
    intro exponent nonzero
    by_contra below
    exact nonzero (bound exponent (by omega)))

/- proof_shape: wordField_coefficient: bind-only
   consumed by sourceField_coefficient; the substantive construction and
   lower-truncation proof are wordCoefficient and the preceding estimate. -/
theorem wordField_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (word : List (Index D)) (exponent : ℤ)
    (vector : ActualTensor D hu) :
    (wordField D hu field word).coeff exponent vector =
      ∑ᶠ modes : ModeTuple D word, flatTerm D hu field word exponent vector modes := by
  rw [wordField, HVertexOperator.coeff_of_coeff]
  rfl

/-- The seed is exactly the existing actual charged tensor field. -/
def chargedWordField (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (word : List (Index D)) : NativeField D hu :=
  wordField D hu (chargedField D hu charge) word

/-- Canonical finite occurrence enumeration, with repetitions retained. -/
def occurrences (D : LatticeData) (monomial : Index D →₀ ℕ) : List (Index D) :=
  monomial.toMultiset.toList

/-- Extend actual normal fields over all oscillator polynomials by their native basis. -/
def polynomialField (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    Oscillator D →ₗ[ℂ] NativeField D hu :=
  (MvPolynomial.basisMonomials (Index D) ℂ).constr ℂ
    (fun monomial => chargedWordField D hu charge (occurrences D monomial))

/-- The normal supplier on every finite-charge ordinary source, acting on the
actual twisted tensor module. This is not the Delta-corrected twisted field. -/
def sourceField (D : LatticeData) (hu : IsUnit D.G.det) :
    Carrier D →ₗ[ℂ] NativeField D hu :=
  Finsupp.lsum ℂ (polynomialField D hu)

private theorem sourceField_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) :
    sourceField D hu source = ∑ charge ∈ source.support,
      ∑ monomial ∈ ((MvPolynomial.basisMonomials (Index D) ℂ).repr (source charge)).support,
        ((MvPolynomial.basisMonomials (Index D) ℂ).repr (source charge) monomial) •
          chargedWordField D hu charge (occurrences D monomial) := by
  simp only [sourceField, Finsupp.lsum_apply, Finsupp.sum, polynomialField,
    Module.Basis.constr_apply]

def coefficientAt (D : LatticeData) (hu : IsUnit D.G.det)
    (exponent : ℤ) (vector : ActualTensor D hu) : NativeField D hu →ₗ[ℂ] ActualTensor D hu where
  toFun field := field.coeff exponent vector
  map_add' first second := by simp
  map_smul' scalar field := by simp

/- proof_shape: sourceField_coefficient: bind-only
   consumed by sourceField_lower_truncation. Finite source sums are taken in
   the already constructed field space; only the innermost mode sum is a finsum,
   and it is taken pointwise in ActualTensor. -/
theorem sourceField_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) :
    (sourceField D hu source).coeff exponent vector =
      ∑ charge ∈ source.support,
        ∑ monomial ∈ ((MvPolynomial.basisMonomials (Index D) ℂ).repr (source charge)).support,
          ((MvPolynomial.basisMonomials (Index D) ℂ).repr (source charge) monomial) •
            ∑ᶠ modes : ModeTuple D (occurrences D monomial),
              flatTerm D hu (chargedField D hu charge) (occurrences D monomial)
                exponent vector modes := by
  change coefficientAt D hu exponent vector (sourceField D hu source) = _
  rw [sourceField_expansion]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro charge chargeMember
  apply Finset.sum_congr rfl
  intro monomial monomialMember
  change _ • (chargedWordField D hu charge (occurrences D monomial)).coeff exponent vector = _
  rw [chargedWordField, wordField_coefficient]

private def polynomialLower (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (polynomial : Oscillator D) (vector : ActualTensor D hu) (cutoff : ℕ) : ℤ := by
  classical
  exact (insert 0 (((MvPolynomial.basisMonomials (Index D) ℂ).repr polynomial).support.image
    (fun monomial => wordLower D hu (chargedField D hu charge)
      (occurrences D monomial) vector cutoff))).min' (by simp)

private def sourceLower (D : LatticeData) (hu : IsUnit D.G.det) (source : Carrier D)
    (vector : ActualTensor D hu) (cutoff : ℕ) : ℤ := by
  classical
  exact (insert 0 (source.support.image
    (fun charge => polynomialLower D hu charge (source charge) vector cutoff))).min' (by simp)

/- proof_shape: sourceField_lower_truncation: content
   admission_basis: escape-witness
   escape_witness: A common original-current cutoff for the actual target state
   combines with finite minima over all supported charge/monomial source pairs.
   The resulting bound kills every pointwise word sum, including inhomogeneous
   sources and arbitrary negative integer exponents. No bound is assumed. -/
theorem sourceField_lower_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) (vector : ActualTensor D hu) :
    ∃ lower : ℤ, ∀ exponent : ℤ, exponent < lower →
      (sourceField D hu source).coeff exponent vector = 0 := by
  classical
  obtain ⟨cutoff, bound⟩ :=
    LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector
  refine ⟨sourceLower D hu source vector cutoff, ?_⟩
  intro exponent below
  rw [sourceField_coefficient]
  apply Finset.sum_eq_zero
  intro charge chargeMember
  have chargeLower : sourceLower D hu source vector cutoff ≤
      polynomialLower D hu charge (source charge) vector cutoff := by
    apply Finset.min'_le
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨charge, chargeMember, rfl⟩)
  apply Finset.sum_eq_zero
  intro monomial monomialMember
  have monomialLower : polynomialLower D hu charge (source charge) vector cutoff ≤
      wordLower D hu (chargedField D hu charge) (occurrences D monomial) vector cutoff := by
    apply Finset.min'_le
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨monomial, monomialMember, rfl⟩)
  have zero := wordCoefficient_vanish D hu (chargedField D hu charge)
    (occurrences D monomial) vector cutoff bound exponent (by omega)
  change _ • wordCoefficient D hu (chargedField D hu charge)
    (occurrences D monomial) exponent vector = 0
  rw [zero, smul_zero]

private theorem singleton_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (i : Index D) (e : ℤ) (v : ActualTensor D hu) :
    (wordField D hu F [i]).coeff e v =
      ∑ᶠ m : ℤ, flatTerm D hu F [i] e v (m, ()) := by
  rw [wordField_coefficient, finsum_curry _ (flatTerm_finite D hu F [i] e v)]
  apply finsum_congr
  intro m
  exact finsum_unique _

private theorem wordField_cons (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (i : Index D) (w : List (Index D)) :
    wordField D hu F (i :: w) = wordField D hu (wordField D hu F w) [i] := by
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro v
  rw [wordField_coefficient, singleton_coefficient,
    finsum_curry _ (flatTerm_finite D hu F (i :: w) e v)]
  apply finsum_congr
  intro m
  by_cases h : m < 0
  · simp only [flatTerm, flatCoefficient, if_pos h, Module.End.mul_apply]
    rw [wordField_coefficient, map_finsum _ (flatTerm_finite D hu F w _ v)]
    rfl
  · simp only [flatTerm, flatCoefficient, if_neg h, Module.End.mul_apply]
    exact (wordField_coefficient D hu F w _ (jetCurrent D hu i m v)).symm

private theorem jetCurrent_same_sign (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Index D) (l r : ℤ)
    (h : (l < 0 ∧ r < 0) ∨ (0 ≤ l ∧ 0 ≤ r)) :
    jetCurrent D hu i l * jetCurrent D hu j r =
      jetCurrent D hu j r * jetCurrent D hu i l := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, jetCurrent, LinearMap.smul_apply, map_smul]
  rw [tensor_current_same_sign D hu i.1 j.1 l r h v, smul_comm]

private theorem flatCoefficient_swap (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (i j : Index D) (w : List (Index D))
    (l r : ℤ) (t : ModeTuple D w) (e : ℤ) :
    flatCoefficient D hu F (i :: j :: w) (l, r, t) e =
      flatCoefficient D hu F (j :: i :: w) (r, l, t) e := by
  have shift : e + 2 * l + 2 * i.2 + 3 + 2 * r + 2 * j.2 + 3 =
      e + 2 * r + 2 * j.2 + 3 + 2 * l + 2 * i.2 + 3 := by ring
  simp only [flatCoefficient]
  rw [shift]
  by_cases hl : l < 0 <;> by_cases hr : r < 0
  · simp only [if_pos hl, if_pos hr, ← mul_assoc]
    rw [jetCurrent_same_sign D hu i j l r (Or.inl ⟨hl, hr⟩)]
  · simp only [if_pos hl, if_neg hr, mul_assoc]
  · simp only [if_neg hl, if_pos hr, mul_assoc]
  · simp only [if_neg hl, if_neg hr, mul_assoc]
    rw [jetCurrent_same_sign D hu j i r l (Or.inr ⟨by omega, by omega⟩)]

private theorem wordField_swap (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (i j : Index D) (w : List (Index D)) :
    wordField D hu F (i :: j :: w) = wordField D hu F (j :: i :: w) := by
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro v
  rw [wordField_coefficient, wordField_coefficient]
  apply finsum_eq_of_bijective (fun m : ℤ × ℤ × ModeTuple D w => (m.2.1, m.1, m.2.2))
  · constructor
    · rintro ⟨l, r, t⟩ ⟨l', r', t'⟩ h
      simpa only [Prod.mk.injEq, and_comm, and_left_comm, and_assoc] using h
    · rintro ⟨r, l, t⟩
      exact ⟨(l, r, t), rfl⟩
  · rintro ⟨l, r, t⟩
    exact congrArg (fun A : Module.End ℂ (ActualTensor D hu) => A v)
      (flatCoefficient_swap D hu F i j w l r t e)

private theorem wordField_perm (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (w u : List (Index D)) (h : w.Perm u) :
    wordField D hu F w = wordField D hu F u := by
  induction h with
  | nil => rfl
  | cons i h ih =>
    exact (wordField_cons D hu F i _).trans
      ((congrArg (fun G : NativeField D hu => wordField D hu G [i]) ih).trans
        (wordField_cons D hu F i _).symm)
  | swap i j w => exact wordField_swap D hu F j i w
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The original singleton word field, as a linear operation on its seed. -/
def singletonLinear (D : LatticeData) (hu : IsUnit D.G.det) (i : Index D) :
    Module.End ℂ (NativeField D hu) where
  toFun F := wordField D hu F [i]
  map_add' F G := by
    apply HVertexOperator.coeff_inj
    funext e
    apply LinearMap.ext
    intro v
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    rw [wordField_coefficient, wordField_coefficient, wordField_coefficient,
      ← finsum_add_distrib (flatTerm_finite D hu F [i] e v)
        (flatTerm_finite D hu G [i] e v)]
    apply finsum_congr
    rintro ⟨m, t⟩
    simp only [flatTerm, flatCoefficient]
    split_ifs <;> simp [Module.End.mul_apply]
  map_smul' c F := by
    apply HVertexOperator.coeff_inj
    funext e
    apply LinearMap.ext
    intro v
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply, LinearMap.smul_apply]
    rw [wordField_coefficient, wordField_coefficient,
      smul_finsum' c (flatTerm_finite D hu F [i] e v)]
    apply finsum_congr
    rintro ⟨m, t⟩
    simp only [flatTerm, flatCoefficient]
    split_ifs <;> simp [Module.End.mul_apply]

private theorem polynomialField_monomial (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (a : Index D →₀ ℕ) :
    polynomialField D hu q (MvPolynomial.monomial a 1) =
      wordField D hu (chargedField D hu q) (occurrences D a) :=
  (MvPolynomial.basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun a => chargedWordField D hu q (occurrences D a)) a

theorem polynomialField_monomial_public (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (a : Index D →₀ ℕ) :
    polynomialField D hu q (MvPolynomial.monomial a 1) =
      wordField D hu (chargedField D hu q) (occurrences D a) :=
  polynomialField_monomial D hu q a

/-- Multiplication of the source by one oscillator is actual singleton insertion.
The occurrence list is used only up to permutation, with multiplicities retained. -/
theorem polynomialField_X_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (i : Index D) (p : Oscillator D) :
    polynomialField D hu q (MvPolynomial.X i * p) =
      singletonLinear D hu i (polynomialField D hu q p) := by
  have basis (a : Index D →₀ ℕ) :
      polynomialField D hu q (MvPolynomial.X i * MvPolynomial.monomial a 1) =
        singletonLinear D hu i (polynomialField D hu q (MvPolynomial.monomial a 1)) := by
    have enumeration : (i :: occurrences D a).Perm
        (occurrences D (Finsupp.single i 1 + a)) := by
      apply Multiset.coe_eq_coe.mp
      simp [occurrences, Finsupp.toMultiset_add, Finsupp.toMultiset_single,
        ← Multiset.cons_coe, Multiset.coe_toList, add_comm]
    rw [show (MvPolynomial.X i : Oscillator D) * MvPolynomial.monomial a (1 : ℂ) =
        MvPolynomial.monomial (Finsupp.single i 1 + a) (1 : ℂ) by
          simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul],
      polynomialField_monomial, polynomialField_monomial]
    rw [← wordField_perm D hu (chargedField D hu q) _ _ enumeration, wordField_cons]
    rfl
  have maps : (polynomialField D hu q).comp (LinearMap.mulLeft ℂ (MvPolynomial.X i)) =
      (singletonLinear D hu i).comp (polynomialField D hu q) := by
    apply (MvPolynomial.basisMonomials (Index D) ℂ).ext
    intro a
    exact basis a
  exact LinearMap.congr_fun maps p

end
end D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField


namespace D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open scoped BigOperators

/-- Pointwise signed-mode formula for the canonical singleton operation. -/
theorem singletonLinear_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (i : Index D) (e : ℤ) (v : ActualTensor D hu) :
    (singletonLinear D hu i F).coeff e v =
      ∑ᶠ m : ℤ, flatTerm D hu F [i] e v (m, ()) :=
  singleton_coefficient D hu F i e v

/-- Canonical cons decomposition through singleton insertion. -/
theorem wordField_cons_singleton (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (i : Index D) (w : List (Index D)) :
    wordField D hu F (i :: w) = singletonLinear D hu i (wordField D hu F w) :=
  wordField_cons D hu F i w

end D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
