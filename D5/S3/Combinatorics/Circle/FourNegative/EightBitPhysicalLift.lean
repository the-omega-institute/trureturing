import D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Endpoint
import D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift

/- GID: D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Corrected eight-bit physical insertion algebra and the complete
   (2,2,2,d) family witness, reusing the native uniform physical theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
open D5.S3.Combinatorics.Circle.SparseNecklaceRounding
open scoped BigOperators

/-! The target label map used by the insertion-only lift.  The first eight
labels are the inserted physical labels and every old label is shifted by
eight. -/
def liftOldLabel {k : ℕ} (i : Fin (k + 1)) : Fin (k + 9) :=
  ⟨i.val + 8, by have hi := i.isLt; omega⟩

def liftFreshLabel (k : ℕ) : Fin (k + 9) :=
  liftOldLabel (Fin.last k)

def liftNewLabel {k : ℕ} (i : Fin 8) : Fin (k + 9) :=
  ⟨i.val, by omega⟩

def insertionMask (T : ℕ) : ℕ := T % 256

def targetN (k : ℕ) : ℤ := modulus (k + 8)

def targetH (k : ℕ) : ℤ := 256 * (modulus k / 2) + 255

def canonicalFirst (k : ℕ) (F C : ℤ) (T : ℕ) : ℤ :=
  256 * F - 255 * C + 85 * (insertionMask T)

def canonicalSecond (k : ℕ) (Y C : ℤ) (T : ℕ) (b : Bool) : ℤ :=
  256 * Y - 255 * C - 21675 * (if b then 1 else 0) +
    170 * (insertionMask T)

def insertionDeletion {k : ℕ} (w : List (Fin (k + 9))) : List (Fin (k + 1)) :=
  w.filterMap (fun i => if h : 8 ≤ i.val then
    some ⟨i.val - 8, by omega⟩ else none)

def insertionMaskUpTo (T : ℕ) (i : Fin 8) : ℕ :=
  insertionMask (T + 2 ^ i.val)

/-! A literal insertion-only word.  The orientation function chooses the
order inside each of the eight old/new pairs; every old occurrence is mapped
by `liftOldLabel`, so the old relative order is built into the definition. -/
def physicalLiftWord {k : ℕ} (sigma : List (Fin (k + 1)))
    (orientation : Fin 8 → Bool) : List (Fin (k + 9)) :=
  sigma.flatMap (fun j =>
    if hj : j.val < 8 then
      let i : Fin 8 := ⟨j.val, hj⟩
      if orientation i then
        [liftOldLabel j, liftNewLabel i]
      else
        [liftNewLabel i, liftOldLabel j]
    else
      [liftOldLabel j])

theorem insertionDeletion_physicalLiftWord {k : ℕ}
    (sigma : List (Fin (k + 1))) (orientation : Fin 8 → Bool) :
    insertionDeletion (physicalLiftWord sigma orientation) = sigma := by
  induction sigma with
  | nil => simp [physicalLiftWord, insertionDeletion]
  | cons j js ih =>
    change insertionDeletion (_ ++ physicalLiftWord js orientation) = j :: js
    by_cases hj : j.val < 8
    · let i : Fin 8 := ⟨j.val, hj⟩
      simp only [dif_pos hj]
      have hb : insertionDeletion
          (if orientation i then [liftOldLabel j, liftNewLabel i]
           else [liftNewLabel i, liftOldLabel j]) = [j] := by
        by_cases ho : orientation i <;>
          simp [ho, insertionDeletion, liftOldLabel, liftNewLabel, hj, i]
      simp only [insertionDeletion, List.filterMap_append]
      have hb' := hb
      simp only [insertionDeletion] at hb'
      have ih' := ih
      simp only [insertionDeletion] at ih'
      rw [hb', ih']
      rfl
    · simp only [dif_neg hj]
      have hb : insertionDeletion [liftOldLabel j] = [j] := by
        simp [insertionDeletion, liftOldLabel, hj]
      simp only [insertionDeletion, List.filterMap_append]
      have hb' := hb
      simp only [insertionDeletion] at hb'
      have ih' := ih
      simp only [insertionDeletion] at ih'
      rw [hb', ih']
      rfl

theorem target_bounds (k : ℕ) (hk : 2 ≤ k) :
    targetN k = 256 * modulus k + 255 ∧
    targetH k = 256 * (modulus k / 2) + 255 := by
  unfold targetN targetH
  constructor
  · unfold modulus
    rw [show k + 8 = k + 8 by rfl, pow_add]
    norm_num
    ring
  · rfl

theorem insertion_mask_range (T : ℕ) :
    0 ≤ (insertionMask T : ℤ) ∧ (insertionMask T : ℤ) ≤ 255 := by
  unfold insertionMask
  have h := Nat.mod_lt T (by decide : 0 < 256)
  omega

theorem canonical_endpoint_formula (k : ℕ) (F Y C : ℤ) (T : ℕ) (b : Bool)
    (hRel : Y = 2 * F - C + 85 * (if b then 1 else 0)) :
    canonicalSecond k Y C T b =
      2 * canonicalFirst k F C T - C + 85 * (if b then 1 else 0) := by
  unfold canonicalFirst canonicalSecond
  rw [hRel]
  by_cases hb : b
  · simp [hb]
    ring
  · simp [hb]
    ring

theorem canonical_endpoint_lift
    (k : ℕ) (F Y C : ℤ) (T : ℕ) (b : Bool) (r : ℤ)
    (hF : 0 ≤ F ∧ F ≤ modulus k / 2)
    (hY : 0 ≤ Y ∧ Y ≤ modulus k)
    (hC : 0 ≤ C ∧ C ≤ 85)
    (hRel : Y = 2 * F - C + 85 * (if b then 1 else 0))
    (hr : (insertionMask T : ℤ) + 3 * F - 3 * C = 256 * r)
    (hr0 : 0 ≤ r)
    (hroomF : 21760 * r ≤ targetH k - modulus k / 2)
    (hroomY : 43520 * r ≤ targetN k - modulus k) :
    0 ≤ canonicalFirst k F C T ∧
      canonicalFirst k F C T ≤ targetH k ∧
      0 ≤ canonicalSecond k Y C T b ∧
      canonicalSecond k Y C T b ≤ targetN k := by
  have hu : 0 ≤ (insertionMask T : ℤ) := (insertion_mask_range T).1
  have hu' : (insertionMask T : ℤ) ≤ 255 := (insertion_mask_range T).2
  have hFform : canonicalFirst k F C T = F + 21760 * r := by
    unfold canonicalFirst
    calc
      256 * F - 255 * C + 85 * (insertionMask T : ℤ) =
          F + 85 * ((insertionMask T : ℤ) + 3 * F - 3 * C) := by ring
      _ = F + 21760 * r := by rw [hr]; ring
  have hYform : canonicalSecond k Y C T b = Y + 43520 * r := by
    calc
      canonicalSecond k Y C T b =
          2 * canonicalFirst k F C T - C + 85 * (if b then 1 else 0) :=
        canonical_endpoint_formula k F Y C T b hRel
      _ = 2 * (F + 21760 * r) - C + 85 * (if b then 1 else 0) := by rw [hFform]
      _ = Y + 43520 * r := by rw [hRel]; ring
  rw [hFform, hYform]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

/-! The four-gap family used by the eight verified seeds. -/
def fourGaps (d : ℕ) : Fin 4 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => d

theorem fourGaps_period (d : ℕ) : period (fourGaps d) = d + 6 := by
  simp [period, gapList, fourGaps, Fin.sum_univ_succ]
  omega

theorem fourGaps_seed (d : ℕ) : necklaceSeed (fourGaps d) = 85 := by
  classical
  have hprefix (j : Fin 4) :
      (∑ q ∈ Finset.univ.filter (fun q : Fin 4 => q < j), fourGaps d q) =
        match j.val with
        | 0 => 0
        | 1 => 2
        | 2 => 4
        | 3 => 6
        | _ => 0 := by
    fin_cases j <;>
      simp only [Finset.sum_filter] <;>
      norm_num [fourGaps, Fin.sum_univ_succ]
  simp only [necklaceSeed, Fin.sum_univ_succ]
  rw [hprefix, hprefix, hprefix, hprefix]
  norm_num

private theorem fourGaps_legal (d : ℕ) (hd : 2 ≤ d) :
    ∀ j : Fin 4, 2 ≤ fourGaps d j := by
  intro j
  fin_cases j <;> simp [fourGaps] <;> omega

private theorem originalOrder_of_checks {k t : ℕ} (w : List (Fin k))
    (hp : w.Perm (List.finRange k))
    (hsum : (w.map (actualSource k t)).sum = 0)
    (hprefix : ∀ n : ℕ, n ≤ w.length →
      ((w.take n).map (actualSource k t)).sum ∈
        Set.Icc (0 : ℤ) (modulus k / 2)) :
    OriginalOrder k t w := by
  refine ⟨hp, hsum, ?_⟩
  intro n
  by_cases hn : n ≤ w.length
  · exact hprefix n hn
  · have ht : w.take n = w := List.take_of_length_le (by omega)
    rw [ht, hsum]
    have hm : 0 ≤ modulus k := by
      unfold modulus
      have : (1 : ℤ) ≤ 2 ^ k := by
        exact_mod_cast (Nat.one_le_two_pow (n := k))
      omega
    have hhalf : 0 ≤ modulus k / 2 := Int.ediv_nonneg hm (by norm_num)
    simp [Set.mem_Icc, hhalf]

private theorem seed_d2 :
    ∃ sigma : List (Fin 8), ∃ cut : ℕ, cut ≤ 8 ∧
      OriginalOrder 8 85 sigma ∧
      OriginalOrder 9 170 (earWord 8 sigma cut) := by
  let sigma : List (Fin 8) := [0,1,2,3,4,5,6,7]
  refine ⟨sigma, 1, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    · intro n hn
      have hn' : n ≤ 8 := by simpa [sigma] using hn
      interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 8 sigma 1)
    · decide
    · decide
    · intro n hn
      have hn' : n ≤ 9 := by simpa [sigma, earWord] using hn
      interval_cases n <;> decide

private theorem seed_d3 :
    ∃ sigma : List (Fin 9), ∃ cut : ℕ, cut ≤ 9 ∧
      OriginalOrder 9 85 sigma ∧
      OriginalOrder 10 170 (earWord 9 sigma cut) := by
  let sigma : List (Fin 9) := [0,1,2,3,4,5,6,7,8]
  refine ⟨sigma, 8, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 9 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 9 sigma 8)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 10 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d4 :
    ∃ sigma : List (Fin 10), ∃ cut : ℕ, cut ≤ 10 ∧
      OriginalOrder 10 85 sigma ∧
      OriginalOrder 11 170 (earWord 10 sigma cut) := by
  let sigma : List (Fin 10) := [0,2,3,4,5,6,7,1,8,9]
  refine ⟨sigma, 9, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 10 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 10 sigma 9)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 11 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d5 :
    ∃ sigma : List (Fin 11), ∃ cut : ℕ, cut ≤ 11 ∧
      OriginalOrder 11 85 sigma ∧
      OriginalOrder 12 170 (earWord 11 sigma cut) := by
  let sigma : List (Fin 11) := [0,1,3,4,5,6,7,8,2,9,10]
  refine ⟨sigma, 10, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 11 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 11 sigma 10)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 12 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d6 :
    ∃ sigma : List (Fin 12), ∃ cut : ℕ, cut ≤ 12 ∧
      OriginalOrder 12 85 sigma ∧
      OriginalOrder 13 170 (earWord 12 sigma cut) := by
  let sigma : List (Fin 12) := [0,1,2,4,5,6,7,8,9,3,10,11]
  refine ⟨sigma, 11, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 12 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 12 sigma 11)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 13 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d7 :
    ∃ sigma : List (Fin 13), ∃ cut : ℕ, cut ≤ 13 ∧
      OriginalOrder 13 85 sigma ∧
      OriginalOrder 14 170 (earWord 13 sigma cut) := by
  let sigma : List (Fin 13) := [0,1,2,3,5,6,7,8,9,10,4,11,12]
  refine ⟨sigma, 12, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 13 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 13 sigma 12)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 14 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d8 :
    ∃ sigma : List (Fin 14), ∃ cut : ℕ, cut ≤ 14 ∧
      OriginalOrder 14 85 sigma ∧
      OriginalOrder 15 170 (earWord 14 sigma cut) := by
  let sigma : List (Fin 14) := [0,1,2,3,4,6,7,8,9,10,11,5,12,13]
  refine ⟨sigma, 13, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 14 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 14 sigma 13)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 15 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d9 :
    ∃ sigma : List (Fin 15), ∃ cut : ℕ, cut ≤ 15 ∧
      OriginalOrder 15 85 sigma ∧
      OriginalOrder 16 170 (earWord 15 sigma cut) := by
  let sigma : List (Fin 15) := [0,1,2,3,4,5,7,8,9,10,11,12,6,13,14]
  refine ⟨sigma, 14, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 15 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 15 sigma 14)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 16 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

/-! The native p-minus-one theorem supplies the exact physical four-gap
rounding contract used by the corrected lift.  The remaining step from this
contract to a literal `OriginalOrder` joint word is kept separate so the
corner data cannot be mistaken for a completed lift. -/
theorem physical_rounding_family_contract (d : ℕ) (hd : 2 ≤ d) :
    PhysicalRounding (fourGaps d) := by
  exact uniform_sparse_necklace_rounding 4 (by decide : 1 ≤ 4)
    (fourGaps d) (fourGaps_legal d hd)

theorem fourGaps_eventual (d : ℕ) (hd : 9 ≤ d) :
    ∃ sigma : List (Fin (6 + d)), ∃ cut : ℕ, cut ≤ 6 + d ∧
      OriginalOrder (6 + d) 85 sigma ∧
      OriginalOrder (6 + d + 1) 170 (earWord (6 + d) sigma cut) := by
  exact actualSource_four_negative_eventual_joint_lift 2 2 2 d
    (by decide) (by decide) (by decide) hd

private theorem transport_pair {k l : ℕ} (hkl : k = l)
    (h : ∃ sigma : List (Fin k), ∃ cut : ℕ, cut ≤ k ∧
      OriginalOrder k 85 sigma ∧
      OriginalOrder (k + 1) 170 (earWord k sigma cut)) :
    ∃ sigma : List (Fin l), ∃ cut : ℕ, cut ≤ l ∧
      OriginalOrder l 85 sigma ∧
      OriginalOrder (l + 1) 170 (earWord l sigma cut) := by
  subst l
  exact h

theorem fourGaps_family :
    ∀ d : ℕ, 2 ≤ d →
      ∃ sigma : List (Fin (d + 6)), ∃ cut : ℕ, cut ≤ d + 6 ∧
        OriginalOrder (d + 6) 85 sigma ∧
        OriginalOrder (d + 7) 170 (earWord (d + 6) sigma cut) := by
  intro d hd
  by_cases h9 : 9 ≤ d
  · have h := fourGaps_eventual d h9
    exact transport_pair (by omega) h
  · have hd8 : d ≤ 8 := by omega
    interval_cases d <;>
      first
      | exact seed_d2
      | exact seed_d3
      | exact seed_d4
      | exact seed_d5
      | exact seed_d6
      | exact seed_d7
      | exact seed_d8

end D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift
