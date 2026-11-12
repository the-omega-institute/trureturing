/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionRows
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Generic full-source rows and charge inventory for resonant insertion. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionWord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth PeriodicShorteningArithmetic
open scoped BigOperators

def resonantFirst (k seed : ℕ) : Fin (k + 1) → ℤ :=
  Fin.lastCases 0 (actualSource k seed)

def resonantCharge (k seed : ℕ) : Fin (k + 1) → ℤ :=
  Fin.lastCases 0 (charge k seed)

def resonantWeight (k : ℕ) : Fin (k + 1) → ℤ :=
  Fin.lastCases 0 (fun i => (2 : ℤ) ^ i.val)

def resonantEar (k : ℕ) (j : Fin (k + 1)) : ℤ :=
  if j.val = k then 1 else 0

theorem resonant_source_rows {k seed : ℕ} (hdim : 2 ≤ k)
    (hroom : seed ≤ 2 ^ (k - 1) - 1) (j : Fin (k + 1)) :
    0 ≤ resonantCharge k seed j ∧
    resonantFirst k seed j = seed * resonantWeight k j -
      modulus k * resonantCharge k seed j ∧
    actualSource (k + 1) (2 * seed) j =
      2 * resonantFirst k seed j - resonantCharge k seed j +
        seed * resonantEar k j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [resonantFirst, resonantCharge, resonantWeight,
      Fin.lastCases_last, resonantEar, Fin.val_last, if_pos]
    have hsecond := digit_data (k + 1) (2 * seed) (by omega)
      (by
        have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by
          rw [show k = (k - 1) + 1 by omega, pow_succ]
          simp [mul_comm]
        have hp' : 2 ^ (k + 1 - 1) = 2 * 2 ^ (k - 1) := by
          rw [show k + 1 - 1 = k by omega, hp]
        omega) (Fin.last k)
    have hc : charge (k + 1) (2 * seed) (Fin.last k) = seed := by
      simp [charge]
    rw [hc] at hsecond
    simp only [Fin.val_last, pow_succ] at hsecond
    refine ⟨?_, ?_, ?_⟩
    · simp
    · ring
    · convert hsecond.2.1 using 1 <;> norm_num [Nat.cast_mul] <;> ring
  · have h := digit_data k seed hdim hroom i
    have heq : actualSource (k + 1) (2 * seed) i.castSucc =
        actualSource (k + 1) seed ⟨i.val + 1, by omega⟩ := by
      unfold actualSource
      simp only [Fin.val_castSucc, Fin.val_mk, pow_succ]
      congr 1
      norm_num [Nat.cast_mul]
      ring
    simp only [resonantFirst, resonantCharge, resonantWeight,
      Fin.lastCases_castSucc, resonantEar, Fin.val_castSucc,
      if_neg (show i.val ≠ k by omega)]
    rw [heq, h.2.2]
    exact ⟨h.1, by simpa [modulus, mul_comm] using h.2.1, by ring⟩

theorem resonant_prefix_rows {k seed : ℕ} (hdim : 2 ≤ k)
    (hroom : seed ≤ 2 ^ (k - 1) - 1) (word : List (Fin (k + 1))) :
    (word.map (resonantFirst k seed)).sum =
        seed * (word.map (resonantWeight k)).sum -
          modulus k * (word.map (resonantCharge k seed)).sum ∧
    (word.map (actualSource (k + 1) (2 * seed))).sum =
      2 * (word.map (resonantFirst k seed)).sum -
        (word.map (resonantCharge k seed)).sum +
        seed * (word.map (resonantEar k)).sum := by
  induction word with
  | nil => simp
  | cons j word ih =>
    have h := resonant_source_rows hdim hroom j
    simp only [List.map_cons, List.sum_cons]
    constructor
    · rw [h.2.1, ih.1]
      ring
    · rw [h.2.2, ih.2]
      ring

theorem resonant_charge_total {k seed : ℕ} (hdim : 2 ≤ k)
    (hroom : seed ≤ 2 ^ (k - 1) - 1) :
    ((List.finRange (k + 1)).map (resonantCharge k seed)).sum = seed := by
  rw [List.finRange_succ_last, List.map_append, List.sum_append]
  simp only [List.map_map, Function.comp_def, resonantCharge,
    Fin.lastCases_castSucc, Fin.lastCases_last, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← List.sum_toFinset _ (List.nodup_finRange k), List.toFinset_finRange]
  exact charge_sum k seed hdim hroom

theorem resonant_ear_total (k : ℕ) :
    ((List.finRange (k + 1)).map (resonantEar k)).sum = 1 := by
  rw [List.finRange_succ_last, List.map_append, List.sum_append]
  have hz : (List.finRange k).map (fun i => resonantEar k i.castSucc) =
      List.replicate k (0 : ℤ) := by
    have h := List.map_eq_replicate_iff.mpr
      (fun i (_ : i ∈ List.finRange k) =>
        show resonantEar k i.castSucc = (0 : ℤ) by
          simp [resonantEar, ne_of_lt i.isLt])
    simpa only [List.length_finRange] using h
  simp only [List.map_map, Function.comp_def]
  rw [hz]
  simp [resonantEar]

theorem resonant_prefix_inventory {k seed : ℕ} (hdim : 2 ≤ k)
    (hroom : seed ≤ 2 ^ (k - 1) - 1)
    (word : List (Fin (k + 1))) (n : ℕ)
    (hw : word.Perm (List.finRange (k + 1))) :
    (0 ≤ ((word.take n).map (resonantCharge k seed)).sum ∧
      ((word.take n).map (resonantCharge k seed)).sum ≤ seed) ∧
    (0 ≤ ((word.take n).map (resonantEar k)).sum ∧
      ((word.take n).map (resonantEar k)).sum ≤ 1) := by
  have hnonneg (f : Fin (k + 1) → ℤ) (hf : ∀ j, 0 ≤ f j) :
      0 ≤ ((word.take n).map f).sum ∧
        ((word.take n).map f).sum ≤ (word.map f).sum := by
    have h0 (l : List (Fin (k + 1))) : 0 ≤ (l.map f).sum := by
      apply List.sum_nonneg
      intro z hz
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
      exact hf j
    have he := congrArg (fun l => (l.map f).sum)
      (List.take_append_drop n word)
    simp only [List.map_append, List.sum_append] at he
    exact ⟨h0 _, by linarith [h0 (word.drop n)]⟩
  have hc := hnonneg (resonantCharge k seed)
    (fun j => (resonant_source_rows hdim hroom j).1)
  have he := hnonneg (resonantEar k)
    (fun j => by simp [resonantEar]; split_ifs <;> norm_num)
  rw [(hw.map _).sum_eq, resonant_charge_total hdim hroom] at hc
  rw [(hw.map _).sum_eq, resonant_ear_total k] at he
  exact ⟨hc, he⟩

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
