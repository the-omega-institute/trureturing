/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainFunctional
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Fixed suffix functionals on full label sets. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainFunctional.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainBlock

/-!
# Fixed suffix functionals on full label sets

The same arbitrary depth bound is used throughout this finite construction.
Labels carry their entire remaining exponent vector; none are projected away.
-/

namespace Erdos7.CappedGain

variable {ι : Type*} [DecidableEq ι]

structure Param where
  p : ℚ
  P : ℚ
  t : ℚ
  p_three : 3 ≤ p
  prime_le : p ≤ P
  t_nonneg : 0 ≤ t
  t_le : t ≤ p - 3

def terminal (depth : ι → ℕ) (A : Finset ι) : ℚ :=
  max (modularLoad (fun x ↦ beta 18 (depth x)) A - 9) 0 / 8

theorem modularLoad_supermodular (w : ι → ℚ) : Supermodular (modularLoad w) := by
  intro A B
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := w)
  dsimp [modularLoad]
  linarith

theorem terminal_increasing (depth : ι → ℕ) : Increasing (terminal depth) := by
  intro A B hAB
  have h := modularLoad_increasing (fun x ↦ beta_nonneg (by norm_num : (1 : ℚ) ≤ 18)
    (depth x)) hAB
  exact div_le_div_of_nonneg_right (max_le_max (sub_le_sub_right h 9) (le_refl 0))
    (by norm_num)

theorem terminal_supermodular (depth : ι → ℕ) : Supermodular (terminal depth) := by
  have hs : Supermodular (fun A ↦ modularLoad (fun x ↦ beta 18 (depth x)) A - 9) := by
    intro A B
    have h := modularLoad_supermodular (fun x ↦ beta 18 (depth x)) A B
    dsimp
    linarith
  have hzero : Supermodular (fun _ : Finset ι ↦ (0 : ℚ)) := by intro A B; norm_num
  have hdiff : Increasing (fun A ↦ (modularLoad (fun x ↦ beta 18 (depth x)) A - 9) - 0) := by
    intro A B hAB
    have h := modularLoad_increasing (fun x ↦ beta_nonneg (by norm_num : (1 : ℚ) ≤ 18)
      (depth x)) hAB
    dsimp
    linarith
  have hmax := supermodular_max_of_increasing_difference hzero hs hdiff
  intro A B
  have h := hmax A B
  dsimp only at h
  dsimp [terminal]
  rw [max_comm (0 : ℚ) (modularLoad (fun x ↦ beta 18 (depth x)) A - 9),
    max_comm (0 : ℚ) (modularLoad (fun x ↦ beta 18 (depth x)) B - 9),
    max_comm (0 : ℚ) (modularLoad (fun x ↦ beta 18 (depth x)) (A ∩ B) - 9),
    max_comm (0 : ℚ) (modularLoad (fun x ↦ beta 18 (depth x)) (A ∪ B) - 9)] at h
  linarith

@[simp] theorem terminal_empty (depth : ι → ℕ) : terminal depth ∅ = 0 := by
  norm_num [terminal, modularLoad]

theorem terminal_nonneg (depth : ι → ℕ) (A : Finset ι) : 0 ≤ terminal depth A := by
  exact div_nonneg (le_max_right _ _) (by norm_num)

/-- A label is future if its suffix after the current coordinate is nonzero. -/
def Future {n : ℕ} (depth : ι → Fin (n + 1) → ℕ) (x : ι) : Prop :=
  ∃ j : Fin n, depth x j.succ ≠ 0

instance {n : ℕ} (depth : ι → Fin (n + 1) → ℕ) (x : ι) : Decidable (Future depth x) := by
  unfold Future
  infer_instance

noncomputable def endingWeight {n : ℕ} (v : Param) (depth : ι → Fin (n + 1) → ℕ)
    (x : ι) : ℚ := if Future depth x then 0 else beta v.P (depth x 0)

theorem endingWeight_nonneg {n : ℕ} (v : Param) (depth : ι → Fin (n + 1) → ℕ)
    (x : ι) : 0 ≤ endingWeight v depth x := by
  classical
  unfold endingWeight
  split_ifs
  · exact le_refl _
  · exact beta_nonneg (by linarith [v.p_three, v.prime_le]) _

theorem endingWeight_future {n : ℕ} (v : Param) (depth : ι → Fin (n + 1) → ℕ)
    (x : ι) (hx : Future depth x) : endingWeight v depth x = 0 := by
  classical
  simp [endingWeight, hx]

/-- There are `n` distorted coordinates followed by one terminal coordinate. -/
noncomputable def value : (n : ℕ) → (Fin n → Param) →
    (ι → Fin (n + 1) → ℕ) → ℕ → Finset ι → ℚ
  | 0, _, depth, _, A => terminal (fun x ↦ depth x 0) A
  | n + 1, params, depth, D, A => by
      classical
      exact block (params 0).p (params 0).t D (fun x ↦ depth x 0)
        (Future depth) (endingWeight (params 0) depth)
        (value n (Fin.tail params) (fun x ↦ Fin.tail (depth x)) D) A

theorem value_properties (n : ℕ) (params : Fin n → Param)
    (depth : ι → Fin (n + 1) → ℕ) (D : ℕ) :
    Increasing (value n params depth D) ∧ Supermodular (value n params depth D) ∧
      value n params depth D ∅ = 0 := by
  classical
  induction n with
  | zero => exact ⟨terminal_increasing _, terminal_supermodular _, terminal_empty _⟩
  | succ n ih =>
    have hnext := ih (Fin.tail params) (fun x ↦ Fin.tail (depth x))
    refine ⟨?_, ?_, ?_⟩
    · exact block_increasing (params 0).p_three (params 0).t_le D _ _ _
        (endingWeight_nonneg _ _) hnext.1
    · exact block_supermodular (params 0).p_three (params 0).t_le D _ _ _
        (endingWeight_nonneg _ _) (endingWeight_future _ _) hnext.2.1 hnext.1
    · exact block_empty (params 0).p_three (params 0).t_nonneg (params 0).t_le D _ _ _ hnext.2.2

theorem value_nonneg (n : ℕ) (params : Fin n → Param)
    (depth : ι → Fin (n + 1) → ℕ) (D : ℕ) (A : Finset ι) :
    0 ≤ value n params depth D A := by
  have h := (value_properties n params depth D).1 (Finset.empty_subset A)
  rwa [(value_properties n params depth D).2.2] at h

end Erdos7.CappedGain
