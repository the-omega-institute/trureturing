/- GID: D5/S3/Arith/Lattices/Klartag/State/RawDataInst2RW2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/RawDataInst2RW2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
import D5.S3.Arith.Lattices.Klartag.State.RawDataInstRW2

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.State.RawDataInst2RW2

open MeasureTheory
open Finset
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainWiring
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupRW2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInstRW2
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2

variable {n : ℕ}

open Classical in
/-- **The chain's window at the reach**: the integer points between `(1−1/n)/α` (exclusive) and
`windowR2 α n − √n/2` (inclusive). -/
noncomputable def shellR (α : ℝ) (n : ℕ) : Finset (Fin n → ℤ) :=
  ((Tiling.finite_ball_integer n (windowR2 α n - Real.sqrt n / 2)).toFinset).filter
    (fun y => (1 - 1 / (n : ℝ)) / α < ‖toE n y‖)

open Classical in
theorem mem_shellR {α : ℝ} {n : ℕ} {y : Fin n → ℤ} :
    y ∈ shellR α n ↔
      ‖toE n y‖ ≤ windowR2 α n - Real.sqrt n / 2 ∧ (1 - 1 / (n : ℝ)) / α < ‖toE n y‖ := by
  rw [shellR, Finset.mem_filter, Set.Finite.mem_toFinset]
  exact Iff.rfl

/-- The inner radius, unscaled, on the reach shell. -/
theorem inner_radiusR {α : ℝ} (hα : 0 < α) {n : ℕ} {y : Fin n → ℤ} (hy : y ∈ shellR α n) :
    1 - 1 / (n : ℝ) < α * ‖toE n y‖ := by
  have h := (mem_shellR.1 hy).2
  rw [div_lt_iff₀ hα] at h
  linarith [h]

/-- `a₀·(α‖toE y‖)² > 1` from the inner radius alone — the window plays no part, so this serves
both lanes. -/
theorem a0C_mul_sq_gt_one_of_inner {α : ℝ} {n : ℕ} (hn : 2 ≤ n) {y : Fin n → ℤ}
    (hr : 1 - 1 / (n : ℝ) < α * ‖toE n y‖) : 1 < a0C n * (α * ‖toE n y‖) ^ 2 := by
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnr
    linarith
  have hsq : (1 - 1 / (n : ℝ)) ^ 2 < (α * ‖toE n y‖) ^ 2 := by nlinarith
  have hbb : (0 : ℝ) < (1 - 1 / (n : ℝ)) ^ 2 := by positivity
  rw [a0C, inv_pow, inv_mul_eq_div, lt_div_iff₀ hbb, one_mul]
  exact hsq

/-- **The seven lattice fields**, for the chain's own `q`, `A₀` and the reach shell. -/
theorem lattice_fieldsR {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 3 ≤ n) :
    (∀ j : (Fin n → ℤ), ∀ i ∈ shellR α n, (0 : ℝ) ≤ ⟪qC α i, qC α j⟫) ∧
    (∀ y ∈ shellR α n, (1 : ℝ) < ⟪A0C n, qC α y⟫) ∧
    (∀ y ∈ shellR α n, y ≠ 0) ∧
    (∀ y ∈ shellR α n, ‖toE n y‖ ≤ windowR2 α n) ∧
    (∀ y ∈ shellR α n, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n) ∧
    (∀ y ∈ shellR α n, 0 < α * ‖toE n y‖) ∧
    (∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ shellR α n,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)) := by
  have hn2 : 2 ≤ n := by omega
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hb : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnr
    linarith
  have hpos : ∀ y ∈ shellR α n, 0 < α * ‖toE n y‖ := fun y hy =>
    lt_trans hb (inner_radiusR hα hy)
  refine ⟨fun j i _ => inner_qUT_nonneg _ _, fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_, fun y hy => ?_, hpos, ?_⟩
  · rw [inner_A0C_qC]
    exact a0C_mul_sq_gt_one_of_inner hn2 (inner_radiusR hα hy)
  · intro hzero
    have h0 : (0 : ℝ) < α * ‖toE n y‖ := hpos y hy
    have hz : ‖toE n y‖ = 0 := by
      rw [hzero, EuclideanSpace.norm_eq]
      simp [Tiling.toE_apply]
    rw [hz, mul_zero] at h0
    exact lt_irrefl 0 h0
  · have := (mem_shellR.1 hy).1
    have hs : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    linarith
  · have := (mem_shellR.1 hy).1
    linarith
  · intro k hk hk0 y hy
    have ht : 0 < (k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n := by
      have h1 : (0 : ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk0
        exact_mod_cast this
      exact mul_pos h1 (TailSideSetup2.stepSizeAdopted2_pos hn)
    have hr0 : 0 < α * ‖toE n y‖ := hpos y hy
    have hgt := a0C_mul_sq_gt_one_of_inner hn2 (inner_radiusR hα hy)
    rw [yOf, div_pos_iff]
    left
    refine ⟨?_, Real.sqrt_pos.2 ht⟩
    rw [sub_pos, inv_lt_iff_one_lt_mul₀ (by positivity)]
    linarith [hgt]

end D5.S3.Arith.Lattices.Klartag.State.RawDataInst2RW2
