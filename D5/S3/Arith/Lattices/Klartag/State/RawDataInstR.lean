/- GID: D5/S3/Arith/Lattices/Klartag/State/RawDataInstR
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/RawDataInstR
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.State.RawDataInst
import D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupR

set_option linter.unusedSectionVars false

open MeasureTheory
open Finset
open scoped RealInnerProductSpace

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.State.RawDataInstR

open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupR
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR

variable {n : ℕ}

/-- **`RawDataR`, eight numeric fields proved.**  The seven `q`/`W`/`A₀` fields are hypotheses, as
in `RawDataInst.rawData_of_lattice`; `R` is Klartag's `(1−1/n)/α`. -/
theorem rawData_of_latticeR (hn : 2073600 ≤ n) {p : ℕ} {α : ℝ} (hαpos : 0 < α) (hp2 : 2 ≤ p)
    (hαnorm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (hαsmall : α ≤ 1 / (2 * (n : ℝ) * Real.sqrt n))
    (hM : max (2 * reachNum n) (max 1 (Real.sqrt n)) ≤ α * (p : ℝ))
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (Increments.UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (Increments.UT n)}
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hne0 : ∀ y ∈ W, y ≠ 0) (hrad : ∀ y ∈ W, ‖toE n y‖ ≤ windowR α n)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)) :
    RawDataR p n α ((1 - 1 / (n : ℝ)) / α) q W A₀ := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hnr
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hDpos : (0 : ℝ) < 2 * (n : ℝ) * Real.sqrt n := by positivity
  have hmul : α * (2 * (n : ℝ) * Real.sqrt n) ≤ 1 := (le_div_iff₀ hDpos).1 hαsmall
  have hone : (1 : ℝ) ≤ α * (p : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have h2w : 2 * reachNum n ≤ α * (p : ℝ) := le_trans (le_max_left _ _) hM
  have hfrac : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hsnn : (0 : ℝ) ≤ α * Real.sqrt n := by positivity
  have hsn : α * Real.sqrt n ≤ 1 := by nlinarith [hmul, hsnn, hn2r, hsq1]
  refine ⟨hq, hA₀, hαpos, hαnorm, by positivity, ?_, ?_, ?_, ?_, hne0, hrad, hwin, hr, hy, ?_⟩
  · rw [mul_div_cancel₀ _ hαpos.ne']
  · rw [div_lt_iff₀ hαpos]
    calc 1 - 1 / (n : ℝ) < 1 := by
          have hinv : (0 : ℝ) < 1 / (n : ℝ) := by positivity
          linarith
      _ ≤ α * (p : ℝ) := hone
      _ = (p : ℝ) * α := mul_comm _ _
  · have hrw : (n : ℝ) * (α * Real.sqrt n / 2) = α * (2 * (n : ℝ) * Real.sqrt n) / 4 := by ring
    rw [hrw]; linarith [hmul]
  · exact windowR_lt_p hn hαpos h2w hsn
  ·
    have hκ : 0 < kappa n := kappa_pos hn0
    have hpn : (p : ℝ) ^ n = ((p ^ n : ℕ) : ℝ) := by push_cast; ring
    have hκp : kappa n * (p : ℝ) = (α * (p : ℝ)) ^ n := by
      rw [mul_pow, show n = (n - 1) + 1 by omega, pow_succ (p : ℝ) (n - 1),
        show (n - 1) + 1 = n by omega, ← hαnorm]
      push_cast; ring
    have hαn : (n : ℝ) * α ^ n ≤ 1 / 2 := by
      have h1 : α ≤ 1 / (2 * (n : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hmul, hsq1]
      have h2 : α ^ n ≤ (1 / (2 * (n : ℝ))) ^ n := pow_le_pow_left₀ hαpos.le h1 n
      have h3 : (1 / (2 * (n : ℝ))) ^ n ≤ (1 / (2 * (n : ℝ))) ^ 2 := by
        apply pow_le_pow_of_le_one (by positivity) _ hn2
        rw [div_le_one (by positivity)]; linarith
      have h4 : (1 / (2 * (n : ℝ))) ^ 2 = 1 / (4 * (n : ℝ) ^ 2) := by field_simp; ring
      have h5 : α ^ n ≤ 1 / (4 * (n : ℝ) ^ 2) := by rw [← h4]; linarith [h2, h3]
      have h6 : (n : ℝ) * α ^ n ≤ (n : ℝ) * (1 / (4 * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h5 (by linarith)
      have h7 : (n : ℝ) * (1 / (4 * (n : ℝ) ^ 2)) = 1 / (4 * (n : ℝ)) := by field_simp
      have h8 : 1 / (4 * (n : ℝ)) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith [h6, h7, h8]
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpn2 : (2 : ℝ) ≤ (p : ℝ) ^ n := by
      have ha : (2 : ℝ) ^ n ≤ (p : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) hp2r n
      have hb : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hkey : (n : ℝ) * (kappa n * (p : ℝ)) + 1 ≤ (p : ℝ) ^ n := by
      have hid : (n : ℝ) * (kappa n * (p : ℝ)) = ((n : ℝ) * α ^ n) * (p : ℝ) ^ n := by
        rw [hκp, mul_pow]; ring
      rw [hid]
      nlinarith [hαn, hpn2]
    have hfin : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2)
        < 8 * ((p : ℝ) ^ n - 1) := by
      have h8 : 8 - 8 / (n : ℝ) ^ 2 < 8 := by
        have hq8 : (0 : ℝ) < 8 / (n : ℝ) ^ 2 := by positivity
        linarith
      have hpos1 : 0 < (n : ℝ) * kappa n * ((p : ℝ) - 1) := by
        have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        positivity
      nlinarith [hkey, h8, hpos1, hκ, hppos]
    rw [hpn] at hfin ⊢
    exact hfin

end D5.S3.Arith.Lattices.Klartag.State.RawDataInstR
