/- GID: D5/S3/Arith/Lattices/Klartag/Completion/AdoptedConstants95
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/AdoptedConstants95
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.TruncSumMean

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.AdoptedConstants95

open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling

variable {n : ℕ}

theorem a0C_sub_one_le (hn : 3 ≤ n) : a0C n - 1 ≤ 4 / (n : ℝ) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hu : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hn0]; linarith
  have hune : (1 : ℝ) - 1 / (n : ℝ) ≠ 0 := ne_of_gt hu
  rw [a0C, ← sub_nonneg]
  have hkey : 4 / (n : ℝ) - ((1 - 1 / (n : ℝ))⁻¹ ^ 2 - 1)
      = (2 * (n : ℝ) ^ 2 - 7 * (n : ℝ) + 4) / ((n : ℝ) * ((n : ℝ) - 1) ^ 2) := by
    have hn1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
    field_simp
    ring
  rw [hkey]
  have hnum : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 - 7 * (n : ℝ) + 4 := by nlinarith [hn3]
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) ^ 2 := by
    have : (0 : ℝ) < ((n : ℝ) - 1) ^ 2 := by nlinarith [hn3]
    positivity
  positivity

theorem four_div_le_r0 (hn : 3 ≤ n) : 4 / (n : ℝ) ≤ DriftStopped6.r0Adopted n := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hq : (0 : ℝ) ≤ Real.log n / (n : ℝ) := by positivity
  have hsqrt : 1 / (6 * (n : ℝ)) ≤ Real.sqrt (Real.log n / (n : ℝ)) := by
    have hsq : (1 / (6 * (n : ℝ))) ^ 2 ≤ Real.log n / (n : ℝ) := by
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) hn0]
      have : (1 : ℝ) * (n : ℝ) ≤ Real.log n * (6 * (n : ℝ)) ^ 2 := by nlinarith [hlog, hn3]
      linarith
    have h0 : (0 : ℝ) ≤ 1 / (6 * (n : ℝ)) := by positivity
    calc 1 / (6 * (n : ℝ)) = Real.sqrt ((1 / (6 * (n : ℝ))) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (Real.log n / (n : ℝ)) := Real.sqrt_le_sqrt hsq
  rw [DriftStopped6.r0Adopted]
  have : 4 / (n : ℝ) = 24 * (1 / (6 * (n : ℝ))) := by field_simp; ring
  rw [this]
  linarith [hsqrt]

theorem mAt_le_one (hn : 3 ≤ n) {c₃ : ℝ} (hc₃ : 0 ≤ c₃) :
    GoodPathBounds.mAt n c₃ ≤ 1 := by
  have h1 := a0C_sub_one_le (n := n) hn
  have h2 := four_div_le_r0 (n := n) hn
  have h3 : (0 : ℝ) ≤ c₃ * DriftStopped6.etaAdopted n :=
    mul_nonneg hc₃ (DriftStopped7.etaAdopted_nonneg (n := n))
  rw [GoodPathBounds.mAt]
  linarith

/-- **`κ ≥ 1/2`**, `hLb_of_bounds`'s first hypothesis. -/
theorem kappa_ge_half (hn : 2073600 ≤ n) {c₃ rr : ℝ} (hc₃ : 0 ≤ c₃)
    (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) (hrr : 0 ≤ rr) :
    1 / 2 ≤ (1 / 2 + 2 * rr) / GoodPathBounds.mAt n c₃ ^ 2 := by
  have hhalf := GoodPathBounds.half_le_mAt hn hc₃η
  have hm0 : (0 : ℝ) < GoodPathBounds.mAt n c₃ := by linarith
  have hle := mAt_le_one (n := n) (by omega) hc₃
  have hsq : GoodPathBounds.mAt n c₃ ^ 2 ≤ 1 := by nlinarith [hm0, hle]
  have hsq0 : (0 : ℝ) < GoodPathBounds.mAt n c₃ ^ 2 := by positivity
  rw [le_div_iff₀ hsq0]
  nlinarith [hsq, hrr, hsq0]

theorem logDet_A0C_eq (hn : 3 ≤ n) :
    ChainWiring.logDet (A0C n) = (n : ℝ) * Real.log (a0C n) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha0 : (0 : ℝ) < a0C n := by
    have := DriftStopped7.one_le_a0C (n := n) (by omega); linarith
  rw [ChainWiring.logDet, StateSupply.symMat_A0C n, Matrix.det_smul, Matrix.det_one, mul_one,
    Real.log_pow]
  simp [Fintype.card_fin]

theorem logDet_A0C_le (hn : 3 ≤ n) : ChainWiring.logDet (A0C n) ≤ 3 := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hu : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hn0]; linarith

  have hlogu : -Real.log (1 - 1 / (n : ℝ)) ≤ 1 / ((n : ℝ) - 1) := by
    have h := Real.log_le_sub_one_of_pos (x := (1 - 1 / (n : ℝ))⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have hid : (1 - 1 / (n : ℝ))⁻¹ - 1 = 1 / ((n : ℝ) - 1) := by
      have hn1 : (n : ℝ) - 1 ≠ 0 := by intro hz; nlinarith
      field_simp
      ring
    linarith [h, hid.le, hid.ge]
  have ha0log : Real.log (a0C n) ≤ 2 / ((n : ℝ) - 1) := by
    rw [a0C, Real.log_pow, Real.log_inv]
    have : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [this]
    have h2 : (2 : ℝ) / ((n : ℝ) - 1) = 2 * (1 / ((n : ℝ) - 1)) := by ring
    rw [h2]
    linarith [hlogu]
  have hmul : (n : ℝ) * Real.log (a0C n) ≤ (n : ℝ) * (2 / ((n : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left ha0log (by linarith)
  have hfin : (n : ℝ) * (2 / ((n : ℝ) - 1)) ≤ 3 := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 1)]
    nlinarith [hn3]
  rw [logDet_A0C_eq hn]
  linarith

end D5.S3.Arith.Lattices.Klartag.Completion.AdoptedConstants95
