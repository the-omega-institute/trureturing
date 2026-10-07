/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped7
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped7
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6
import D5.S3.Arith.Lattices.Klartag.Gaussian.GaussianMaximal3
import Mathlib
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeData

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

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped7

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped4
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open scoped ENNReal RealInnerProductSpace

section Numeric

variable {n : ℕ}

theorem log_le_four_sqrt_sqrt (hn : 1 ≤ n) :
    Real.log n ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have ht0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_pos.2 hs0
  have h1 : Real.log (Real.sqrt (Real.sqrt (n : ℝ))) ≤ Real.sqrt (Real.sqrt (n : ℝ)) - 1 :=
    Real.log_le_sub_one_of_pos ht0
  have h2 : Real.log (Real.sqrt (n : ℝ)) = Real.log n / 2 := Real.log_sqrt hn0.le
  have h3 : Real.log (Real.sqrt (Real.sqrt (n : ℝ))) = Real.log (Real.sqrt (n : ℝ)) / 2 :=
    Real.log_sqrt (Real.sqrt_nonneg _)
  linarith

theorem sqrt_ge_1440 (hn : 2073600 ≤ n) : (1440 : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [show (1440 : ℝ) = Real.sqrt (1440 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num; linarith)

theorem sqrt_sqrt_ge (hn : 2073600 ≤ n) : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hs := sqrt_ge_1440 hn
  rw [show (37 : ℝ) = Real.sqrt (37 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith)

theorem log_div_le (hn : 2073600 ≤ n) : Real.log n / (n : ℝ) ≤ (1 / 96 : ℝ) ^ 2 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  set t := Real.sqrt (Real.sqrt (n : ℝ)) with ht
  have ht37 : (37 : ℝ) ≤ t := sqrt_sqrt_ge hn
  have ht0 : (0 : ℝ) < t := by linarith
  have hsq : t ^ 2 = Real.sqrt (n : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hn4 : t ^ 4 = (n : ℝ) := by
    have h : (t ^ 2) ^ 2 = (n : ℝ) := by rw [hsq]; exact Real.sq_sqrt hn0.le
    nlinarith [h]
  have hlog : Real.log n ≤ 4 * t := log_le_four_sqrt_sqrt (by omega)
  rw [div_le_iff₀ hn0]
  have hkey : 4 * t ≤ (1 / 96 : ℝ) ^ 2 * (n : ℝ) := by
    rw [← hn4]
    nlinarith [ht37, ht0, pow_pos ht0 3]
  linarith

theorem r0Adopted_nonneg : 0 ≤ DriftStopped6.r0Adopted n := by
  rw [DriftStopped6.r0Adopted]; positivity

theorem etaAdopted_nonneg : 0 ≤ DriftStopped6.etaAdopted n := by
  rw [DriftStopped6.etaAdopted]; exact Real.sqrt_nonneg _

theorem r0Adopted_le (hn : 2073600 ≤ n) : DriftStopped6.r0Adopted n ≤ 1 / 4 := by
  have h := log_div_le hn
  have hs : Real.sqrt (Real.log n / (n : ℝ)) ≤ 1 / 96 := by
    rw [show (1 : ℝ) / 96 = Real.sqrt ((1 / 96) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h
  rw [DriftStopped6.r0Adopted]
  linarith

theorem c3_mul_eta_le (hn : 2073600 ≤ n) :
    DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n ≤ 1 / 4 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have heta : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 :=
    ParamsAdopted2.eta2_le hn3
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hstep : DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n
      ≤ (n : ℝ) ^ 2 * (Real.sqrt 2 / (n : ℝ) ^ 3) := by
    rw [DriftStopped6.c3Adopted]
    exact mul_le_mul_of_nonneg_left heta (by positivity)
  have hval : (n : ℝ) ^ 2 * (Real.sqrt 2 / (n : ℝ) ^ 3) = Real.sqrt 2 / (n : ℝ) := by
    field_simp
  rw [hval] at hstep
  have hfin : Real.sqrt 2 / (n : ℝ) ≤ 2 / (2073600 : ℝ) := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith [h2, hnR, Real.sqrt_nonneg (2 : ℝ)]
  linarith

theorem one_le_a0C (hn : 2 ≤ n) : (1 : ℝ) ≤ a0C n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : 1 / (n : ℝ) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hpos : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have h1 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by linarith
  have h2 : 1 - 1 / (n : ℝ) ≤ 1 := by linarith
  have hmul : (1 - 1 / (n : ℝ))⁻¹ * (1 - 1 / (n : ℝ)) = 1 := inv_mul_cancel₀ (ne_of_gt h1)
  have hxi : (0 : ℝ) < (1 - 1 / (n : ℝ))⁻¹ := inv_pos.2 h1
  have h3 : (1 : ℝ) ≤ (1 - 1 / (n : ℝ))⁻¹ := by nlinarith [hmul, hxi, h2]
  rw [a0C]
  nlinarith [h3]

theorem sqrt_hd_le (hn : 2073600 ≤ n) :
    Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
      ≤ 1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hd : (Fintype.card (UT n) : ℝ) ≤ (n : ℝ) ^ 2 := Discharge.card_UT_le_sq (by omega)
  have hh : ParamsAdopted2.stepSizeAdopted2 n ≤ 1 / (n : ℝ) ^ 9 :=
    ParamsAdopted2.stepSizeAdopted2_le hn3
  have hh0 : 0 ≤ ParamsAdopted2.stepSizeAdopted2 n := ParamsAdopted2.stepSizeAdopted2_nonneg hn3
  have hprod : ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)
      ≤ 1 / (n : ℝ) ^ 7 := by
    have h1 : ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)
        ≤ (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 :=
      mul_le_mul hh hd (Nat.cast_nonneg _) (by positivity)
    have h2 : (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 = 1 / (n : ℝ) ^ 7 := by field_simp
    linarith
  have hrepr : (1 : ℝ) / (n : ℝ) ^ 7 = (1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) ^ 2 := by
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
    field_simp
    nlinarith [hsq, hn0]
  calc Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
      ≤ Real.sqrt ((1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) ^ 2) := by
        rw [← hrepr]; exact Real.sqrt_le_sqrt hprod
    _ = 1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := Real.sqrt_sq (by positivity)

theorem B_adopted_le' (hn : 2073600 ≤ n) : B_adopted n ≤ 5 / (n : ℝ) ^ 3 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hlogn : Real.log n ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hn0
    linarith
  have hsl : Real.sqrt (Real.log n) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hlogn
  have hhd := sqrt_hd_le hn
  have hhd0 : 0 ≤ Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)) :=
    Real.sqrt_nonneg _
  have hmain : 5 * Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
      * Real.sqrt (Real.log n) ≤ 5 / (n : ℝ) ^ 3 := by
    have h1 : 5 * Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
        * Real.sqrt (Real.log n)
        ≤ 5 * (1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) * Real.sqrt (n : ℝ) := by
      have hA : Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
          * Real.sqrt (Real.log n)
          ≤ (1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) * Real.sqrt (n : ℝ) :=
        mul_le_mul hhd hsl (Real.sqrt_nonneg _) (by positivity)
      linarith
    have h2 : 5 * (1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) * Real.sqrt (n : ℝ)
        = 5 / (n : ℝ) ^ 3 := by field_simp
    linarith
  exact le_trans (B_adopted_le hn) hmain

theorem B_adopted_nonneg (hn : 2073600 ≤ n) : 0 ≤ B_adopted n := by
  have hn3 : 3 ≤ n := by omega
  refine le_trans ?_ (le_max_left _ _)
  have hc : 0 < cAdopted n := cAdopted_pos hn3
  positivity

end Numeric

section Window

end Window

section Residual

end Residual

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped7
