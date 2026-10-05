/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStep
import D5.S3.Arith.Lattices.Klartag.Walk.ChainInputDom
import D5.S3.Arith.Lattices.Klartag.Completion.WindowR2

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
open scoped ENNReal NNReal

/-- **Proposition 4.1 at step `k`, in the profile's language.**  From the `Φ` form of the padded
tail at horizon `k·h` to the `profileAt` form `ContactIntegrated.integrated_count_le` consumes. -/
theorem tail_at_stepRW2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α hstep : ℝ} {N : ℕ} (C : ℕ → Ω → Finset (Fin n → ℤ))
    (W : Finset (Fin n → ℤ))
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))
    (hPhi : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      μ {ω | y ∈ C k ω}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))))
    (hzero : ∀ y ∈ W, μ.real {ω | y ∈ C 0 ω} = 0) :
    ∀ k, k < N → ∀ y ∈ W,
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * (if k = 0 then 0 else
            profileAt (a0C n) α (windowR2 α n) n ((k : ℝ) * hstep) ‖toE n y‖) := by
  intro k hk y hy'
  by_cases hk0 : k = 0
  · subst hk0; rw [if_pos rfl, mul_zero, hzero y hy']
  · rw [if_neg hk0,
      profileAt_eq_Phi (hwin y hy') (hr y hy') (hy k hk hk0 y hy')]
    exact measureReal_le_of_le (by
      have := Phi_nonneg (hy k hk hk0 y hy'); linarith) (hPhi k hk hk0 y hy')

/-- The per-step profile: Proposition 4.1's value at step time `k·h`, zero at `k = 0`. -/
noncomputable def profStepRW2 (α : ℝ) (n : ℕ) (hstep : ℝ) (y : Fin n → ℤ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else profileAt (a0C n) α (windowR2 α n) n ((k : ℝ) * hstep) ‖toE n y‖

theorem intWeight_leRW2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α hstep : ℝ} {N : ℕ} (hα : 0 < α) (hh : 0 < hstep)
    (hNT : (N : ℝ) * hstep = ChainDrift.horizon n)
    (C : ℕ → Ω → Finset (Fin n → ℤ)) {y : Fin n → ℤ}
    (htail : ∀ k, k < N → μ.real {ω | y ∈ C k ω} ≤ 4 * profStepRW2 α n hstep y k) :
    ContactIntegrated.intWeight μ C hstep N y
      ≤ 4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowR2 α n) n t ‖toE n y‖ := by
  have hstep_le : ContactIntegrated.intWeight μ C hstep N y
      ≤ ∑ k ∈ Finset.range N, hstep * (4 * profStepRW2 α n hstep y k) := by
    rw [ContactIntegrated.intWeight]
    exact Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (htail k (Finset.mem_range.1 hk)) hh.le)
  have hpull : ∑ k ∈ Finset.range N, hstep * (4 * profStepRW2 α n hstep y k)
      = 4 * ∑ k ∈ Finset.range N, hstep * profStepRW2 α n hstep y k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
  have hR := riemann_lower_le (f := fun t => profileAt (a0C n) α (windowR2 α n) n t ‖toE n y‖)
    (hstep := hstep) (N := N) hh
    (fun t => profile_nonneg _ _)
    (fun s t hs hst => profile_mono_time hs hst _)
    (fun b => integrableOn_profile_time (‖toE n y‖ + Real.sqrt n / 2))
  rw [hNT] at hR
  refine le_trans hstep_le ?_
  rw [hpull]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  simpa [profStepRW2] using hR

/-- **`ChainRaw2RW2.tail`, discharged.**  The per-step tail of §1, summed by §2 and §3, at the
adopted `e = 7` discretisation. -/
theorem tail_of_stepsRW2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α : ℝ} (hn : 3 ≤ n) (hα : 0 < α) (C : ℕ → Ω → Finset (Fin n → ℤ))
    {y : Fin n → ℤ}
    (hsteps : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n →
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * profStepRW2 α n (ParamsAdopted2.stepSizeAdopted2 n) y k) :
    ENNReal.ofReal (ContactIntegrated.intWeight μ C
        (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
      ≤ ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowR2 α n) n t ‖toE n y‖) :=
  ENNReal.ofReal_le_ofReal
    (intWeight_leRW2 hα (adopted_stepSize_pos hn) (adopted_horizon hn) C hsteps)

structure ChainRaw2RW2 (p n : ℕ) where
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  R : ℝ
  R_nonneg : 0 ≤ R
  R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4
  window_lt_p : windowR2 alpha n < (p : ℝ)
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  supp_ne_zero : ∀ y ∈ supp, y ≠ 0
  supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowR2 alpha n
  /-- The only probabilistic input; `tail_of_stepsRW2` supplies it. -/
  tail : ∀ y ∈ supp, w y ≤ ENNReal.ofReal
    (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
      profileAt (a0C n) alpha (windowR2 alpha n) n t ‖toE n y‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

noncomputable def chainRaw2_of_chainRW2 {p n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hn : 3 ≤ n)
    (C : ℕ → Ω → Finset (Fin n → ℤ))
    (alpha : ℝ) (alpha_pos : 0 < alpha)
    (alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (R : ℝ) (R_nonneg : 0 ≤ R) (R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)) (R_lt_p : R < (p : ℝ))
    (tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4)
    (window_lt_p : windowR2 alpha n < (p : ℝ))
    (supp : Finset (Fin n → ℤ)) (supp_ne_zero : ∀ y ∈ supp, y ≠ 0)
    (supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowR2 alpha n)
    (hsteps : ∀ y ∈ supp, ∀ k, k < ParamsAdopted2.numStepsAdopted2 n →
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * profStepRW2 alpha n (ParamsAdopted2.stepSizeAdopted2 n) y k)
    (arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)) :
    ChainRaw2RW2 p n where
  alpha := alpha
  alpha_pos := alpha_pos
  alpha_norm := alpha_norm
  R := R
  R_nonneg := R_nonneg
  R_scaled := R_scaled
  R_lt_p := R_lt_p
  tiling_defect := tiling_defect
  window_lt_p := window_lt_p
  w := fun y => ENNReal.ofReal (ContactIntegrated.intWeight μ C
    (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
  supp := supp
  supp_ne_zero := supp_ne_zero
  supp_radius := supp_radius
  tail := fun y hy => tail_of_stepsRW2 hn alpha_pos C (hsteps y hy)
  arith := arith

end D5.S3.Arith.Lattices.Klartag
