/- GID: D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/ChainDrift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.Walk.Chain

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Walk.ChainDrift

open MeasureTheory
open Finset
open scoped ENNReal

/-- **The telescoped drift bound.**  A one-step decrease with an error term sums to a bound on the
terminal value.  This is the discrete Riemann sum that replaces `-(1/2)∫₀^T δ_s ds`. -/
theorem telescope {D drift err : ℕ → ℝ} {m : ℕ}
    (hstep : ∀ k, k < m → D (k + 1) ≤ D k - drift k + err k) :
    D m ≤ D 0 - ∑ k ∈ range m, drift k + ∑ k ∈ range m, err k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := ih fun k hk => hstep k (hk.trans (Nat.lt_succ_self m))
    have h2 := hstep m (Nat.lt_succ_self m)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- If a conditional expectation is dominated a.e., the expectations are ordered. -/
theorem integral_le_of_condExp_le {m : MeasurableSpace Ω} (hm : m ≤ m0) [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (_hf : Integrable f μ) (hg : Integrable g μ)
    (h : μ[f|m] ≤ᵐ[μ] g) : ∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ := by
  have h1 : ∫ ω, (μ[f|m]) ω ∂μ = ∫ ω, f ω ∂μ := integral_condExp hm
  rw [← h1]
  exact integral_mono_ae integrable_condExp hg h

structure DriftInputs (μ : Measure Ω) (ℱ : ℕ → MeasurableSpace Ω) (D N err : ℕ → Ω → ℝ)
    (κ : ℝ) (m : ℕ) : Prop where
  /-- the filtration is coarser than the ambient σ-algebra -/
  le : ∀ k, ℱ k ≤ m0

  step : ∀ k, k < m → μ[D (k + 1)|ℱ k] ≤ᵐ[μ] fun ω => D k ω - κ * N k ω + err k ω
  intD : ∀ k, k ≤ m → Integrable (D k) μ
  intN : ∀ k, k < m → Integrable (N k) μ
  interr : ∀ k, k < m → Integrable (err k) μ

variable {ℱ : ℕ → MeasurableSpace Ω} {D N err : ℕ → Ω → ℝ} {κ : ℝ} {m : ℕ}

/-- One step, integrated. -/
theorem integral_step [IsFiniteMeasure μ] (h : DriftInputs μ ℱ D N err κ m) {k : ℕ}
    (hk : k < m) :
    ∫ ω, D (k + 1) ω ∂μ ≤ ∫ ω, D k ω ∂μ - κ * ∫ ω, N k ω ∂μ + ∫ ω, err k ω ∂μ := by
  have hint1 : Integrable (fun ω => D k ω - κ * N k ω) μ :=
    (h.intD k hk.le).sub ((h.intN k hk).const_mul κ)
  have hint : Integrable (fun ω => D k ω - κ * N k ω + err k ω) μ := hint1.add (h.interr k hk)
  have hmain := integral_le_of_condExp_le (h.le k) (h.intD (k + 1) hk) hint (h.step k hk)
  have heq : ∫ ω, (D k ω - κ * N k ω + err k ω) ∂μ
      = ∫ ω, D k ω ∂μ - κ * ∫ ω, N k ω ∂μ + ∫ ω, err k ω ∂μ := by
    rw [integral_add hint1 (h.interr k hk),
      integral_sub (h.intD k hk.le) ((h.intN k hk).const_mul κ), integral_const_mul]
  rwa [heq] at hmain

/-- **The telescoped drift bound, integrated** (Klartag Lemma 3.3, discrete form). -/
theorem drift_bound [IsFiniteMeasure μ] (h : DriftInputs μ ℱ D N err κ m) :
    ∫ ω, D m ω ∂μ ≤ ∫ ω, D 0 ω ∂μ - ∑ k ∈ range m, κ * ∫ ω, N k ω ∂μ
      + ∑ k ∈ range m, ∫ ω, err k ω ∂μ :=
  telescope (D := fun k => ∫ ω, D k ω ∂μ) fun _k hk => integral_step h hk

open Real

/-- `T = 16 log n / n²` (Klartag Lemma 5.2, p. 23). -/
noncomputable def horizon (n : ℕ) : ℝ := 16 * Real.log n / (n : ℝ) ^ 2

noncomputable def numSteps (n e : ℕ) : ℕ := ⌈16 * (n : ℝ) ^ e * Real.log n⌉₊

/-- `h = T / N`, so that `N·h = T` exactly. -/
noncomputable def stepSize (n e : ℕ) : ℝ := horizon n / (numSteps n e : ℝ)

theorem log_pos_of_three {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have he : Real.exp 1 ≤ (n : ℝ) := le_trans (le_of_lt (by
    have := Real.exp_one_lt_d9
    linarith)) h3
  have := Real.log_le_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at this

theorem numSteps_pos {n e : ℕ} (hn : 3 ≤ n) : 0 < (numSteps n e : ℝ) := by
  have hlog := log_pos_of_three hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbase : (1 : ℝ) ≤ (n : ℝ) ^ e := one_le_pow₀ hn'
  have : (0 : ℝ) < 16 * (n : ℝ) ^ e * Real.log n := by nlinarith
  have hceil : 16 * (n : ℝ) ^ e * Real.log n ≤ (numSteps n e : ℝ) := Nat.le_ceil _
  linarith

/-- `h ≤ n^{-(e+2)}`: the step size the choice of `numSteps` delivers. -/
theorem stepSize_le {n e : ℕ} (hn : 3 ≤ n) : stepSize n e ≤ 1 / (n : ℝ) ^ (e + 2) := by
  have hlog := log_pos_of_three hn
  have hn' : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbase : (0 : ℝ) < (n : ℝ) ^ e := pow_pos hn' e
  have hden : (0 : ℝ) < 16 * (n : ℝ) ^ e * Real.log n := by nlinarith
  have hceil : 16 * (n : ℝ) ^ e * Real.log n ≤ (numSteps n e : ℝ) := Nat.le_ceil _
  have hT : (0 : ℝ) ≤ horizon n := by
    rw [horizon]; positivity
  calc stepSize n e = horizon n / (numSteps n e : ℝ) := rfl
    _ ≤ horizon n / (16 * (n : ℝ) ^ e * Real.log n) := by
        exact div_le_div_of_nonneg_left hT hden hceil
    _ = 1 / (n : ℝ) ^ (e + 2) := by
        rw [horizon, pow_add]
        field_simp

end D5.S3.Arith.Lattices.Klartag.Walk.ChainDrift
