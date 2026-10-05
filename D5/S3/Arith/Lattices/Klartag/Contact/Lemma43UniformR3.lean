/- GID: D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR3
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR3
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43UniformR2

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

namespace D5.S3.Arith.Lattices.Klartag.Lemma43R3

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open scoped ENNReal NNReal

/-- **The terminal summand is integrable.**  `Profile.integrableOn_profile_radial` at
`t = ChainDrift.horizon n` and `W = WindowR2.windowR2 α n`. -/
theorem integrableOn_radial_terminal2 {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    IntegrableOn (fun y : ℝ => y ^ (n - 1) *
        profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y)
      (Ioi (0 : ℝ)) :=
  integrableOn_profile_radial (windowR2_nonneg hn hα) (ChainDrift.horizon n)

/-- **The integrated summand is integrable**, in the `4·∫` shape `fR4`/`fR2` uses. -/
theorem integrableOn_radial_fR2 {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    IntegrableOn (fun y : ℝ => y ^ (n - 1) *
        (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profile (a0C n) α (WindowR2.windowR2 α n) n t y))
      (Ioi (0 : ℝ)) := by
  have hW0 : (0 : ℝ) ≤ WindowR2.windowR2 α n := windowR2_nonneg hn hα
  have hT0 : (0 : ℝ) ≤ ChainDrift.horizon n := T_nonneg (by omega)
  have h := (integrableOn_profile_radial_t (a₀ := a0C n) (α := α)
    (W := WindowR2.windowR2 α n) (T := ChainDrift.horizon n) (n := n) hW0 hT0).const_mul 4
  have heq : (fun y : ℝ => y ^ (n - 1) *
        (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profile (a0C n) α (WindowR2.windowR2 α n) n t y))
      = fun y : ℝ => 4 * (y ^ (n - 1) *
        ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profile (a0C n) α (WindowR2.windowR2 α n) n t y) := by
    funext y; ring
  rw [heq]
  exact h

theorem radial_bound_combined {α a b : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
        (a * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
                profile (a0C n) α (WindowR2.windowR2 α n) n t y)
          + b * profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y)
      = a * (∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
              (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
                profile (a0C n) α (WindowR2.windowR2 α n) n t y))
        + b * (∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
              profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y) := by
  have hF := integrableOn_radial_fR2 (α := α) (n := n) hn hα
  have hG := integrableOn_radial_terminal2 (α := α) (n := n) hn hα
  have hcongr : ∀ y ∈ Ioi (0 : ℝ), y ^ (n - 1) *
      (a * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
              profile (a0C n) α (WindowR2.windowR2 α n) n t y)
        + b * profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y)
      = a * (y ^ (n - 1) * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
              profile (a0C n) α (WindowR2.windowR2 α n) n t y))
        + b * (y ^ (n - 1) *
            profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y) :=
    fun y _ => by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_add (hF.const_mul a) (hG.const_mul b),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- **The combined radial bound.**  §2 plus `radial_bound4_of_chain2` and
`radial_bound_terminal2`: the constant is `a·4·C1R·(8 − 8/n²) + b·C1cR·n²`, with no new factor and
the `n²` of the exponent still cancelled by the horizon in the first summand. -/
theorem radial_bound_combined_le {α a b : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
        (a * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
                profile (a0C n) α (WindowR2.windowR2 α n) n t y)
          + b * profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y)
      ≤ a * (4 * C1R α n * (8 - 8 / (n : ℝ) ^ 2)) + b * (C1cR (a0C n) α n * (n : ℝ) ^ 2) := by
  rw [radial_bound_combined hn hα]
  have h1 := radial_bound4_of_chain2 (α := α) (n := n) hn hα hdef
  have h2 := radial_bound_terminal2 (α := α) (n := n) hn hα hdef
  have k1 := mul_le_mul_of_nonneg_left h1 ha
  have k2 := mul_le_mul_of_nonneg_left h2 hb
  linarith

end D5.S3.Arith.Lattices.Klartag.Lemma43R3
