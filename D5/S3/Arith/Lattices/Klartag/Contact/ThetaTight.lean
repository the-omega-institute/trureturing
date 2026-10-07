/- GID: D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/ThetaTight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.TerminalCount

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

namespace D5.S3.Arith.Lattices.Klartag.Contact.ThetaTight

open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Construction.Section5

variable {a₀ α : ℝ} {n : ℕ}

/-- `α·ρ = (√a₀)⁻¹ + α√n/2` — the α-dependence of `ρ` is exactly one factor of `α⁻¹`. -/
theorem alpha_mul_rhoC (ha : α ≠ 0) :
    α * rhoC a₀ α n = (Real.sqrt a₀)⁻¹ + α * Real.sqrt n / 2 := by
  rw [rhoC]
  field_simp

/-- The upper end of `α·ρ`, from the tiling defect `n·(α√n/2) ≤ 1/4`. -/
theorem alpha_mul_rhoC_le (ha : α ≠ 0) (hn : n ≠ 0)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) :
    α * rhoC a₀ α n ≤ (Real.sqrt a₀)⁻¹ + 1 / (4 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [alpha_mul_rhoC ha]
  have h : α * Real.sqrt n / 2 ≤ 1 / (4 * (n : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hdef, hnR]
  linarith

/-- **The tight threshold.**  `Params.markov` asks for `2(p−1)·n·κ_n·C < θ·(pⁿ−1)`; this is the
smallest `θ` that meets it, written out.  Unlike `16·C` it is `α`-free to within the tiling
defect, because `n·κ_n·C1c = p^{n−1}·(n·αⁿ·C1c)`. -/
noncomputable def thetaTight (p n : ℕ) (C : ℝ) : ℝ :=
  4 * ((p : ℝ) - 1) * (n : ℝ) * kappa n * C / ((p : ℝ) ^ n - 1)

/-- `thetaTight` clears `markov`'s bound with a factor of two to spare. -/
theorem two_mul_lt_thetaTight_mul {p : ℕ} {C : ℝ} (hp : 1 < (p : ℝ) ^ n)
    (hC : 0 < ((p : ℝ) - 1) * (n : ℝ) * kappa n * C) :
    2 * (((p : ℝ) - 1) * (n : ℝ) * kappa n * C)
      < thetaTight p n C * ((p : ℝ) ^ n - 1) := by
  have hd : (0 : ℝ) < (p : ℝ) ^ n - 1 := by linarith
  rw [thetaTight, div_mul_cancel₀ _ (ne_of_gt hd)]
  linarith

end D5.S3.Arith.Lattices.Klartag.Contact.ThetaTight
