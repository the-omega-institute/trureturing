/- GID: D5/S3/Analytic/Asymptotics/MellinBarnesSeries
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/MellinBarnesSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closing a decreasing contour sequence identifies its integral with a residue series. -/

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Bastiaan J Braams
SPDX-License-Identifier: Apache-2.0

Adapted source port, 2026-10-31, from bjbraams/lean-DLMF revision
560b9475f35bbc6e4f5296631298859825091f7f. Imports, namespace and visibility
are adapted for this repository. The immutable source chain, complete-license and
NOTICE assessment are in Library/Asymptotics/braams2026barnesmittagport.md.
Retire each port when this repository's pinned Mathlib supplies an equivalent
declaration and replace its actual consumers with direct Mathlib calls.
-/

import D5.S3.Analytic.Asymptotics.BarnesResidue

noncomputable section
open Complex MeasureTheory Set Filter Real intervalIntegral
open scoped Topology Interval
namespace D5.S3.Analytic.Asymptotics.MellinBarnesSeries

/-- Hypotheses for closing a vertical-line integral to the left across simple poles: lines
`c n`, poles `p n` with `c (n+1) < Re (p n) < c n`, and holomorphic numerators `φ n` with
`F s = φ n s / (s - p n)` on the `n`-th closed strip. -/
structure MBSeriesData (F : ℂ → ℂ) (c : ℕ → ℝ) (p : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) : Prop where
  /-- the pole `p n` lies strictly inside the strip `c (n+1) < Re s < c n`. -/
  lt_re : ∀ n, c (n + 1) < (p n).re
  /-- Each pole lies strictly to the left of the right boundary of its strip. -/
  re_lt : ∀ n, (p n).re < c n
  /-- the numerator is holomorphic on the closed strip. -/
  differentiableOn : ∀ n, DifferentiableOn ℂ (φ n) (re ⁻¹' Icc (c (n + 1)) (c n))
  /-- the factorization of `F` on the closed strip. -/
  eq_div : ∀ n, ∀ s ∈ re ⁻¹' Icc (c (n + 1)) (c n), s ≠ p n → F s = φ n s / (s - p n)
  /-- integrability of `F` on every line. -/
  integrable : ∀ n, Integrable fun y : ℝ => F (c n + y * I)
  /-- the horizontal cross-section integrals vanish at `+i∞`. -/
  top : ∀ n, Tendsto (fun T : ℝ => ∫ x in c (n + 1)..c n, F (x + T * I)) atTop (𝓝 0)
  /-- the horizontal cross-section integrals vanish at `-i∞`. -/
  bot : ∀ n, Tendsto (fun T : ℝ => ∫ x in c (n + 1)..c n, F (x + T * I)) atBot (𝓝 0)

/-- One step of the shift: crossing the `n`-th pole. -/
private theorem mbSeries_step {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ} {φ : ℕ → ℂ → ℂ}
    (h : MBSeriesData F c p φ) (n : ℕ) :
    (∫ y : ℝ, F (c n + y * I)) - ∫ y : ℝ, F (c (n + 1) + y * I) = 2 * π * φ n (p n) := by
  have hmem : ∀ x y : ℝ, x ∈ Icc (c (n + 1)) (c n) →
      ((x : ℂ) + y * I) ∈ re ⁻¹' Icc (c (n + 1)) (c n) := fun x y hx => by simpa using hx
  have hne_line : ∀ x y : ℝ, x ≠ (p n).re → (x : ℂ) + y * I ≠ p n := fun x y hx he => hx (by
    have := congrArg re he; simpa using this)
  have hne_horiz : ∀ x T : ℝ, T ≠ (p n).im → (x : ℂ) + T * I ≠ p n := fun x T hT he => hT (by
    have := congrArg im he; simpa using this)
  have hlo : c (n + 1) ≤ c n := (h.lt_re n).le.trans (h.re_lt n).le
  have hline : ∀ x : ℝ, x ∈ Icc (c (n + 1)) (c n) → x ≠ (p n).re →
      (fun y : ℝ => φ n (x + y * I) / (x + y * I - p n)) = fun y : ℝ => F (x + y * I) :=
    fun x hx hxp => funext fun y => (h.eq_div n _ (hmem x y hx) (hne_line x y hxp)).symm
  have h1 := hline (c (n + 1)) ⟨le_rfl, hlo⟩ (h.lt_re n).ne
  have h2 := hline (c n) ⟨hlo, le_rfl⟩ (h.re_lt n).ne'
  have hH : ∀ T : ℝ, T ≠ (p n).im →
      (∫ x in c (n + 1)..c n, φ n (x + T * I) / (x + T * I - p n)) =
        ∫ x in c (n + 1)..c n, F (x + T * I) := by
    intro T hT
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hlo] at hx
    exact (h.eq_div n _ (hmem x T hx) (hne_horiz x T hT)).symm
  have key := BarnesResidue.barnesRes_vertical_shift (h.lt_re n) (h.re_lt n) (h.differentiableOn n)
    (by rw [h1]; exact h.integrable (n + 1)) (by rw [h2]; exact h.integrable n)
    ((h.top n).congr' (by
      filter_upwards [eventually_gt_atTop (p n).im] with T hT; exact (hH T hT.ne').symm))
    ((h.bot n).congr' (by
      filter_upwards [eventually_lt_atBot (p n).im] with T hT; exact (hH T hT.ne).symm))
  rwa [h1, h2] at key

/-- **Finite contour shift.** Moving the line from `c 0` to `c N` crosses the poles
`p 0, …, p (N-1)`. -/
private theorem mbSeries_sub_eq_sum {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ} {φ : ℕ → ℂ → ℂ}
    (h : MBSeriesData F c p φ) (N : ℕ) :
    (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      ∑ n ∈ Finset.range N, 2 * π * φ n (p n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, ← mbSeries_step h N]
    ring

/-- **Closing the contour.** If the line integrals tend to `0` as the line moves to the left,
the integral on the first line is the limit of the partial sums of `2π` times the residues. -/
private theorem mbSeries_tendsto {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ} {φ : ℕ → ℂ → ℂ}
    (h : MBSeriesData F c p φ)
    (hlim : Tendsto (fun N : ℕ => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 2 * π * φ n (p n)) atTop
      (𝓝 (∫ y : ℝ, F (c 0 + y * I))) := by
  have := (tendsto_const_nhds (x := ∫ y : ℝ, F (c 0 + y * I))).sub hlim
  rw [sub_zero] at this
  exact this.congr fun N => mbSeries_sub_eq_sum h N

/-- **Closing the contour, summable form.** -/
theorem mbSeries_hasSum {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ} {φ : ℕ → ℂ → ℂ}
    (h : MBSeriesData F c p φ)
    (hlim : Tendsto (fun N : ℕ => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0))
    (hs : Summable fun n => φ n (p n)) :
    HasSum (fun n => 2 * π * φ n (p n)) (∫ y : ℝ, F (c 0 + y * I)) := by
  have hs' : Summable fun n => 2 * π * φ n (p n) := hs.mul_left _
  have h1 := hs'.hasSum
  rwa [tendsto_nhds_unique h1.tendsto_sum_nat (mbSeries_tendsto h hlim)] at h1


end D5.S3.Analytic.Asymptotics.MellinBarnesSeries
