/- GID: D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupRW2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/PaddedLawSetupRW2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
import D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
import D5.S3.Arith.Lattices.Klartag.Walk.ChainWalkRW2

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

namespace D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupRW2

open MeasureTheory
open ProbabilityTheory
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2

noncomputable section

/-- **The tail-side hypothesis is unchanged.**  `PaddedLawSetup.TailSideHyp` does not mention the
window, so the reach lane uses it as it stands. -/
@[reducible] def TailSideHypR (n : ℕ) (c α : ℝ)
    (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)) (W : Finset (Fin n → ℤ))
    (A₀ : EuclideanSpace ℝ (UT n)) : Prop :=
  TailSideHyp n c α q W A₀

/-- **`PaddedLawSetup.RawData` at the reach window.**  Identical field for field except
`window_lt_p`, `supp_radius` and `hwin`, which are stated at `WindowR2.windowR2 α n`. -/
structure RawDataR (p n : ℕ) (α R : ℝ) (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n))
    (W : Finset (Fin n → ℤ)) (A₀ : EuclideanSpace ℝ (UT n)) : Prop where
  hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫
  hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫
  alpha_pos : 0 < α
  alpha_norm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  R_nonneg : 0 ≤ R
  R_scaled : α * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4
  window_lt_p : windowR2 α n < (p : ℝ)
  supp_ne_zero : ∀ y ∈ W, y ≠ 0
  supp_radius : ∀ y ∈ W, ‖toE n y‖ ≤ windowR2 α n
  hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n
  hr : ∀ y ∈ W, 0 < α * ‖toE n y‖
  hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
    0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

/-- **`RawDataR` restricts**, exactly as `LatticeData.rawData_mono` does for `RawData`: every field
is either `∀ y ∈ W` or independent of `W`. -/
theorem rawDataR_mono {p n : ℕ} {α R : ℝ} {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)}
    {W W' : Finset (Fin n → ℤ)} {A₀ : EuclideanSpace ℝ (UT n)}
    (h : RawDataR p n α R q W A₀) (hsub : W' ⊆ W) : RawDataR p n α R q W' A₀ :=
  { hq := fun j i hi => h.hq j i (hsub hi)
    hA₀ := fun y hy => h.hA₀ y (hsub hy)
    alpha_pos := h.alpha_pos
    alpha_norm := h.alpha_norm
    R_nonneg := h.R_nonneg
    R_scaled := h.R_scaled
    R_lt_p := h.R_lt_p
    tiling_defect := h.tiling_defect
    window_lt_p := h.window_lt_p
    supp_ne_zero := fun y hy => h.supp_ne_zero y (hsub hy)
    supp_radius := fun y hy => h.supp_radius y (hsub hy)
    hwin := fun y hy => h.hwin y (hsub hy)
    hr := fun y hy => h.hr y (hsub hy)
    hy := fun k hk hk0 y hy => h.hy k hk hk0 y (hsub hy)
    arith := h.arith }

noncomputable def chainRaw2_on_setupR {n p : ℕ} {c α : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)} {R : ℝ} (hn : 3 ≤ n)
    (hdata : RawDataR p n α R q W A₀) (htail : TailSideHypR n c α q W A₀) :
    ChainRaw2RW2 p n :=
  chainRaw2_of_walkRW2 (P := gaussPath (EuclideanSpace ℝ (UT n))) (ξ := step c)
    hn hdata.hq hdata.hA₀ hdata.alpha_pos hdata.alpha_norm R hdata.R_nonneg
    hdata.R_scaled hdata.R_lt_p hdata.tiling_defect hdata.window_lt_p hdata.supp_ne_zero
    hdata.supp_radius hdata.hwin hdata.hr hdata.hy htail hdata.arith

end

end D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupRW2
