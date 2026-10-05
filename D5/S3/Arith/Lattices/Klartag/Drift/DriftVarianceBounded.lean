/- GID: D5/S3/Arith/Lattices/Klartag/Drift/DriftVarianceBounded
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/DriftVarianceBounded
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second order log determinant bounds and accumulated drift. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.ShortfallBound

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

namespace D5.S3.Arith.Lattices.Klartag.Drift.DriftVarianceBounded

open MeasureTheory
open ProbabilityTheory
open Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Popoviciu, per summand.** -/
theorem variance_trunc_le {Z : Ω → ℝ} {cap : ℝ}
    (hZm : AEMeasurable Z P) (hZ : ∀ᵐ ω ∂P, Z ω ∈ Set.Icc (0 : ℝ) cap) :
    variance Z P ≤ (cap / 2) ^ 2 := by
  have h := variance_le_sq_of_bounded hZ hZm
  simpa using h

/-- **The drift proxy's variance**, from independence and a pathwise cap.  No Gaussian moment of
any order is used. -/
theorem variance_sum_le {Z : ℕ → Ω → ℝ} {K : ℕ} {cap : ℝ}
    (hmem : ∀ j ∈ Finset.range K, MemLp (Z j) 2 P)
    (hindep : Set.Pairwise (↑(Finset.range K)) fun i j => IndepFun (Z i) (Z j) P)
    (hZ : ∀ j ∈ Finset.range K, ∀ᵐ ω ∂P, Z j ω ∈ Set.Icc (0 : ℝ) cap) :
    variance (fun ω => ∑ j ∈ Finset.range K, Z j ω) P ≤ (K : ℝ) * (cap / 2) ^ 2 := by
  have hfun : (fun ω => ∑ j ∈ Finset.range K, Z j ω) = ∑ j ∈ Finset.range K, Z j := by
    funext ω; simp
  rw [hfun, IndepFun.variance_sum hmem hindep]
  calc ∑ j ∈ Finset.range K, variance (Z j) P
      ≤ ∑ _j ∈ Finset.range K, (cap / 2) ^ 2 :=
        Finset.sum_le_sum fun j hj =>
          variance_trunc_le ((hmem j hj).aestronglyMeasurable.aemeasurable) (hZ j hj)
    _ = (K : ℝ) * (cap / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end D5.S3.Arith.Lattices.Klartag.Drift.DriftVarianceBounded
