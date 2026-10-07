/- GID: D5/S3/Arith/Lattices/Klartag/Completion/GoodPathVar
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/GoodPathVar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds

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

namespace D5.S3.Arith.Lattices.Klartag.Completion.GoodPathVar

open MeasureTheory
open Finset

section Var

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `(x − L)⁺ = (x − L) + (L − x)⁺`. -/
theorem pos_part_split (L x : ℝ) : max (x - L) 0 = (x - L) + max (L - x) 0 := by
  rcases le_total x L with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

theorem integrable_pos_part {X : Ω → ℝ} (hX : Integrable X P) (L : ℝ) :
    Integrable (fun ω => max (L - X ω) 0) P :=
  ((integrable_const L).sub hX).pos_part

theorem integrable_pos_part' {X : Ω → ℝ} (hX : Integrable X P) (L : ℝ) :
    Integrable (fun ω => max (X ω - L) 0) P :=
  (hX.sub (integrable_const L)).pos_part

/-- **The existence step against a lower-tail bound.**  `s` is the expected shortfall below `L`
and `f` the good event's failure probability.  Markov runs on `(X − L)⁺`, so nothing here needs a
pointwise floor for `X` — which is the whole point: the floor `n·log (mAt n c₃)` is what made
`GoodPathBounds.exists_mem_of_integral_le`'s margin decay like `1/n`. -/
theorem exists_mem_of_variance {X : Ω → ℝ} (hXm : Measurable X) (hX : Integrable X P)
    {L B b s f : ℝ} (hB : ∫ ω, X ω ∂P ≤ B)
    (hshort : ∫ ω, max (L - X ω) 0 ∂P ≤ s)
    {S : Set Ω} (hS : MeasurableSet S) (hbad : P.real Sᶜ ≤ f) (hLb : L < b)
    (hbudget : (B - L + s) / (b - L) + f < 1) :
    ∃ ω, X ω ≤ b ∧ ω ∈ S := by
  classical
  have hposint := integrable_pos_part' hX L
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => max (X ω - L) 0)
    (Filter.Eventually.of_forall fun ω => le_max_right _ _) hposint (b - L)
  have hint : ∫ ω, max (X ω - L) 0 ∂P ≤ B - L + s := by
    have heq : ∫ ω, max (X ω - L) 0 ∂P
        = (∫ ω, (X ω - L) ∂P) + ∫ ω, max (L - X ω) 0 ∂P :=
      calc ∫ ω, max (X ω - L) 0 ∂P
          = ∫ ω, ((X ω - L) + max (L - X ω) 0) ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall fun ω => pos_part_split L (X ω))
        _ = (∫ ω, (X ω - L) ∂P) + ∫ ω, max (L - X ω) 0 ∂P :=
            integral_add (hX.sub (integrable_const L)) (integrable_pos_part hX L)
    have hlin : ∫ ω, (X ω - L) ∂P = (∫ ω, X ω ∂P) - L := by
      rw [integral_sub hX (integrable_const L), integral_const]; simp
    rw [heq, hlin]; linarith
  have hsub : {ω | b ≤ X ω} ⊆ {ω | b - L ≤ max (X ω - L) 0} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact le_trans (by linarith) (le_max_left _ _)
  have hmono : P.real {ω | b ≤ X ω} ≤ P.real {ω | b - L ≤ max (X ω - L) 0} :=
    measureReal_mono hsub (measure_ne_top P _)
  have hmark : P.real {ω | b ≤ X ω} ≤ (B - L + s) / (b - L) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hmk, hmono, hint]
  have hmeas : MeasurableSet {ω | X ω ≤ b} := measurableSet_le hXm measurable_const
  have hcompl : {ω | X ω ≤ b}ᶜ ⊆ {ω | b ≤ X ω} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
    linarith
  have hle : P.real {ω | X ω ≤ b}ᶜ ≤ P.real {ω | b ≤ X ω} :=
    measureReal_mono hcompl (measure_ne_top P _)
  have hG : P.real {ω | X ω ≤ b} + P.real {ω | X ω ≤ b}ᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hmeas]; simp
  have hSsum : P.real S + P.real Sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hS]; simp
  refine GoodPathBounds.exists_mem_inter_of_one_lt' (P := P) (G := {ω | X ω ≤ b}) hS ?_
  linarith

end Var

end D5.S3.Arith.Lattices.Klartag.Completion.GoodPathVar
