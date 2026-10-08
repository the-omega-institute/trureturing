/- GID: D5/S3/Arith/Lattices/Klartag/Construction/LiftBound
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Construction/LiftBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construction A lattices, covolumes and ellipsoid transfer. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.State.StateInvariant3

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Construction.LiftBound

open MeasureTheory
open Matrix
open Finset
open Module
open ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant2

noncomputable section

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The freezes partition the active set.**  A step never breaks an already-active constraint
(`Chain.newActive_disjoint`), so the counts add. -/
theorem sum_card_newActive (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    ∑ j ∈ Finset.range k, (Chain.newActive q W A₀ ξ j ω).card
      = (Chain.chain q W A₀ ξ k ω).2.card := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Chain.chain_snd_succ_eq,
      Finset.card_union_of_disjoint (Chain.newActive_disjoint hA₀ hq hne k ω).symm]

/-- **The accumulated lift, with no per-step count and no `dim`.** -/
theorem norm_liftSum_le_card (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {η : ℝ} (_hη0 : 0 ≤ η) (k : ℕ) (ω : Ω)
    (hstep : ∀ j, j < k → ‖gaussStep q W A₀ ξ j ω‖ ≤ η) :
    ‖liftSum q W A₀ ξ k ω‖ ≤ ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) * η := by
  classical
  have hterm : ∀ j ∈ Finset.range k,
      ‖liftStep q W A₀ ξ j ω‖ ≤ ((Chain.newActive q W A₀ ξ j ω).card : ℝ) * η := by
    intro j hj
    refine le_trans (norm_liftStep_le hA₀ hq hne j ω) ?_
    exact mul_le_mul_of_nonneg_left (hstep j (Finset.mem_range.1 hj)) (Nat.cast_nonneg _)
  calc ‖liftSum q W A₀ ξ k ω‖
      ≤ ∑ j ∈ Finset.range k, ‖liftStep q W A₀ ξ j ω‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k, ((Chain.newActive q W A₀ ξ j ω).card : ℝ) * η :=
        Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range k, ((Chain.newActive q W A₀ ξ j ω).card : ℝ)) * η := by
        rw [Finset.sum_mul]
    _ = ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) * η := by
        rw [← Nat.cast_sum, sum_card_newActive hA₀ hq hne k ω]

section Wired

variable [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The per-path core with the **accumulated** lift bound (`StateInvariantGlue.stateBounds_of_chain`
takes the per-step one and pays a factor `dim`). -/
theorem stateBounds_of_chain_count {a₀ r₀ L : ℝ} {k : ℕ} {ω : Ω}
    (_hA₀ : A₀ ∈ Chain.kSet q W)
    (_hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (_hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hr₀ : 0 ≤ r₀) (hL : 0 ≤ L)
    (hacc : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖ ≤ r₀)
    (hlift : ‖liftSum q W A₀ ξ k ω‖ ≤ L)
    (hlt : r₀ + L < a₀) :
    Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1)
      (a₀ - (r₀ + L)) (a₀ + (r₀ + L)) := by
  refine StateInvariant.stateBounds_of_opNorm_le (symMat_isSymm _) (by positivity) hlt ?_
  have hdec : symMat (Chain.chain q W A₀ ξ k ω).1 - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ)
      = symMat (gaussSum q W A₀ ξ k ω) + symMat (liftSum q W A₀ ξ k ω) := by
    rw [chain_fst_eq, symMat_add, symMat_add, hA₀m]
    abel
  rw [hdec, map_add]
  exact (norm_add_le _ _).trans
    (add_le_add hacc ((StepInputs2.opNorm_symMat_le_norm _).trans hlift))

end Wired

end

end D5.S3.Arith.Lattices.Klartag.Construction.LiftBound
