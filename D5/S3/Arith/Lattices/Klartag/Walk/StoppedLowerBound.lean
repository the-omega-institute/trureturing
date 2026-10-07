/- GID: D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.CutSideConditions

set_option linter.unusedSectionVars false

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

namespace D5.S3.Arith.Lattices.Klartag.Walk.StoppedLowerBound

open MeasureTheory
open Matrix
open Finset
open Module
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The state bounds from `stateGood` at the same index.**  `CutSideConditions`' proof with the
`goodCut` membership replaced by the weaker `stateGood`, which the stopping time supplies. -/
theorem stateBounds_of_stateGood {η a₀ r₀ c₃ : ℝ} {j : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hlt : r₀ + c₃ * η < a₀)
    (hstate : ω ∈ stateGood q W A₀ ξ η r₀ c₃ j) :
    Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ j ω).1)
      (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) := by
  have hstep : ∀ i, i < j → ‖StateInvariant.gaussStep q W A₀ ξ i ω‖ ≤ η := fun i hi =>
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hstate.1 i hi)
  have hlift : ‖StateInvariant.liftSum q W A₀ ξ j ω‖ ≤ c₃ * η := by
    refine le_trans (LiftBound.norm_liftSum_le_card hA₀ hq hne hη j ω hstep) ?_
    exact mul_le_mul_of_nonneg_right hstate.2.2 hη
  have hc₃ : (0 : ℝ) ≤ c₃ := le_trans (Nat.cast_nonneg _) hstate.2.2
  exact LiftBound.stateBounds_of_chain_count hA₀ hq hne hA₀m hr₀ (by positivity)
    hstate.2.1 hlift hlt

/-- **The increment ceiling from `stateGood` one index later.**  `stateGood (j+1)` carries both
`‖ξ_j‖ ≤ η` and `card C_{j+1} ≤ c₃`, and `newActive_j ⊆ C_{j+1}`. -/
theorem norm_incr_le_of_stateGood {η r₀ c₃ : ℝ} {j : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hstate : ω ∈ stateGood q W A₀ ξ η r₀ c₃ (j + 1)) :
    ‖LogDetChainLower.incr q W A₀ ξ j ω‖ ≤ (1 + c₃) * η := by
  classical
  have hg : ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ ≤ η :=
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hstate.1 j (by omega))
  have hg0 : (0 : ℝ) ≤ ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ := norm_nonneg _
  have hsub : Chain.newActive q W A₀ ξ j ω ⊆ (Chain.chain q W A₀ ξ (j + 1) ω).2 := by
    rw [Chain.chain_snd_succ_eq]; exact Finset.subset_union_right
  have hcard : ((Chain.newActive q W A₀ ξ j ω).card : ℝ) ≤ c₃ := by
    refine le_trans ?_ hstate.2.2
    exact_mod_cast Finset.card_le_card hsub
  have hl : ‖StateInvariant.liftStep q W A₀ ξ j ω‖ ≤ c₃ * η := by
    refine le_trans (StateInvariant2.norm_liftStep_le hA₀ hq hne j ω) ?_
    have hc0 : (0 : ℝ) ≤ c₃ := le_trans (Nat.cast_nonneg _) hcard
    calc ((Chain.newActive q W A₀ ξ j ω).card : ℝ)
          * ‖StateInvariant.gaussStep q W A₀ ξ j ω‖
        ≤ c₃ * ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ :=
          mul_le_mul_of_nonneg_right hcard hg0
      _ ≤ c₃ * η := mul_le_mul_of_nonneg_left hg hc0
  rw [LogDetChainLower.incr_eq]
  calc ‖StateInvariant.gaussStep q W A₀ ξ j ω + StateInvariant.liftStep q W A₀ ξ j ω‖
      ≤ ‖StateInvariant.gaussStep q W A₀ ξ j ω‖
        + ‖StateInvariant.liftStep q W A₀ ξ j ω‖ := norm_add_le _ _
    _ ≤ η + c₃ * η := add_le_add hg hl
    _ = (1 + c₃) * η := by ring

/-- **The pathwise lower bound on the stopped log-determinant, at every `ω`.**  The index is
`K' = min K (τ−1)`, which is what `stoppedState` reads, and every `j < K'` is strictly below `τ`,
so `StoppedChain.stateGood_of_lt_tau` discharges both side conditions with no good event. -/
theorem logDet_stopped_ge {η a₀ r₀ c₃ rr : ℝ} {N K : ℕ} {ω : Ω} {xs : ι → (Fin n → ℝ)}
    (hqx : q = fun i => ChainWiring.qUT (xs i))
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hlt : r₀ + c₃ * η < a₀)
    (hrr0 : 0 ≤ rr) (hrr : rr ≤ 1 / 2)
    (hrm : (1 + c₃) * η ≤ rr * (a₀ - (r₀ + c₃ * η))) :
    ChainWiring.logDet A₀
        + (∑ j ∈ Finset.range (min K (tau q W A₀ ξ η r₀ c₃ N ω - 1)),
            ⟪LogDetChainLower.Vcoef q W A₀ ξ j ω, ξ j ω⟫)
        - ((1 / 2 + 2 * rr) / (a₀ - (r₀ + c₃ * η)) ^ 2)
            * (∑ j ∈ Finset.range (min K (tau q W A₀ ξ η r₀ c₃ N ω - 1)),
                ‖LogDetChainLower.incr q W A₀ ξ j ω‖ ^ 2)
      ≤ ChainWiring.logDet (stoppedState q W A₀ ξ η r₀ c₃ N K ω) := by
  subst hqx
  set K' := min K (tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω - 1) with hK'
  have hlt' : ∀ j, j < K' → j + 1 < tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω := by
    intro j hj
    have h1 : j < tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω - 1 := by
      rw [hK'] at hj; omega
    omega
  rw [stoppedState]
  exact LogDetChainLower.logDet_chain_ge_martingale (xs := xs) (W := W) (A₀ := A₀) (ξ := ξ)
    (m := a₀ - (r₀ + c₃ * η)) (M := a₀ + (r₀ + c₃ * η)) hrr0 hrr K'
    (fun j hj => stateBounds_of_stateGood hA₀ hq hne hA₀m hη hr₀ hlt
      (stateGood_of_lt_tau (N := N) (by omega : j < tau _ W A₀ ξ η r₀ c₃ N ω)))
    (fun j hj => le_trans
      (le_trans (StepInputs2.opNorm_symMat_le_norm _)
        (norm_incr_le_of_stateGood hA₀ hq hne
          (stateGood_of_lt_tau (N := N) (hlt' j hj)))) hrm)

end D5.S3.Arith.Lattices.Klartag.Walk.StoppedLowerBound
