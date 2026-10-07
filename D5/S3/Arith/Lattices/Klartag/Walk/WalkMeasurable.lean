/- GID: D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.WalkTelescope
import D5.S3.Arith.Lattices.Klartag.Walk.ChainWiring

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.Chain
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open scoped RealInnerProductSpace

section Measurable

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
variable {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem measurable_of_active_and_inc (hξ : ∀ k, Measurable (ξ k)) (k : ℕ)
    (f : Finset ι → EuclideanSpace ℝ (UT n) → ℝ) (hf : ∀ c : Finset ι, Measurable (f c)) :
    Measurable fun ω => f (chain q W A₀ ξ k ω).2 (ξ k ω) := by
  classical
  have hrep : (fun ω => f (chain q W A₀ ξ k ω).2 (ξ k ω))
      = fun ω => ∑ c ∈ W.powerset,
          if (chain q W A₀ ξ k ω).2 = c then f c (ξ k ω) else 0 := by
    funext ω
    rw [Finset.sum_ite_eq W.powerset (chain q W A₀ ξ k ω).2 (fun c => f c (ξ k ω)),
      if_pos (Finset.mem_powerset.2 (chain_snd_subset_window k ω))]
  rw [hrep]
  refine Finset.measurable_sum _ fun c _ => ?_
  have hbranch : Measurable fun ω => f c (ξ k ω) := (hf c).comp (hξ k)
  exact Measurable.ite (ChainWiring.measurableSet_active_eq hξ k c) hbranch measurable_const

/-- **The pure walk is measurable** — the increment reads the active set through the projection. -/
theorem measurable_pureWalk (hξ : ∀ k, Measurable (ξ k)) (x : ι) (k : ℕ) :
    Measurable (pureWalk q W A₀ ξ x k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    show Measurable fun ω => pureWalk q W A₀ ξ x k ω
      + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q x⟫
    refine ih.add ?_
    refine measurable_of_active_and_inc hξ k
      (fun c v => ⟪(freeSub q c).starProjection v, q x⟫) fun c => ?_
    have hcont : Continuous fun v : EuclideanSpace ℝ (UT n) =>
        ⟪(freeSub q c).starProjection v, q x⟫ :=
      continuous_inner.comp ((freeSub q c).starProjection.continuous.prodMk continuous_const)
    exact hcont.measurable

/-- **`WalkTelescope.hprop_of_hincl`'s `hM`.** -/
theorem measurable_constraintM (hξ : ∀ k, Measurable (ξ k)) (x : ι) (k : ℕ) :
    Measurable (constraintM q W A₀ ξ x k) :=
  (measurable_pureWalk hξ x k).sub measurable_const

omit [Countable ι] [MeasurableSpace Ω] in
/-- The chain reads only the increments before time `k`. -/
theorem chain_eq_of_eq {Ω' : Type*} (ξ' : ℕ → Ω' → EuclideanSpace ℝ (UT n))
    (ω : Ω) (ω' : Ω') (k : ℕ) (h : ∀ j < k, ξ j ω = ξ' j ω') :
    chain q W A₀ ξ k ω = chain q W A₀ ξ' k ω' := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : ∀ j < k, ξ j ω = ξ' j ω' := fun j hj => h j (Nat.lt_succ_of_lt hj)
    rw [chain_succ, chain_succ, ih hk, h k (Nat.lt_succ_self k)]

end Measurable

end D5.S3.Arith.Lattices.Klartag
