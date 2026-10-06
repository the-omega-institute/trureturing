/- GID: D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/ReflStep2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second order log determinant bounds and accumulated drift. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Construction.LiftBound

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.ReflStep2

open MeasureTheory
open ProbabilityTheory
open Matrix
open Finset
open Module
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant2
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant3

noncomputable section

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- The reflected step, *defined* through the past. -/
def reflStep2 (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (UT n) :=
  reflOf q (chainU q W A₀ k (past ξ k ω)).2 (ξ k ω)

/-- **The bridge.**  Fresh definition on the left; the frozen `reflStep` is one delta step away. -/
theorem reflStep2_eq_reflStep (k : ℕ) (ω : Ω) :
    reflStep2 q W A₀ ξ k ω = StateInvariant.reflStep q W A₀ ξ k ω := by
  show (Chain.freeSub q (chainU q W A₀ k (past ξ k ω)).2).reflection (ξ k ω)
      = (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).reflection (ξ k ω)
  exact reflection_congr (by rw [chain_eq_chainU]) _

/-- The same at an index `j < k`, against the past truncated at `k`. -/
theorem reflOf_past_eq_reflStep {j k : ℕ} (hjk : j < k) (ω : Ω) :
    reflOf q (chainU q W A₀ j (past ξ k ω)).2 ((past ξ k ω) j)
      = StateInvariant.reflStep q W A₀ ξ j ω := by
  have hv : (past ξ k ω) j = ξ j ω := by simp [past, hjk]
  have hchain : chainU q W A₀ j (past ξ k ω) = Chain.chain q W A₀ ξ j ω :=
    (chain_congr j fun i hi => by simp [past, lt_trans hi hjk]).symm
  rw [hv]
  show (Chain.freeSub q (chainU q W A₀ j (past ξ k ω)).2).reflection (ξ j ω)
      = (Chain.freeSub q (Chain.chain q W A₀ ξ j ω).2).reflection (ξ j ω)
  exact reflection_congr (by rw [hchain]) _

end

end D5.S3.Arith.Lattices.Klartag.Drift.ReflStep2
