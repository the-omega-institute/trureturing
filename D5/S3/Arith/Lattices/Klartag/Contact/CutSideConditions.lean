/- GID: D5/S3/Arith/Lattices/Klartag/Contact/CutSideConditions
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/CutSideConditions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.LogDetChainLower
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds

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

namespace D5.S3.Arith.Lattices.Klartag.Contact.CutSideConditions

open MeasureTheory
open Matrix
open Finset
open Module
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **`card (newActive j) ≤ c₃`** on `goodCut`, for `j < K`: the newly frozen constraints at step
`j` all sit in `C_{j+1}`. -/
theorem card_newActive_le {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η r₀ c₃ : ℝ} {K j : ℕ} {ω : Ω}
    (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K) (hKN : K < N) (hj : j < K) :
    ((Chain.newActive q W A₀ ξ j ω).card : ℝ) ≤ c₃ := by
  classical
  have hsub : Chain.newActive q W A₀ ξ j ω ⊆ (Chain.chain q W A₀ ξ (j + 1) ω).2 := by
    rw [Chain.chain_snd_succ_eq]; exact Finset.subset_union_right
  have hcard : ((Chain.newActive q W A₀ ξ j ω).card : ℝ)
      ≤ ((Chain.chain q W A₀ ξ (j + 1) ω).2.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact le_trans hcard (stateGood_of_goodCut hω hKN (by omega)).2.2

section Numeric

/-- **`rr := 5/⁴√n`** — the ceiling the increment actually needs, and it decays.  At `n₁` it is
`0.132`; the resulting coefficient `(1/2 + 2rr)/m²` is `0.92` there and tends to `1/2`. -/
noncomputable def rrAt (n : ℕ) : ℝ := 5 / Real.sqrt (Real.sqrt (n : ℝ))

end Numeric

end D5.S3.Arith.Lattices.Klartag.Contact.CutSideConditions
