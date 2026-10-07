/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped4

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped5

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped4
open scoped RealInnerProductSpace

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

omit [Countable ι] [MeasurableSpace Ω] in
/-- **The middle case pins `k` to `τ − 1`.**  `k < τ` and `¬(k+1 ≤ τ−1)` force `τ−1 ≤ k < τ`. -/
theorem mid_iff {η r₀ c₃ : ℝ} {N k : ℕ} {ω : Ω}
    (hτ : 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω) :
    (k < tau q W A₀ ξ η r₀ c₃ N ω ∧ ¬ (k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1))
      ↔ k = tau q W A₀ ξ η r₀ c₃ N ω - 1 := by
  constructor
  · rintro ⟨h1, h2⟩; omega
  · intro h; omega

omit [Countable ι] [MeasurableSpace Ω] in
/-- Summing the middle term is a single evaluation. -/
theorem sum_mid_eq {η r₀ c₃ : ℝ} {N m : ℕ} {ω : Ω} (g : ℕ → ℝ)
    (hτ : 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω) :
    ∑ k ∈ Finset.range m,
        (if k < tau q W A₀ ξ η r₀ c₃ N ω ∧ ¬ (k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1)
          then g k else 0)
      = if tau q W A₀ ξ η r₀ c₃ N ω - 1 ∈ Finset.range m
          then g (tau q W A₀ ξ η r₀ c₃ N ω - 1) else 0 := by
  classical
  rw [← Finset.sum_ite_eq (Finset.range m) (tau q W A₀ ξ η r₀ c₃ N ω - 1) g]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : k = tau q W A₀ ξ η r₀ c₃ N ω - 1
  · rw [if_pos ((mid_iff hτ).2 h), if_pos h.symm]
  · rw [if_neg (fun hc => h ((mid_iff hτ).1 hc)), if_neg (fun hc => h hc.symm)]

def IntegrableAtIndex (P : Measure Ω) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (N : ℕ) : Prop :=
  ∀ f : Ω → ℕ, Measurable f → (∀ ω, f ω < N) →
    Integrable (fun ω => ‖ξ (f ω) ω‖) P ∧ Integrable (fun ω => ‖ξ (f ω) ω‖ ^ 2) P

omit [MeasurableSpace Ω] in
omit [Countable ι] in
/-- `τ` is measurable — it is a stopping time, so `{τ ≤ k}` is measurable for every `k`, and a
`ℕ`-valued map with measurable sublevel sets is measurable. -/
theorem measurable_tau {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) (N : ℕ) :
    Measurable (tau q W A₀ ξ η r₀ c₃ N) := by
  refine measurable_to_countable' fun k => ?_
  have hle : ∀ j, MeasurableSet[m0] {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ j} := by
    intro j
    have h := isStoppingTime_tau ℱ hG N j
    have h2 : MeasurableSet[ℱ j] {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ j} := by simpa using h
    exact ℱ.le j _ h2
  have hset : (tau q W A₀ ξ η r₀ c₃ N) ⁻¹' {k}
      = {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ k} \ {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ k - 1} ∪
        (if k = 0 then {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ 0} else ∅) := by
    ext ω
    by_cases hk : k = 0
    · subst hk; simp [Set.mem_preimage]
    · rw [if_neg hk]
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_sdiff,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, or_false]
      omega
  rw [hset]
  refine MeasurableSet.union ((hle k).diff (hle (k - 1))) ?_
  by_cases hk : k = 0
  · rw [if_pos hk]; exact hle 0
  · rw [if_neg hk]; exact MeasurableSet.empty

omit [MeasurableSpace Ω] in
omit [Countable ι] in
theorem measurable_tau_sub_one {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) (N : ℕ) :
    Measurable (fun ω => tau q W A₀ ξ η r₀ c₃ N ω - 1) :=
  (measurable_tau ℱ hG N).sub_const 1

section Integral

variable {P : Measure Ω} [IsProbabilityMeasure P]

end Integral

section Sides

open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling

end Sides

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped5
