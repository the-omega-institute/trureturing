/- GID: D5/S3/Arith/Lattices/Klartag/State/StateInvariant3
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/StateInvariant3
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.State.StateInvariant2

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.State.StateInvariant3

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

noncomputable section

/-- `Submodule.reflection` carries a `HasOrthogonalProjection` instance argument depending on the
subspace, so `rw` on the subspace fails ("motive is not type correct").  `subst` does not. -/
theorem reflection_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Submodule ℝ E} [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (h : K = L) (x : E) : K.reflection x = L.reflection x := by
  subst h; rfl

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem measurable_past (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) : Measurable (past ξ k) := by
  refine measurable_pi_iff.mpr fun j => ?_
  show Measurable fun ω => if j < k then ξ j ω else (0 : EuclideanSpace ℝ (UT n))
  by_cases h : j < k
  · simp only [if_pos h]; exact hξ j
  · simp only [if_neg h]; exact measurable_const

theorem indepFun_past (hξ : ∀ j, Measurable (ξ j)) (hindep : iIndepFun ξ P) (k : ℕ) :
    IndepFun (past ξ k) (ξ k) P := by
  classical
  have hdisj : Disjoint (Finset.range k) ({k} : Finset ℕ) := by
    simp [Finset.disjoint_singleton_right]
  have hbase := hindep.indepFun_finset (Finset.range k) {k} hdisj (fun j => hξ j)
  have hf : Measurable fun u : (↥(Finset.range k) → EuclideanSpace ℝ (UT n)) =>
      (fun j => if h : j < k then u ⟨j, Finset.mem_range.2 h⟩ else 0 :
        ℕ → EuclideanSpace ℝ (UT n)) := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases h : j < k
    · show Measurable fun u : (↥(Finset.range k) → EuclideanSpace ℝ (UT n)) =>
        if h' : j < k then u ⟨j, Finset.mem_range.2 h'⟩ else 0
      simp only [dif_pos h]
      exact measurable_pi_apply (⟨j, Finset.mem_range.2 h⟩ : ↥(Finset.range k))
    · show Measurable fun u : (↥(Finset.range k) → EuclideanSpace ℝ (UT n)) =>
        if h' : j < k then u ⟨j, Finset.mem_range.2 h'⟩ else 0
      simp only [dif_neg h]
      exact measurable_const
  have hg : Measurable fun u : (↥({k} : Finset ℕ) → EuclideanSpace ℝ (UT n)) =>
      u ⟨k, Finset.mem_singleton_self k⟩ := measurable_pi_apply _
  have hcomp := hbase.comp hf hg
  have e1 : ((fun u : (↥(Finset.range k) → EuclideanSpace ℝ (UT n)) =>
        (fun j => if h : j < k then u ⟨j, Finset.mem_range.2 h⟩ else 0 :
          ℕ → EuclideanSpace ℝ (UT n)))
      ∘ fun (ω : Ω) (i : ↥(Finset.range k)) => ξ i ω) = past ξ k := by
    funext ω j
    show (if h : j < k then ξ j ω else 0) = (past ξ k ω) j
    by_cases h : j < k
    · rw [dif_pos h]; simp [past, h]
    · rw [dif_neg h]; simp [past, h]
  have e2 : ((fun u : (↥({k} : Finset ℕ) → EuclideanSpace ℝ (UT n)) =>
        u ⟨k, Finset.mem_singleton_self k⟩)
      ∘ fun (ω : Ω) (i : ↥({k} : Finset ℕ)) => ξ i ω) = ξ k := rfl
  rw [e1, e2] at hcomp
  exact hcomp

/-- **(B1)** `Σ_{j<k} ξ_j ~ N(0, k c² · Id)`. -/
theorem map_sum_xi {c : ℝ} (hc : 0 ≤ c) (hξ : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) (hlaw : ∀ j, P.map (ξ j) = scaled c (EuclideanSpace ℝ (UT n)))
    (k : ℕ) :
    P.map (fun ω => ∑ j ∈ Finset.range k, ξ j ω)
      = scaled (Real.sqrt k * c) (EuclideanSpace ℝ (UT n)) :=
  map_sum_scaled hc hξ hlaw (fun m => by
    have h := hindep.indepFun_sum_range_succ hξ m
    have e : (∑ j ∈ Finset.range m, ξ j) = fun ω => ∑ j ∈ Finset.range m, ξ j ω := by
      funext ω; rw [Finset.sum_apply]
    rwa [e] at h) k

end

end D5.S3.Arith.Lattices.Klartag.State.StateInvariant3
