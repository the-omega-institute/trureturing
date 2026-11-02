/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.ProbDist.Basic
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.ProbDist.Support

/-!
# Couplings of probability laws

A **coupling** of laws `μ : ProbDist α` and `ν : ProbDist β` is a joint law `π : ProbDist (α × β)`
whose `Prod.fst`-marginal is `μ` and whose `Prod.snd`-marginal is `ν`. Every pair `(μ, ν)` admits
at least one coupling — the independent product `ProbDist.prod μ ν` — so the set of couplings is
always nonempty.

## Main definitions

* `IsCoupling μ ν π` — `π : ProbDist (α × β)` has first marginal `μ` and second marginal `ν`.

## Main statements

* `ProbDist.prod_isCoupling` — the independent product is a coupling of its factors.
* `exists_coupling` — every pair of laws admits a coupling.
* `IsCoupling.supportsOn_prod_set` — a coupling of laws supported on `s` and `t` is supported on
  `s ×ˢ t`.

## Tags

probability, coupling, joint distribution, marginal
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability

/-- `π : ProbDist (α × β)` is a **coupling** of laws `μ : ProbDist α`, `ν : ProbDist β`: Its
`Prod.fst`-marginal equals `μ` and its `Prod.snd`-marginal equals `ν`. -/
structure IsCoupling {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : ProbDist α) (ν : ProbDist β) (π : ProbDist (α × β)) : Prop where
  /-- The first marginal of `π` is `μ`. -/
  fst_marginal : ProbDist.map π Prod.fst measurable_fst = μ
  /-- The second marginal of `π` is `ν`. -/
  snd_marginal : ProbDist.map π Prod.snd measurable_snd = ν

/-- The product coupling has the correct marginals. -/
lemma ProbDist.prod_isCoupling {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : ProbDist α) (ν : ProbDist β) :
    IsCoupling μ ν (ProbDist.prod μ ν) := by
  refine ⟨?_, ?_⟩
  · apply ProbabilityMeasure.toMeasure_injective
    rw [ProbDist.map_toMeasure]
    exact Measure.fst_prod
  · apply ProbabilityMeasure.toMeasure_injective
    rw [ProbDist.map_toMeasure]
    exact Measure.snd_prod

/-- Non-emptiness of `Π(μ, ν)`: Every pair of laws has a coupling. -/
lemma exists_coupling {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : ProbDist α) (ν : ProbDist β) :
    ∃ π : ProbDist (α × β), IsCoupling μ ν π :=
  ⟨ProbDist.prod μ ν, ProbDist.prod_isCoupling μ ν⟩

namespace IsCoupling

/-- A coupling of laws supported on `s` and `t` is supported on `s ×ˢ t`. -/
lemma supportsOn_prod_set {μ ν : ProbDist ℝ} {π : ProbDist (ℝ × ℝ)}
    (hπ : IsCoupling μ ν π) {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμ : μ.supportsOn s) (hν : ν.supportsOn t) :
    π.toMeasure (s ×ˢ t) = 1 := by
  have hfst : π.toMeasure.fst = μ.toMeasure := by
    have heq := congrArg (fun d : ProbDist ℝ => (d : Measure ℝ)) hπ.fst_marginal
    simpa [Measure.fst, ProbDist.map_toMeasure] using heq
  have hsnd : π.toMeasure.snd = ν.toMeasure := by
    have heq := congrArg (fun d : ProbDist ℝ => (d : Measure ℝ)) hπ.snd_marginal
    simpa [Measure.snd, ProbDist.map_toMeasure] using heq
  have h_sfst : π.toMeasure (sᶜ ×ˢ (Set.univ : Set ℝ)) = 0 := by
    have hpre : (sᶜ ×ˢ (Set.univ : Set ℝ)) = Prod.fst ⁻¹' sᶜ := by
      ext ⟨x, y⟩; simp
    rw [hpre, ← Measure.fst_apply hs.compl, hfst]
    exact (MeasureTheory.prob_compl_eq_zero_iff hs).mpr hμ
  have h_stnd : π.toMeasure ((Set.univ : Set ℝ) ×ˢ tᶜ) = 0 := by
    have hpre : ((Set.univ : Set ℝ) ×ˢ tᶜ) = Prod.snd ⁻¹' tᶜ := by
      ext ⟨x, y⟩; simp
    rw [hpre, ← Measure.snd_apply ht.compl, hsnd]
    exact (MeasureTheory.prob_compl_eq_zero_iff ht).mpr hν
  have h_compl : (s ×ˢ t)ᶜ = sᶜ ×ˢ (Set.univ : Set ℝ) ∪ (Set.univ : Set ℝ) ×ˢ tᶜ := by
    ext ⟨x, y⟩; by_cases hx : x ∈ s <;> by_cases hy : y ∈ t <;> simp [hx, hy]
  have h_null : π.toMeasure (s ×ˢ t)ᶜ = 0 := by
    rw [h_compl]
    refine le_antisymm ?_ zero_le
    calc π.toMeasure (sᶜ ×ˢ (Set.univ : Set ℝ) ∪ (Set.univ : Set ℝ) ×ˢ tᶜ)
        ≤ π.toMeasure (sᶜ ×ˢ (Set.univ : Set ℝ))
            + π.toMeasure ((Set.univ : Set ℝ) ×ˢ tᶜ) := measure_union_le _ _
      _ = 0 := by rw [h_sfst, h_stnd]; simp
  exact (MeasureTheory.prob_compl_eq_zero_iff (hs.prod ht)).mp h_null

/-- A coupling with marginals concentrated on `Icc a b` is concentrated on the square. -/
lemma supportsOn_Icc_prod {a b : ℝ} {μ ν : ProbDist ℝ} {π : ProbDist (ℝ × ℝ)}
    (hπ : IsCoupling μ ν π) (hμ : μ.supportsOn (Icc a b)) (hν : ν.supportsOn (Icc a b)) :
    π.toMeasure (Icc a b ×ˢ Icc a b) = 1 :=
  hπ.supportsOn_prod_set measurableSet_Icc measurableSet_Icc hμ hν

end IsCoupling

/-- The product coupling of two laws supported on `Icc a b` is supported on the square. -/
lemma ProbDist.prod_supportsOn_Icc {a b : ℝ} {μ ν : ProbDist ℝ}
    (hμ : μ.supportsOn (Icc a b)) (hν : ν.supportsOn (Icc a b)) :
    (ProbDist.prod μ ν).toMeasure (Icc a b ×ˢ Icc a b) = 1 :=
  (ProbDist.prod_isCoupling μ ν).supportsOn_Icc_prod hμ hν

end Econlib.Probability
