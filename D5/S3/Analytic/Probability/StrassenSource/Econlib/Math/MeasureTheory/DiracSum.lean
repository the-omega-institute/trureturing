/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Finitely supported measures as finite sums of Diracs

A probability measure carried by a finite set `S` is a finite weighted **sum of Diracs**, and its
integrals collapse to finite sums over `S`. This file records the measure decomposition, the
corresponding collapse of the Bochner integral, and the compatibility of pushforward with finite
sums of measures.

## Main statements

* `MeasureTheory.integral_eq_finset_sum_of_support` — `∫ f ∂μ = ∑ x ∈ S, μ{x} · f x` when `μ S = 1`
  and `f` is integrable.
* `MeasureTheory.measure_eq_finset_sum_dirac_of_support` — `μ = ∑ x ∈ S, μ{x} • dirac x` when
  `μ S = 1`.
* `MeasureTheory.measure_map_finset_sum` — pushforward commutes with finite sums of measures.

## Tags

dirac measure, sum of diracs, finite support, probability measure, pushforward
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

/-- For a probability measure `μ` carried by the finite set `S` (that is, `μ S = 1`), the Bochner
integral of an integrable `f` collapses to the finite sum `∑ x ∈ S, μ{x} · f x`. -/
lemma integral_eq_finset_sum_of_support {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    {S : Finset Ω} {μ : ProbabilityMeasure Ω} (hμ_supp : μ.toMeasure (S : Set Ω) = 1)
    {f : Ω → ℝ} (hf : Integrable f μ.toMeasure) :
    ∫ x, f x ∂μ.toMeasure = ∑ x ∈ S, μ.toMeasure.real {x} * f x := by
  classical
  have hS_meas : MeasurableSet (S : Set Ω) := Finset.measurableSet S
  have hS_ne_top : μ.toMeasure (S : Set Ω) ≠ ⊤ := by
    rw [hμ_supp]
    exact ENNReal.one_ne_top
  have hcompl_zero : μ.toMeasure ((S : Set Ω)ᶜ) = 0 := by
    rw [measure_compl hS_meas hS_ne_top, hμ_supp, measure_univ]
    simp
  have hcompl_int : ∫ x in (S : Set Ω)ᶜ, f x ∂μ.toMeasure = 0 :=
    setIntegral_measure_zero f hcompl_zero
  have hadd := integral_add_compl hS_meas hf
  have hrestrict :
      ∫ x in (S : Set Ω), f x ∂μ.toMeasure = ∑ x ∈ S, μ.toMeasure.real {x} * f x := by
    rw [setIntegral_finset]
    · simp [smul_eq_mul, mul_comm]
    · exact hf.integrableOn
  linarith

/-- A probability measure `μ` carried by the finite set `S` (that is, `μ S = 1`) is the finite
weighted sum of Diracs `∑ x ∈ S, μ{x} • dirac x`. -/
lemma measure_eq_finset_sum_dirac_of_support {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    {S : Finset Ω} {μ : ProbabilityMeasure Ω} (hμ_supp : μ.toMeasure (S : Set Ω) = 1) :
    μ.toMeasure = ∑ x ∈ S, μ.toMeasure {x} • Measure.dirac x := by
  classical
  have hS_meas : MeasurableSet (S : Set Ω) := Finset.measurableSet S
  have hS_ne_top : μ.toMeasure (S : Set Ω) ≠ ⊤ := by
    rw [hμ_supp]
    exact ENNReal.one_ne_top
  have hcompl_zero : μ.toMeasure ((S : Set Ω)ᶜ) = 0 := by
    rw [measure_compl hS_meas hS_ne_top, hμ_supp, measure_univ]
    simp
  have hae : ∀ᵐ x ∂μ.toMeasure, x ∈ S := by
    rw [ae_iff]
    change μ.toMeasure (({a | a ∈ S})ᶜ) = 0
    exact hcompl_zero
  exact (Measure.ae_mem_finset_iff (μ := μ.toMeasure) (s := S)).mp hae

/-- Pushforward by a measurable map commutes with a finite sum of measures:
`(∑ i ∈ s, m i).map f = ∑ i ∈ s, (m i).map f`. -/
lemma measure_map_finset_sum {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f)
    {s : Finset ι} (m : ι → Measure α) :
    Measure.map f (∑ i ∈ s, m i) = ∑ i ∈ s, Measure.map f (m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.map_zero]
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has,
        Measure.map_add _ _ hf, ih]

end MeasureTheory
