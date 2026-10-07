/- GID: D5/S3/Arith/Lattices/Klartag/Contact/ContactIntegrated
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/ContactIntegrated
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
import D5.S3.Arith.Lattices.Klartag.Walk.ChainInputDom
import D5.S3.Arith.Lattices.Klartag.Walk.ChainDrift

open MeasureTheory
open Finset

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Contact.ContactIntegrated

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]

noncomputable def intWeight (μ : Measure Ω) (Cset : ℕ → Ω → Finset ι) (hstep : ℝ)
    (Nsteps : ℕ) (x : ι) : ℝ :=
  ∑ k ∈ range Nsteps, hstep * μ.real {ω | x ∈ Cset k ω}

/-- The expected contact count at one step is the window sum of per-time contact probabilities. -/
theorem integral_card_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Finset ι)
    (Cs : Ω → Finset ι) (hsub : ∀ ω, Cs ω ⊆ W)
    (hmeas : ∀ x ∈ W, MeasurableSet {ω | x ∈ Cs ω}) :
    ∫ ω, ((Cs ω).card : ℝ) ∂μ = ∑ x ∈ W, μ.real {ω | x ∈ Cs ω} := by
  classical
  have hcard : ∀ ω, ((Cs ω).card : ℝ)
      = ∑ x ∈ W, Set.indicator {ω | x ∈ Cs ω} (fun _ => (1 : ℝ)) ω := by
    intro ω
    have hfil : W.filter (fun x => x ∈ Cs ω) = Cs ω := by
      ext x; simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub ω h, h⟩⟩
    rw [← hfil, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x ∈ Cs ω <;> simp [Set.indicator, hx]
  have hint : ∀ x ∈ W, Integrable
      (fun ω => Set.indicator {ω | x ∈ Cs ω} (fun _ => (1 : ℝ)) ω) μ :=
    fun x hx => (integrable_const (1 : ℝ)).indicator (hmeas x hx)
  calc ∫ ω, ((Cs ω).card : ℝ) ∂μ
      = ∫ ω, ∑ x ∈ W, Set.indicator {ω | x ∈ Cs ω} (fun _ => (1 : ℝ)) ω ∂μ := by simp_rw [hcard]
    _ = ∑ x ∈ W, ∫ ω, Set.indicator {ω | x ∈ Cs ω} (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_finsetSum W hint
    _ = ∑ x ∈ W, μ.real {ω | x ∈ Cs ω} :=
        Finset.sum_congr rfl (fun x hx => integral_indicator_one (hmeas x hx))

theorem integrated_count_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Finset ι)
    (Cset : ℕ → Ω → Finset ι) (hstep : ℝ) (Nsteps : ℕ)
    (hsub : ∀ k ω, Cset k ω ⊆ W)
    (hmeas : ∀ k, ∀ x ∈ W, MeasurableSet {ω | x ∈ Cset k ω}) :
    ∑ k ∈ range Nsteps, hstep * ∫ ω, ((Cset k ω).card : ℝ) ∂μ
      = ∑ x ∈ W, intWeight μ Cset hstep Nsteps x := by
  simp_rw [intWeight]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_card_eq μ W (Cset k) (hsub k) (hmeas k), Finset.mul_sum]

end D5.S3.Arith.Lattices.Klartag.Contact.ContactIntegrated
