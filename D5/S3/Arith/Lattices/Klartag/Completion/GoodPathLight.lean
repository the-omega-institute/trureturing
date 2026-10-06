/- GID: D5/S3/Arith/Lattices/Klartag/Completion/GoodPathLight
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/GoodPathLight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.State.StateSupply
import D5.S3.Arith.Lattices.Klartag.Completion.TerminalCount

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.GoodPathLight

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupR
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2R
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.State.StateSupply
open scoped ENNReal RealInnerProductSpace

section Restated

variable {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞} {C' : ℝ}

end Restated

section Bridge

end Bridge

section FreeDim

variable {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **`sum_free_ge`, corrected for a cut free dimension.**  `sum_free_ge` needs
`dim − |C_k| ≤ Nfun k ω` everywhere; when `Nfun` is cut at a stopping time that fails after it, and
the repair is the extra term `dim·∑_k P(bad k)`.  Everything else is `sum_free_ge`'s own argument. -/
theorem sum_free_ge_cut (Cset : ℕ → Ω → Finset ι) (Nfun : ℕ → Ω → ℝ)
    (Good : ℕ → Set Ω) (dd : ℝ) (Nsteps : ℕ)
    (hfree : ∀ k, k < Nsteps → ∀ ω ∈ Good k, dd - ((Cset k ω).card : ℝ) ≤ Nfun k ω)
    (hzero : ∀ k, k < Nsteps → ∀ ω, 0 ≤ Nfun k ω)
    (_hdd : 0 ≤ dd)
    (hmeasG : ∀ k, MeasurableSet (Good k))
    (hintN : ∀ k, k < Nsteps → Integrable (Nfun k) μ)
    (hintC : ∀ k, k < Nsteps → Integrable (fun ω => ((Cset k ω).card : ℝ)) μ) :
    ∑ k ∈ Finset.range Nsteps,
        (dd - ∫ ω, ((Cset k ω).card : ℝ) ∂μ - dd * μ.real (Good k)ᶜ)
      ≤ ∑ k ∈ Finset.range Nsteps, ∫ ω, Nfun k ω ∂μ := by
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.1 hk

  have hpt : ∀ ω, Set.indicator (Good k) (fun ω => dd - ((Cset k ω).card : ℝ)) ω ≤ Nfun k ω := by
    intro ω
    by_cases hg : ω ∈ Good k
    · rw [Set.indicator_of_mem hg]
      exact hfree k hk' ω hg
    · rw [Set.indicator_of_notMem hg]
      exact hzero k hk' ω
  have hintI : Integrable
      (Set.indicator (Good k) (fun ω => dd - ((Cset k ω).card : ℝ))) μ :=
    (((integrable_const dd).sub (hintC k hk')).indicator (hmeasG k))
  have hmono := integral_mono hintI (hintN k hk') hpt
  refine le_trans ?_ hmono

  have hintIc : Integrable (Set.indicator (Good k)ᶜ (fun ω => dd - ((Cset k ω).card : ℝ))) μ :=
    ((integrable_const dd).sub (hintC k hk')).indicator (hmeasG k).compl
  have hsum : ∀ ω, Set.indicator (Good k) (fun ω => dd - ((Cset k ω).card : ℝ)) ω
      + Set.indicator (Good k)ᶜ (fun ω => dd - ((Cset k ω).card : ℝ)) ω
      = dd - ((Cset k ω).card : ℝ) := by
    intro ω
    by_cases hg : ω ∈ Good k
    · rw [Set.indicator_of_mem hg, Set.indicator_of_notMem (by simpa using hg)]
      ring
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_mem (by simpa using hg)]
      ring
  have hadd : ∫ ω, (dd - ((Cset k ω).card : ℝ)) ∂μ
      = ∫ ω, Set.indicator (Good k) (fun ω => dd - ((Cset k ω).card : ℝ)) ω ∂μ
        + ∫ ω, Set.indicator (Good k)ᶜ (fun ω => dd - ((Cset k ω).card : ℝ)) ω ∂μ := by
    rw [← integral_add hintI hintIc]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hsum ω).symm)
  have hbd : ∫ ω, Set.indicator (Good k)ᶜ (fun ω => dd - ((Cset k ω).card : ℝ)) ω ∂μ
      ≤ dd * μ.real (Good k)ᶜ := by
    have hle : ∀ ω, Set.indicator (Good k)ᶜ (fun ω => dd - ((Cset k ω).card : ℝ)) ω
        ≤ Set.indicator (Good k)ᶜ (fun _ => dd) ω := by
      intro ω
      by_cases hg : ω ∈ (Good k)ᶜ
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
        have hc : (0 : ℝ) ≤ ((Cset k ω).card : ℝ) := Nat.cast_nonneg _
        linarith
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
    have hmono2 := integral_mono hintIc ((integrable_const dd).indicator (hmeasG k).compl) hle
    rwa [integral_indicator_const dd (hmeasG k).compl, smul_eq_mul, mul_comm] at hmono2
  rw [integral_sub (integrable_const dd) (hintC k hk'), integral_const] at hadd
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hadd
  linarith

end FreeDim

section Final

variable {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞}

end Final

end D5.S3.Arith.Lattices.Klartag.Completion.GoodPathLight
