/- GID: D5/S3/Arith/Lattices/Klartag/Completion/TerminalCount
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/TerminalCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8

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

namespace D5.S3.Arith.Lattices.Klartag.Completion.TerminalCount

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup
open scoped ENNReal RealInnerProductSpace

section Terminal

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
  {A₀ : EuclideanSpace ℝ (UT n)} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {α : ℝ}

end Terminal

section Count

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The drift side's second count bound.**  With the terminal weight summed below `θT` on the
window the chain is run on, the count event fails with probability at most `2θT/c₃`. -/
theorem countGood_of_terminal_weight (hξ : ∀ k, Measurable (ξ k)) {K : ℕ} {c₃ : ℝ}
    (hc₃ : 0 < c₃) (weight : ι → ℝ)
    (htail : ∀ i ∈ W, P.real {ω | i ∈ (Chain.chain q W A₀ ξ K ω).2} ≤ 2 * weight i + 0)
    {θT : ℝ} (hθ : ∑ i ∈ W, weight i ≤ θT) :
    P.real (StateInvariant4.countGood q W A₀ ξ K c₃)ᶜ ≤ (2 * θT + 0) / c₃ :=
  StateInvariant4.measureReal_compl_countGood_le_expected hξ hc₃ weight (fun _ => 0) htail hθ
    (by simp)

end Count

theorem sums_of_combined {ι : Type*} {S : Finset ι} {w₁ w₂ : ι → ℝ≥0∞} {c₁ c₂ θ₁ θ₂ : ℝ≥0∞}
    (h : ∑ y ∈ S, (c₁ * w₁ y + c₂ * w₂ y) < 1)
    (h₁ : 1 ≤ c₁ * θ₁) (h₂ : 1 ≤ c₂ * θ₂) :
    (∑ y ∈ S, w₁ y) < θ₁ ∧ (∑ y ∈ S, w₂ y) < θ₂ := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  constructor
  · by_contra hcon
    have hge : θ₁ ≤ ∑ y ∈ S, w₁ y := not_lt.1 hcon
    have hmul : c₁ * θ₁ ≤ c₁ * ∑ y ∈ S, w₁ y := by gcongr
    have hle : c₁ * (∑ y ∈ S, w₁ y) ≤ c₁ * (∑ y ∈ S, w₁ y) + c₂ * (∑ y ∈ S, w₂ y) := le_self_add
    exact absurd (lt_of_le_of_lt hle h) (not_lt.2 (le_trans h₁ hmul))
  · by_contra hcon
    have hge : θ₂ ≤ ∑ y ∈ S, w₂ y := not_lt.1 hcon
    have hmul : c₂ * θ₂ ≤ c₂ * ∑ y ∈ S, w₂ y := by gcongr
    have hle : c₂ * (∑ y ∈ S, w₂ y) ≤ c₁ * (∑ y ∈ S, w₁ y) + c₂ * (∑ y ∈ S, w₂ y) := le_add_self
    exact absurd (lt_of_le_of_lt hle h) (not_lt.2 (le_trans h₂ hmul))

end D5.S3.Arith.Lattices.Klartag.Completion.TerminalCount
