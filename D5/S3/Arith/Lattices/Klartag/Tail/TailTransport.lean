/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailTransport
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStep
import D5.S3.Arith.Lattices.Klartag.State.Padding
import D5.S3.Arith.Lattices.Klartag.State.StepGlue

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open ProbabilityTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open scoped ENNReal NNReal

/-- **The transport.**  `hitSet M N` does not read the padding coordinates, so its probability
under the padded measure is its probability under the chain's measure. -/
theorem measure_hitSet_fst {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} [SFinite P₁]
    {N : ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν] (M : ℕ → Ω₁ → ℝ) :
    (P₁.prod (Measure.pi fun _ : Fin N => ν)) (hitSet M N)
      = P₁ {ω₁ | ∃ k ≤ N, M k ω₁ ≤ 0} := by
  have hset : hitSet M N
      = ({ω₁ | ∃ k ≤ N, M k ω₁ ≤ 0} ×ˢ (Set.univ : Set (Fin N → ℝ))) := by
    ext ω; simp [hitSet, Set.mem_prod]
  rw [hset, Measure.prod_prod, measure_univ, mul_one]

/-- **Proposition 4.1 at horizon `t`, about the chain's measure alone.**  `Klartag`'s `M₀` is the
initial gap `a₀ − (α·r)⁻²` and `q = 1`, so the tail's argument is `yOf a₀ t (α·r)` — the profile's
own argument, by `TailAtStep.tail_arg_eq`. -/
theorem hit_tail_yOf {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P₁] {k : ℕ} {δ : ℝ≥0} {M c : ℕ → Ω₁ → ℝ}
    (hM : ∀ j, Measurable (M j)) (hc : ∀ i, Measurable (c i))
    {a₀ u t : ℝ} (ht : 0 < t) (hM₀ : 0 < a₀ - (u ^ 2)⁻¹)
    (hv : (((k • δ : ℝ≥0)) : ℝ) = t * 1 ^ 2)
    {inc : (Ω₁ × (Fin k → ℝ)) → (Fin k → ℝ)} (hincm : Measurable inc)
    (hincw : ∀ j : ℕ, j ≤ k → ∀ ω : Ω₁ × (Fin k → ℝ),
      walkSum j (inc ω) = -(paddedProc M (a₀ - (u ^ 2)⁻¹) c j ω))
    (hincl : (P₁.prod (Measure.pi fun _ : Fin k => gaussianReal 0 δ)).map inc
      = Measure.pi fun _ : Fin k => gaussianReal 0 δ) :
    P₁ {ω₁ | ∃ j ≤ k, M j ω₁ ≤ 0} ≤ ENNReal.ofReal (4 * Phi (yOf a₀ t u)) := by
  have h := padded_tail_of_increments hM hc ht one_pos hM₀ hv hincm hincw hincl
  rw [measure_hitSet_fst, tail_arg_eq] at h
  exact h

end D5.S3.Arith.Lattices.Klartag
