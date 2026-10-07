/- GID: D5/S3/Arith/Lattices/Klartag/Drift/LogDetVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/LogDetVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second order log determinant bounds and accumulated drift. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.DriftAccumulated

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

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

namespace D5.S3.Arith.Lattices.Klartag.Drift.LogDetVariance

open MeasureTheory
open Matrix
open Finset
open Module
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

end Spectral

section Cone

variable {n : Type*} [Fintype n] [DecidableEq n]

end Cone

section Chain

variable {n : ℕ}

/-- `‖A⁻¹‖_op ≤ 1/m` from the state bounds. -/
theorem opNorm_inv_le {A : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹‖ ≤ 1 / m := by
  have hm := hSB.mpos
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have h := DriftStopped2.norm_inv_apply_le hSB y
  rw [div_eq_inv_mul] at h
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y‖ ≤ m⁻¹ * ‖y‖ := h
    _ = 1 / m * ‖y‖ := by rw [one_div]

end Chain

section Increment

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem condExp_inner_sq {V ξ : Ω → EuclideanSpace ℝ ι} {v : ℝ}
    (hξm : Measurable[mΩ] ξ)
    (hcov : ∀ p q : ι, ∫ ω, ξ ω p * ξ ω q ∂P = if p = q then v else 0)
    (hintprod : ∀ p q : ι, Integrable (fun ω => ξ ω p * ξ ω q) P)
    (hint : ∀ p q : ι, Integrable (fun ω => (V ω p * V ω q) * (ξ ω p * ξ ω q)) P)
    {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) [SigmaFinite (P.trim hℱ)]
    (hV : ∀ p, StronglyMeasurable[ℱ] fun ω => V ω p)
    (hind : ProbabilityTheory.Indep (MeasurableSpace.comap ξ inferInstance) ℱ P) :
    P[fun ω => (⟪V ω, ξ ω⟫ : ℝ) ^ 2 | ℱ] =ᵐ[P] fun ω => v * ‖V ω‖ ^ 2 := by
  classical
  letI : MeasurableSpace Ω := mΩ
  have hrw : (fun ω => (⟪V ω, ξ ω⟫ : ℝ) ^ 2)
      = fun ω => ∑ p, ∑ q, (V ω p * V ω q) * (ξ ω p * ξ ω q) := by
    funext ω
    have hin : (⟪V ω, ξ ω⟫ : ℝ) = ∑ p, V ω p * ξ ω p := by
      simp [PiLp.inner_apply, mul_comm]
    rw [hin, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [hrw]
  refine (StepInputs2.condExp_quadForm (M := fun ω p q => V ω p * V ω q) hℱ
    (fun p q => ((hV p).mul (hV q) :
      StronglyMeasurable[ℱ] fun ω => V ω p * V ω q)) hξm hind hcov hintprod hint).trans ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hnorm : ‖V ω‖ ^ 2 = ∑ p, V ω p * V ω p := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp [sq]
  simp only [hnorm]

end Increment

section Var

end Var

end D5.S3.Arith.Lattices.Klartag.Drift.LogDetVariance
