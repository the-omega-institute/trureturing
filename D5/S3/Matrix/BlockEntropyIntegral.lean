/- GID: D5/S3/Matrix/BlockEntropyIntegral
   generality: G
   mirror-B: none(waiver:covered-by-observer-crossed-product-entropy-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrating the strict trace-log gap for block pinching. -/

module

public import D5.S3.Matrix.BlockEntropy
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
Omega original.

Integrating the strict trace-log gap for block pinching.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
@[expose] public section

namespace Omega.Matrix.BlockEntropy

open _root_.Matrix _root_.MeasureTheory Set
open scoped ComplexOrder MatrixOrder CStarAlgebra Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The finite trace-log expression for matrices with input support in the reference support. -/
def traceLogDivergence (A B : Matrix n n ℂ) : ℝ :=
  (A * CFC.log A).trace.re - (A * CFC.log B).trace.re

omit [Fintype n] [DecidableEq n] in
/-- Block pinching is fixed by a second block pinching. -/
theorem energyPinching_idempotent (E : n → ℝ) (A : Matrix n n ℂ) :
    energyPinching E (energyPinching E A) = energyPinching E A := by
  ext i j
  by_cases h : E i = E j <;> simp [energyPinching, h]

omit [DecidableEq n] in
private theorem pinching_trace (E : n → ℝ) (A : Matrix n n ℂ) :
    (energyPinching E A).trace = A.trace := by simp [Matrix.trace, Matrix.diag, energyPinching]

private theorem trace_log_pinching (E : n → ℝ) (A B : Matrix n n ℂ)
    (hB : Commute B (energyDiagonal E)) :
    (energyPinching E A * CFC.log B).trace = (A * CFC.log B).trace :=
  trace_pinching_mul E A (CFC.log B) (hB.cfc_real Real.log)

private theorem traceLog_pinching_pythagoras (E : n → ℝ) (A B : Matrix n n ℂ)
    (hB : Commute B (energyDiagonal E)) :
    traceLogDivergence A B - traceLogDivergence (energyPinching E A) B =
      traceLogDivergence A (energyPinching E A) := by
  have hP := (energyPinching_eq_self_iff E (energyPinching E A)).mp (energyPinching_idempotent E A)
  simp only [traceLogDivergence, trace_log_pinching E A B hB,
    trace_log_pinching E A (energyPinching E A) hP]
  ring

/-- Against a centralizer reference the integrated trace-log difference equals the
nonnegative coherence loss, and vanishes precisely on centralizer-valued fields
almost everywhere for the state testing measure. -/
theorem integrated_pinching_defect {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (E : n → ℝ) (A : X → Matrix n n ℂ) (B : Matrix n n ℂ)
    (hpos : ∀ x, (A x).PosSemidef) (hB : Commute B (energyDiagonal E))
    (p c : X → ℝ) (hp : Measurable p) (hp₀ : ∀ x, 0 ≤ p x)
    (h₁ : Integrable (fun x => p x * (c x + traceLogDivergence (A x) B)) μ)
    (h₂ : Integrable (fun x => p x * (c x + traceLogDivergence (energyPinching E (A x)) B)) μ) :
    let d := (∫ x, p x * traceLogDivergence (A x) (energyPinching E (A x)) ∂μ);
    -(∫ x, p x * (c x + traceLogDivergence (energyPinching E (A x)) B) ∂μ) -
      -(∫ x, p x * (c x + traceLogDivergence (A x) B) ∂μ) = d ∧ 0 ≤ d ∧
      (d = 0 ↔ ∀ᵐ x ∂(μ.withDensity (fun y => ENNReal.ofReal (p y))),
        Commute (A x) (energyDiagonal E)) := by
  let f := fun x => p x * (c x + traceLogDivergence (A x) B)
  let g := fun x => p x * (c x + traceLogDivergence (energyPinching E (A x)) B)
  let d := fun x => p x * traceLogDivergence (A x) (energyPinching E (A x))
  have hdiff : d = fun x => f x - g x := by
    funext x
    dsimp [d, f, g]
    rw [← traceLog_pinching_pythagoras E (A x) B hB]
    ring
  have hK (x : X) : 0 ≤ traceLogDivergence (A x) (energyPinching E (A x)) ∧
      (traceLogDivergence (A x) (energyPinching E (A x)) = 0 ↔ A x = energyPinching E (A x)) :=
    trace_log_klein _ _ (hpos x) (pinching_pos E (hpos x)) (pinching_trace E (A x)).symm
      (pinching_kernel E (hpos x))
  have hnonneg (x : X) : 0 ≤ d x := mul_nonneg (hp₀ x) (hK x).1
  change -(∫ x, g x ∂μ) - -(∫ x, f x ∂μ) = (∫ x, d x ∂μ) ∧ 0 ≤ (∫ x, d x ∂μ) ∧ _
  refine ⟨?_, integral_nonneg hnonneg, ?_⟩
  · rw [hdiff, integral_sub (f := f) (g := g) h₁ h₂]
    ring
  · have hd : Integrable d μ := hdiff ▸ h₁.sub h₂
    rw [integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hnonneg) hd,
      ae_withDensity_iff hp.ennreal_ofReal]
    apply Filter.eventually_congr
    apply Filter.Eventually.of_forall
    intro x
    change d x = 0 ↔ _
    by_cases hx : p x = 0
    · simp [d, hx]
    · have hpx : 0 < p x := lt_of_le_of_ne (hp₀ x) (Ne.symm hx)
      simp [d, hx, ENNReal.ofReal_ne_zero_iff.mpr hpx, (hK x).2, eq_comm (a := A x),
        energyPinching_eq_self_iff]

end Omega.Matrix.BlockEntropy
