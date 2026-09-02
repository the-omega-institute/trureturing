/- GID: D5/S3/ContinuousObservables/DerivativeParityReadout
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/DerivativeParityReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The derivative readout of an even periodic scalar field is odd and periodic under the same translations. -/

import Mathlib

/-!
The source atom's concrete `Z_unit` and its parameter `s` are not defined in
the current Lean library.  We therefore expose them as a family of real
functions.  The self-contained classical content is that differentiation
transports reflection oddness and translation periodicity from the scalar
field to its derivative readout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ContinuousObservables.DerivativeParityReadout

/- The balanced field is the eta derivative of an externally supplied scalar field. -/
def balancedField {S : Type*} (Zunit : S → ℝ → ℝ) (s : S) (eta : ℝ) : ℝ :=
  deriv (fun u => Zunit s u) eta

/-- Reflection-even scalar data have an odd derivative readout. -/
theorem balanced_field_reflection_odd
    {S : Type*} {Zunit : S → ℝ → ℝ}
    (hDifferentiable : ∀ s eta,
      DifferentiableAt ℝ (fun u => Zunit s u) eta)
    (hEven : ∀ s eta, Zunit s (-eta) = Zunit s eta) :
    ∀ s eta, balancedField Zunit s (-eta) = -balancedField Zunit s eta := by
  intro s eta
  unfold balancedField
  have hReflected :
      HasDerivAt (fun x : ℝ => Zunit s (-x))
        (deriv (fun u => Zunit s u) (-eta) * (-1 : ℝ)) eta := by
    have hOuter := (hDifferentiable s (-eta)).hasDerivAt
    have hNeg := hOuter.comp eta (hasDerivAt_neg eta)
    simpa [Function.comp_def] using hNeg
  have hSame : (fun x : ℝ => Zunit s (-x)) = (fun x => Zunit s x) := by
    funext x
    exact hEven s x
  rw [hSame] at hReflected
  have hAtEta := (hDifferentiable s eta).hasDerivAt
  have hUnique := hReflected.unique hAtEta
  linarith

/-- A periodic scalar field has a derivative readout with the same period. -/
theorem balanced_field_periodic
    {S : Type*} {Zunit : S → ℝ → ℝ}
    (period : ℝ)
    (hDifferentiable : ∀ s eta,
      DifferentiableAt ℝ (fun u => Zunit s u) eta)
    (hPeriodic : ∀ s eta, Zunit s (eta + period) = Zunit s eta) :
    ∀ s eta, balancedField Zunit s (eta + period) =
      balancedField Zunit s eta := by
  intro s eta
  unfold balancedField
  have hTranslate :
      (fun x : ℝ => Zunit s (x + period)) = (fun x : ℝ => Zunit s x) := by
    funext x
    exact hPeriodic s x
  have hAtTranslate := (hDifferentiable s (eta + period)).hasDerivAt
  have hTranslateDerivative :
      HasDerivAt (fun x : ℝ => Zunit s (x + period))
        (deriv (fun u => Zunit s u) (eta + period)) eta := by
    have hOuter := hAtTranslate
    have hAdd := (hasDerivAt_id eta).add_const period
    have hComp := hOuter.comp eta hAdd
    simpa [Function.comp_def, add_comm] using hComp
  rw [hTranslate] at hTranslateDerivative
  exact hTranslateDerivative.deriv.symm

/- A concrete even field witnesses the reflection theorem. -/
example :
    balancedField (fun _ : Unit => fun eta : ℝ => eta ^ 2) () (-3) =
      -balancedField (fun _ : Unit => fun eta : ℝ => eta ^ 2) () 3 := by
  apply balanced_field_reflection_odd
  · intro s eta
    fun_prop
  · intro s eta
    simp [pow_two]

/- If evenness is removed, the derivative oddness conclusion can fail. -/
example :
    balancedField (fun _ : Unit => fun eta : ℝ => eta) () (-1) ≠
      -balancedField (fun _ : Unit => fun eta : ℝ => eta) () 1 := by
  norm_num [balancedField]

#print axioms balanced_field_reflection_odd
#print axioms balanced_field_periodic

end D5.S3.ContinuousObservables.DerivativeParityReadout
