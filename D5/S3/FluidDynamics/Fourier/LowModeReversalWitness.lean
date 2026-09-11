/- GID: D5/S3/FluidDynamics/Fourier/LowModeReversalWitness
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/LowModeReversalWitness
   mirror-E: none(waiver:exact-symbolic-Fourier-family)
   anchors: []
   utility: none
   digest: An explicit two-amplitude incompressible Fourier family has identical low-mode reversals and distinct Leray-projected accelerations. -/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact full/partial reversal in Fourier coordinates

The fields are alpha*(0,cos x,0)+beta*(cos(y-x),cos(y-x),0).
The four input frequencies are (1,0),(-1,0),(-1,1),(1,-1), with third
coordinate zero. `coefficient` collects equal input frequencies; `advection`
computes all sixteen convolution interactions; `leray` applies the actual
pressure-eliminating Fourier multiplier. No output coefficient is supplied
as a premise or taken from a numerical solver.

Every integer output frequency is retained in the definitions. The observation
is the complete |k|^2 <= 1 cutoff, not a selected input slot. The theorem's
error bound is for one complex Fourier coefficient. No Parseval theorem,
continuum solution existence, nonlinear trajectory error, or blowup is claimed.
The Fourier differential multiplier convention is documented in the theory;
its equivalence with arbitrary Sobolev/Frechet PDE definitions is separate.

Source: NS_OBSERVER_DYNAMICS_RH_THEORY, Proposition 5.2. Prior context:
Fang--Bos--Shao--Bertoglio, arXiv:1112.0659. Searches for Navier, Leray and
FourierPolynomial found no existing fluid-mode owner in the pinned dev.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.LowModeReversalWitness

open scoped BigOperators

/-- Integer planar frequencies, embedded in three-space with zero third entry. -/
abbrev Mode := ℤ × ℤ

/-- Three velocity components. -/
abbrev Amplitude := Fin 3 → ℂ

/-- The exact integer squared frequency, with no floating comparison. -/
def frequencySquared (k : Mode) : ℤ := k.1 ^ 2 + k.2 ^ 2

/-- The four modes of the two real cosine waves. -/
def frequency (j : Fin 4) : Mode :=
  if j = 0 then (1, 0) else if j = 1 then (-1, 0)
  else if j = 2 then (-1, 1) else (1, -1)

/-- Real cosine amplitudes split equally across each conjugate frequency pair. -/
def inputAmplitude (alpha beta : ℝ) (j : Fin 4) (c : Fin 3) : ℂ :=
  if j.val < 2 then (if c = 1 then (alpha : ℂ) / 2 else 0)
  else (if c.val < 2 then (beta : ℂ) / 2 else 0)

/-- Actual coefficient, summing every occurrence of an input frequency. -/
def coefficient (alpha beta : ℝ) (k : Mode) (c : Fin 3) : ℂ :=
  ∑ j : Fin 4, if frequency j = k then inputAmplitude alpha beta j c else 0

/-- The full low-frequency coefficient function. -/
def lowObservation (alpha beta : ℝ) : Mode → Amplitude :=
  fun k c => if frequencySquared k ≤ 1 then coefficient alpha beta k c else 0

/-- Fourier coefficient of (u dot grad)u, computed by the full input convolution. -/
def advection (alpha beta : ℝ) (k : Mode) (c : Fin 3) : ℂ :=
  Complex.I * ∑ i : Fin 4, ∑ j : Fin 4,
    if frequency i + frequency j = k then
      (((frequency j).1 : ℂ) * inputAmplitude alpha beta i 0 +
       ((frequency j).2 : ℂ) * inputAmplitude alpha beta i 1) *
        inputAmplitude alpha beta j c
    else 0

/-- Leray's multiplier I-kk^T/|k|^2, including the identity at k=0.
The zero-frequency formula is meaningful because both wave coordinates vanish. -/
def leray (k : Mode) (w : Amplitude) : Amplitude := fun c =>
  w c - (if c = 0 then (k.1 : ℂ) else if c = 1 then (k.2 : ℂ) else 0) *
    ((k.1 : ℂ) * w 0 + (k.2 : ℂ) * w 1) / (frequencySquared k : ℂ)

/-- The actual viscous Fourier multiplier minus the Leray-projected nonlinearity. -/
def acceleration (nu alpha beta : ℝ) (k : Mode) (c : Fin 3) : ℂ :=
  -(nu : ℂ) * (frequencySquared k : ℂ) * coefficient alpha beta k c -
    leray k (advection alpha beta k) c

/-- Every input coefficient is perpendicular to its actual frequency. -/
theorem input_divergence_free (alpha beta : ℝ) (j : Fin 4) :
    ((frequency j).1 : ℂ) * inputAmplitude alpha beta j 0 +
      ((frequency j).2 : ℂ) * inputAmplitude alpha beta j 1 = 0 := by
  fin_cases j <;> norm_num [frequency, inputAmplitude, Fin.ext_iff]

/-- Equal real amplitudes at each opposite-frequency pair. -/
theorem conjugate_pair_data (alpha beta : ℝ) :
    frequency 1 = -frequency 0 ∧ frequency 3 = -frequency 2 ∧
    inputAmplitude alpha beta 0 = inputAmplitude alpha beta 1 ∧
    inputAmplitude alpha beta 2 = inputAmplitude alpha beta 3 := by
  constructor
  · decide
  constructor
  · decide
  constructor <;> funext c <;> simp [inputAmplitude]

/-- The low observation forgets beta at every output frequency and component. -/
theorem lowObservation_independent (alpha beta beta' : ℝ) :
    lowObservation alpha beta = lowObservation alpha beta' := by
  funext k c
  by_cases hk : frequencySquared k ≤ 1
  · have hleft : (-1, 1) ≠ k := by
      intro heq
      subst k
      norm_num [frequencySquared] at hk
    have hright : (1, -1) ≠ k := by
      intro heq
      subst k
      norm_num [frequencySquared] at hk
    simp [lowObservation, hk, coefficient, Fin.sum_univ_succ,
      frequency, inputAmplitude, hleft, hright]
  · simp [lowObservation, hk]

/-- The output coefficient is derived symbolically for every viscosity and
both continuous amplitudes. It is not an assumed finite table entry. -/
theorem transverse_acceleration (nu alpha beta : ℝ) :
    acceleration nu alpha beta (0, 1) 0 =
      -Complex.I * (alpha : ℂ) * (beta : ℂ) / 4 := by
  simp only [acceleration, coefficient, leray, advection, Fin.sum_univ_four]
  norm_num [frequencySquared, frequency, inputAmplitude, Prod.mk_add_mk,
    Prod.mk.injEq, Fin.ext_iff]
  ring

/-- Full reversal (-1,-1) and visible-only reversal (-1,1) have the same
entire low-frequency state and a nonzero low-frequency acceleration gap. -/
theorem full_partial_reversal_separation (nu : ℝ) :
    lowObservation (-1) (-1) = lowObservation (-1) 1 ∧
    acceleration nu (-1) (-1) (0, 1) 0 -
      acceleration nu (-1) 1 (0, 1) 0 = -Complex.I / 2 := by
  refine ⟨lowObservation_independent (-1) (-1) 1, ?_⟩
  rw [transverse_acceleration, transverse_acceleration]
  norm_num
  ring

/-- Every deterministic predictor from the same complete low-mode state has
error at least 1/4 on one of the two actual complex acceleration coefficients. -/
theorem low_mode_prediction_error_floor (nu : ℝ)
    (predict : (Mode → Amplitude) → ℂ) :
    (1 / 4 : ℝ) ≤ max
      ‖acceleration nu (-1) (-1) (0, 1) 0 - predict (lowObservation (-1) (-1))‖
      ‖acceleration nu (-1) 1 (0, 1) 0 - predict (lowObservation (-1) 1)‖ := by
  let a := acceleration nu (-1) (-1) (0, 1) 0
  let b := acceleration nu (-1) 1 (0, 1) 0
  let z := predict (lowObservation (-1) (-1))
  have hp : predict (lowObservation (-1) 1) = z := by
    dsimp [z]
    rw [lowObservation_independent (-1) 1 (-1)]
  change (1 / 4 : ℝ) ≤ max ‖a - z‖ ‖b - predict (lowObservation (-1) 1)‖
  rw [hp]
  have hgap : ‖a - b‖ = (1 / 2 : ℝ) := by
    dsimp [a, b]
    rw [(full_partial_reversal_separation nu).2]
    norm_num [Complex.norm_div, Complex.norm_I]
  have htriangle : ‖a - b‖ ≤ ‖a - z‖ + ‖b - z‖ := by
    have hid : a - b = (a - z) - (b - z) := by ring
    rw [hid]
    exact norm_sub_le _ _
  rw [hgap] at htriangle
  have hleft := le_max_left ‖a - z‖ ‖b - z‖
  have hright := le_max_right ‖a - z‖ ‖b - z‖
  linarith

/-- No state-only predictor can recover this actual low acceleration on the
whole two-amplitude family, including for every fixed positive viscosity. -/
theorem no_low_mode_acceleration_closure (nu : ℝ) :
    ¬ ∃ predict : (Mode → Amplitude) → ℂ,
      ∀ alpha beta : ℝ,
        predict (lowObservation alpha beta) = acceleration nu alpha beta (0, 1) 0 := by
  rintro ⟨predict, hpredict⟩
  have h := low_mode_prediction_error_floor nu predict
  simp only [hpredict (-1) (-1), hpredict (-1) 1, sub_self,
    norm_zero, max_self] at h
  norm_num at h

#print axioms Mode
#print axioms Amplitude
#print axioms frequencySquared
#print axioms frequency
#print axioms inputAmplitude
#print axioms coefficient
#print axioms lowObservation
#print axioms advection
#print axioms leray
#print axioms acceleration
#print axioms input_divergence_free
#print axioms conjugate_pair_data
#print axioms lowObservation_independent
#print axioms transverse_acceleration
#print axioms full_partial_reversal_separation
#print axioms low_mode_prediction_error_floor
#print axioms no_low_mode_acceleration_closure

end D5.S3.FluidDynamics.Fourier.LowModeReversalWitness
