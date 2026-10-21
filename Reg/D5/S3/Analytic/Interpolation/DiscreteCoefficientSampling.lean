/-
A faithful four-slot source registration for the original full
 discrete_coefficient_sampling_lower statement. Native scoped build and report
 artifacts carry the current kernel and registration evidence.

The selected operand is the actual coefficient p.coeff r in the left-hand
coefficient-energy sum, with its existing natural index binder r as state. Parameters are whole complex
polynomials, states are natural coefficient indices, and outputs are complex.
The actual readout is the function coercion of Polynomial.coeff p (the pinned
coefficient API returns a Finsupp). The rejected readout is constant one.
Only the selected coefficient occurrence changes in Law; the original
degree premise and every sampled polynomial evaluation remain unchanged.
The bridge is Iff.rfl for the entire theorem, with kappa before N and p.
Law rejection uses d=1, N=2 and p=0: the rejected coefficient sum is one and
the actual sample energy is zero. Dependence uses p=X at indices 0 and 1.

The lawful DependentFamily realization template and its enrollment are
imported directly. The four mathematical slots are bridge, variation,
sensitivity and observational dependence. Their compiled terms retain the full source telescope. There is one role and no anchors.

The source selector reaches the coefficient application beneath the norm and
square, retaining the original context [d,hd,kappa,N,hN,p,hp,r]. Coordinate 5
is the polynomial parameter and existing binder 7 is the natural state. This
selects the same coefficient family without synthesizing a fresh function
state. The first native report rejected functionOperand mode at
source.function_operand: the Finsupp coercion has a syntactically dependent
output in the raw function type. Ordinary existing-binder mode selects the
actual coefficient value and preserves the entire original Law.

-/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling

open scoped BigOperators
open Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev coefficientSignature : Signature.{0, 0, 0, 0, 0} where
  Params := Polynomial ℂ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ p r => p.coeff r) (fun e => nomatch e)

def coefficientRejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => (1 : ℂ)) (fun e => nomatch e)

private theorem coefficientDependence :
    ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  refine ⟨(X : ℂ[X]), (0 : ℕ), (1 : ℕ), ?_⟩
  norm_num [coefficientActual, realize]

def discrete_coefficient_sampling_lower_arena : Arena where
  signature := coefficientSignature
  Law R := ∀ (d : ℕ) (hd : 0 < d),
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 2 * d ≤ N →
      ∀ p : ℂ[X], p.natDegree < d →
        κ * (N : ℝ) * (∑ r ∈ Finset.range d, ‖R.readout () p r‖ ^ 2) ≤
          ∑ m ∈ Finset.Icc (N + 1) (2 * N),
            ‖p.eval ((m : ℂ) / (N : ℂ))‖ ^ 2

private theorem discrete_coefficient_sampling_lower_actual_law :
    discrete_coefficient_sampling_lower_arena.Law coefficientActual := by
  exact @_root_.D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling.discrete_coefficient_sampling_lower

private theorem discrete_coefficient_sampling_lower_rejected_law :
    ¬ discrete_coefficient_sampling_lower_arena.Law coefficientRejected := by
  intro hall
  obtain ⟨κ, hκ, h⟩ := hall 1 (by decide)
  have hz := h 2 (by decide) (0 : ℂ[X]) (by norm_num)
  norm_num [coefficientRejected, realize] at hz
  linarith

def discrete_coefficient_sampling_lower_family :
    Registration discrete_coefficient_sampling_lower_arena
      (type_of% (@_root_.D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling.discrete_coefficient_sampling_lower)) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨discrete_coefficient_sampling_lower_actual_law,
    coefficientRejected, discrete_coefficient_sampling_lower_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coefficientRejected, ?_, rfl,
        discrete_coefficient_sampling_lower_rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := coefficientDependence

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling.discrete_coefficient_sampling_lower)
    (type_of% coefficientActual) Type Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling.discrete_coefficient_sampling_lower.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling.discrete_coefficient_sampling_lower_family
  realizationSource := none
  generated := false
  arena := .source ⟨discrete_coefficient_sampling_lower_arena⟩
  objectArena := .source ⟨discrete_coefficient_sampling_lower_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source discrete_coefficient_sampling_lower_arena
    ⟨discrete_coefficient_sampling_lower_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature
    (fun _ p r => p.coeff r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "fn", "arg", "arg",
        "arg", "body", "fn", "arg", "arg"],
      stateBinder := 7,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling
