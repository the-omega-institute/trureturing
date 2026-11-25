import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.PureState.ReadingExponent
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the reading exponent.
The readout is the square `s ^ 2` on the right of the conclusion, as a function of `s`; the
function `F` and both hypotheses stay in the law verbatim. The square itself is multiplicative
and normalized on the quarter circle, which refutes the identity readout `s ↦ s`. -/

namespace Reg.D5.S3.Quantum.PureState.ReadingExponent

open _root_.D5.S3.Quantum.PureState.ReadingExponent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

namespace Square

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ s => s ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Retain the complete function and hypothesis telescope of `eq_sq_of_mul_of_cos_add_sin`;
only the square is read out. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (F : ℝ → ℝ),
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, F (s * t) = F s * F t) →
    (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), F (Real.cos t) + F (Real.sin t) = 1) →
    ∀ s ∈ Set.Icc (0 : ℝ) 1, F s = r.readout () () s

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun s => s ^ 2)
    (fun s _ t _ => mul_pow s t 2)
    (fun t _ => Real.cos_sq_add_sin_sq t)
    (1 / 2) ⟨by norm_num, by norm_num⟩
  norm_num [rejected, realize] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @eq_sq_of_mul_of_cos_add_sin

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eq_sq_of_mul_of_cos_add_sin, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

end Square

def eq_sq_of_mul_of_cos_add_sin_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@eq_sq_of_mul_of_cos_add_sin) (Realization Square.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.PureState.ReadingExponent.eq_sq_of_mul_of_cos_add_sin_unit
  realizationName := `Reg.D5.S3.Quantum.PureState.ReadingExponent.Square.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Square.arena⟩
  objectArena := .source ⟨Square.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Square.arena ⟨Square.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Square.signature (fun _ _ s => s ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.PureState.ReadingExponent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.PureState.ReadingExponent
