import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.LiteralExceptionalCoprimality
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.LiteralExceptionalCoprimality
open Polynomial
open _root_.D5.S3.Observer.CubicGain.ExactW3Center
open _root_.D5.S3.Observer.CubicGain.LiteralExceptionalCoprimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Polynomial ℝ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ p => by classical exact decide (IsCoprime criticalPolynomial p))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (exceptionalFactor : Polynomial ℤ).natDegree = 133 ∧
    R.readout () () (exceptionalFactor : Polynomial ℝ) = true

private theorem rejected_law : ¬ arena.Law rejected := by
  simp [arena, rejected, realize]

private theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize] using displayed_exceptional_factor_coprime

private theorem dependence : ObservationalDependence signature actual := by
  have hn : ¬ IsUnit criticalPolynomial := by
    intro hu
    have h0 := (Polynomial.isUnit_iff_degree_eq_zero).mp hu
    rw [critical_root_exists.1] at h0
    norm_num at h0
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [actual, realize, isCoprime_zero_right, hn, isCoprime_one_right]

def source_registration : Registration arena (type_of% @displayed_exceptional_factor_coprime) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@displayed_exceptional_factor_coprime) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.LiteralExceptionalCoprimality.displayed_exceptional_factor_coprime.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.LiteralExceptionalCoprimality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ p => by classical exact decide (IsCoprime criticalPolynomial p))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.LiteralExceptionalCoprimality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Observer.CubicGain.LiteralExceptionalCoprimality
