import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.LiteralCriticalCoprimality
import Reg.Support.SingleDependentReadout
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.LiteralCriticalCoprimality
open Polynomial
open _root_.D5.S3.Observer.CubicGain.ExactW3Center
open _root_.D5.S3.Observer.CubicGain.LiteralCriticalCoprimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace derivative
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Polynomial ℝ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ _ p => by classical exact decide (IsCoprime criticalPolynomial p)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () criticalPolynomial.derivative = true
private theorem rejected_law : ¬ arena.Law rejected := by simp [arena, rejected, realize]
private theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize] using critical_polynomial_is_coprime_derivative
private theorem dependence : ObservationalDependence signature actual := by
  have hn : ¬ IsUnit criticalPolynomial := by
    intro hu
    have h0 := Polynomial.isUnit_iff_degree_eq_zero.mp hu
    rw [critical_root_exists.1] at h0
    norm_num at h0
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [actual, realize, isCoprime_zero_right, hn, isCoprime_one_right]
def source_registration : Registration arena (type_of% @critical_polynomial_is_coprime_derivative) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@critical_polynomial_is_coprime_derivative) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.LiteralCriticalCoprimality.critical_polynomial_is_coprime_derivative.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.LiteralCriticalCoprimality.derivative.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => by classical exact decide (IsCoprime criticalPolynomial p)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.LiteralCriticalCoprimality
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
end derivative

namespace normalization
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Polynomial ℤ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ _ p => by classical exact decide p.IsPrimitive) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∃ f : Polynomial ℤ, f.map (Int.castRingHom ℝ) = criticalPolynomial ∧
    f.natDegree = 67 ∧ R.readout () () f = true ∧ 0 < f.leadingCoeff
private theorem rejected_law : ¬ arena.Law rejected := by simp [arena, rejected, realize]
private theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize] using literal_critical_integer_normalization
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  have hz : ¬ (0 : Polynomial ℤ).IsPrimitive := fun h => h.ne_zero rfl
  simp [actual, realize, hz]
def source_registration : Registration arena (type_of% @literal_critical_integer_normalization) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@literal_critical_integer_normalization) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.LiteralCriticalCoprimality.literal_critical_integer_normalization.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.LiteralCriticalCoprimality.normalization.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => by classical exact decide p.IsPrimitive) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.LiteralCriticalCoprimality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg","body","arg","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end normalization

end Reg.D5.S3.Observer.CubicGain.LiteralCriticalCoprimality
