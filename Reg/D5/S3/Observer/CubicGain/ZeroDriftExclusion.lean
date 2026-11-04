import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.ZeroDriftExclusion
import Reg.Support.SingleDependentReadout

/-! The complete parent predicate on the unrestricted original-world carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.ZeroDriftExclusion
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => OriginalWorld) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ => OriginalParent) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (W : OriginalWorld), R.readout () () W → W.2.2.1 = 0 →
    (originalPolynomial W).eval 7 ≠ 0

private def good : OriginalWorld :=
  (1/2,1/8,24,![-24,184/5,-72/5,8/5])

private def bad : OriginalWorld := (0,0,0,![0,0,0,0])

private theorem good_parent : OriginalParent good := by
  refine ⟨by norm_num [good],by norm_num [good],by norm_num [good],?_,?_⟩
  · intro h
    have hh := congrArg (fun p : Polynomial ℝ => p.eval 0) h
    norm_num [good,originalPolynomial,Polynomial.ofFn_eq_sum_monomial,
      Fin.sum_univ_four] at hh
  · intro i
    fin_cases i <;>
      norm_num [good,originalRead,history,originalPolynomial,
        Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four,chronological,
        sourceMatrix,actionJ,actionM,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h bad trivial rfl
  norm_num [bad,originalPolynomial,Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_four] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),good,bad,?_⟩
  intro h
  have hb : OriginalParent bad := Eq.mp h good_parent
  norm_num [OriginalParent,bad] at hb

def source_registration :
    Registration arena (type_of% @original_zero_drift_terminal_gain_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_zero_drift_terminal_gain_ne_zero,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@original_zero_drift_terminal_gain_ne_zero) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.ZeroDriftExclusion.original_zero_drift_terminal_gain_ne_zero.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.ZeroDriftExclusion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => OriginalParent) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.ZeroDriftExclusion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","domain","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Reg.D5.S3.Observer.CubicGain.ZeroDriftExclusion
