import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier
open _root_.D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Circuit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => angle t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : Circuit,
    (valid t ∧ phase t = (-1, 0)) ↔ leaves t ∧ R.readout () () t = 2 * Real.pi

private theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  let t := Circuit.mul (.leaf Real.pi) (.leaf Real.pi)
  have ht : leaves t ∧ angle t = 2 * Real.pi := by
    refine ⟨⟨⟨Real.pi_pos.le,le_rfl⟩,⟨Real.pi_pos.le,le_rfl⟩⟩,?_⟩
    change Real.pi+Real.pi=2*Real.pi
    ring
  have hh := ((bad t).mp ((stationary_iff t).mpr ht)).2
  change (0:ℝ)=2*Real.pi at hh
  linarith [Real.pi_pos]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(),Circuit.leaf 0,Circuit.leaf Real.pi,?_⟩
  change (0:ℝ)≠Real.pi
  exact Real.pi_pos.ne

def source_registration : Registration arena (type_of% @stationary_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stationary_iff,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stationary_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier.stationary_iff.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => angle t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","arg","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier
