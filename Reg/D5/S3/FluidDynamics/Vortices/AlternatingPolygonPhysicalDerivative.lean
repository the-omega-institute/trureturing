import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
noncomputable section
open scoped BigOperators
open Matrix Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters (Configuration)
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
namespace Relation_physical_cartesian_chain
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 1 ≤ m)
    {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () () (physicalRealOperator m b Ω (cartesian0 m) = 0) (physicalRealOperator m b Ω ((2 * Ω)⁻¹ • cartesian1 m) = cartesian0 m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ∧ True := Eq.mp (congrFun he True) ⟨trivial, trivial⟩
  exact hf.1
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative.physical_cartesian_chain) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative.physical_cartesian_chain, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative.physical_cartesian_chain) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative.Relation_physical_cartesian_chain.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative.Relation_physical_cartesian_chain.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_physical_cartesian_chain

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
