import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
noncomputable section
open scoped BigOperators
open Matrix Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters (Configuration)
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
namespace Relation_derivative_rotation
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Configuration p) (fun p => Configuration p → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {N : ℕ} (b Ω θ : ℝ) {z : Configuration N}
    (_hz : CollisionFree z) (v : Configuration N),
    T.readout () N ((jacobian N b Ω (rotate θ z)).mulVec (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation.orientation N θ v)) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation.orientation N θ ((jacobian N b Ω z).mulVec v))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 0) 0 0 0 (z := 0) (by intro j; exact Fin.elim0 j) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Configuration 1), (1 : Configuration 1), ?_⟩
  intro he
  have hf : (1 : Configuration 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation.derivative_rotation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation.derivative_rotation, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation.derivative_rotation) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation.Relation_derivative_rotation.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation.Relation_derivative_rotation.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_derivative_rotation

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
