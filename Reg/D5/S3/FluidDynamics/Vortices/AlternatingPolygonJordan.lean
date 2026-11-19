import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
import Reg.Support.SingleDependentReadout

/-! The observed object is the actual maximal generalized eigenspace, not a presumed spectrum. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature ℕ
  (fun _ => ℂ) (fun m => Submodule ℂ (Cartesian m))

def actual : Realization signature :=
  realize signature (fun _ m μ => (actualOperator m).maxGenEigenspace μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) {μ : ℂ} (_hμ : μ ≠ 0),
    R.readout () m μ = (actualOperator m).eigenspace μ

private theorem root_rank :
    Module.finrank ℂ ((actualOperator 1).eigenspace (spectralRoot 1 0)) = 1 := by
  simpa using (signed_root_multiplicities 1 (by omega) (by omega : 0 < 1)
    (spectralRoot 1 0) (Or.inl rfl)).2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 (by omega) (spectralRoot_ne_zero 1 (by omega) (by omega : 0 < 1))
  change (⊥ : Submodule ℂ (Cartesian 1)) = (actualOperator 1).eigenspace (spectralRoot 1 0) at he
  have hf := root_rank
  rw [← he] at hf
  simp at hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, spectralRoot 1 0, ?_⟩
  intro he
  change (actualOperator 1).maxGenEigenspace 0 =
    (actualOperator 1).maxGenEigenspace (spectralRoot 1 0) at he
  rw [actual_nonzero_semisimple 1 (by omega)
    (spectralRoot_ne_zero 1 (by omega) (by omega : 0 < 1))] at he
  have hf := congrArg (fun S : Submodule ℂ (Cartesian 1) => Module.finrank ℂ S) he
  rw [neutral_generalized_finrank 1 (by omega), root_rank] at hf
  norm_num at hf

def source : Registration arena (type_of% @actual_nonzero_semisimple) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_nonzero_semisimple, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_nonzero_semisimple) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m μ => (actualOperator m).maxGenEigenspace μ)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
noncomputable section
open scoped BigOperators
open Matrix Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters (Configuration)
open Matrix
open _root_.D5.S3.FluidDynamics.Vortices.InverseChordCirculant _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonFourier
namespace Relation_actual_normal_form
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Modes p) (fun p => Modes p → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m) (v : _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.Cartesian m),
    T.readout () m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.cartesianCoordinates m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.actualOperator m v)) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.modeOperator m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.cartesianCoordinates m v))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Modes 1), (1 : Modes 1), ?_⟩
  intro he
  have hf : (1 : Modes 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.actual_normal_form) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.actual_normal_form, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.actual_normal_form) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.Relation_actual_normal_form.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan.Relation_actual_normal_form.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_actual_normal_form

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
