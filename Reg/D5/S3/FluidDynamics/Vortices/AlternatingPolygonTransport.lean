import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
noncomputable section
open scoped BigOperators
open Matrix Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters (Configuration)
open Matrix Polynomial
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
namespace Relation_parameter_matrix_eq
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Matrix (Fin (2*p) ⊕ Fin (2*p)) (Fin (2*p) ⊕ Fin (2*p)) ℂ) (fun p => Matrix (Fin (2*p) ⊕ Fin (2*p)) (Fin (2*p) ⊕ Fin (2*p)) ℂ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () m ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.jacobian (2 * m) b Ω
      (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.radius b Ω • polygon (2 * m))).map Complex.ofRealHom) ((2 * Ω : ℂ) • (jacobian (2 * m)).map Complex.ofRealHom)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ), (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ), ?_⟩
  intro he
  have hf : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_matrix_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_matrix_eq, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_matrix_eq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.Relation_parameter_matrix_eq.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.Relation_parameter_matrix_eq.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_parameter_matrix_eq

namespace Relation_parameterOperator_eq
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Module.End ℂ (Cartesian p)) (fun p => Module.End ℂ (Cartesian p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameterOperator m b Ω) ((2 * Ω : ℂ) • actualOperator m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Module.End ℂ (Cartesian 1)), (1 : Module.End ℂ (Cartesian 1)), ?_⟩
  intro he
  have hf : (1 : Module.End ℂ (Cartesian 1)) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameterOperator_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameterOperator_eq, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameterOperator_eq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.Relation_parameterOperator_eq.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.Relation_parameterOperator_eq.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_parameterOperator_eq

namespace Relation_parameter_genEigenspace
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Submodule ℂ (Cartesian p)) (fun p => Submodule ℂ (Cartesian p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω)
    (μ : ℂ) (n : ℕ∞),
    T.readout () m ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameterOperator m b Ω).genEigenspace ((2 * Ω : ℂ) * μ) n) ((actualOperator m).genEigenspace μ n)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (b := 1) (Ω := 1) (by norm_num) (by norm_num) 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (⊥ : Submodule ℂ (Cartesian 1)), (⊤ : Submodule ℂ (Cartesian 1)), ?_⟩
  intro he
  have hf : (⊤ : Submodule ℂ (Cartesian 1)) = ⊥ := Eq.mp (congrFun he ⊥) rfl
  exact top_ne_bot hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_genEigenspace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_genEigenspace, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_genEigenspace) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.Relation_parameter_genEigenspace.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.Relation_parameter_genEigenspace.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
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
end Relation_parameter_genEigenspace

namespace Relation_parameter_charpoly
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℂ[X]) (fun p => ℂ[X] → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () () (((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.jacobian (2 * m) b Ω
      (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.radius b Ω • polygon (2 * m))).map Complex.ofRealHom).charpoly) (C ((2 * Ω : ℂ) ^ (4 * m)) *
        (((jacobian (2 * m)).map Complex.ofRealHom).charpoly).comp
          (C (2 * Ω : ℂ)⁻¹ * X))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ[X]), (1 : ℂ[X]), ?_⟩
  intro he
  have hf : (1 : ℂ[X]) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_charpoly) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_charpoly, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_charpoly) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.Relation_parameter_charpoly.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.Relation_parameter_charpoly.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_parameter_charpoly

namespace Relation_parameter_neutral_chain
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m)
    {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () () (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameterOperator m b Ω (neutral0 m) = 0) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameterOperator m b Ω ((2 * Ω : ℂ)⁻¹ • neutral1 m) = neutral0 m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ∧ True := Eq.mp (congrFun he True) ⟨trivial, trivial⟩
  exact hf.1
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_neutral_chain) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_neutral_chain, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.parameter_neutral_chain) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.Relation_parameter_neutral_chain.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport.Relation_parameter_neutral_chain.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_parameter_neutral_chain

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
