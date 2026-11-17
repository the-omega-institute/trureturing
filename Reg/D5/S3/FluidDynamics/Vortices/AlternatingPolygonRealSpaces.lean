import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
noncomputable section
open scoped BigOperators
open Matrix Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters (Configuration)
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonMultiplicity
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
namespace Relation_complexify_operator
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Cartesian p) (fun p => Cartesian p → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (v : _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.RealCartesian m),
    T.readout () m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.complexify m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.realOperator m v)) (actualOperator m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.complexify m v))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Cartesian 1), (1 : Cartesian 1), ?_⟩
  intro he
  have hf : (1 : Cartesian 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.complexify_operator) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.complexify_operator, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.complexify_operator) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.Relation_complexify_operator.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.Relation_complexify_operator.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_complexify_operator

namespace Relation_real_nonzero_semisimple
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Submodule ℝ (RealCartesian p)) (fun p => Submodule ℝ (RealCartesian p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m)
    {μ : ℝ} (_hμ : μ ≠ 0),
    T.readout () m ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.realOperator m).maxGenEigenspace μ) ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.realOperator m).eigenspace μ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (μ := 1) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (⊥ : Submodule ℝ (RealCartesian 1)), (⊤ : Submodule ℝ (RealCartesian 1)), ?_⟩
  intro he
  have hf : (⊤ : Submodule ℝ (RealCartesian 1)) = ⊥ := Eq.mp (congrFun he ⊥) rfl
  exact top_ne_bot hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.real_nonzero_semisimple) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.real_nonzero_semisimple, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.real_nonzero_semisimple) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.Relation_real_nonzero_semisimple.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.Relation_real_nonzero_semisimple.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
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
end Relation_real_nonzero_semisimple

namespace Relation_real_geometric_multiplicity
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 3 ≤ m)
    {r : ℕ} (_hr : 2 ≤ r) (_hrm : r < m) (μ : ℝ)
    (_hμ : μ = positiveRoot m r ∨ μ = -positiveRoot m r),
    T.readout () () (Module.finrank ℝ ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.realOperator m).eigenspace μ)) (2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 (by omega) (r := 2) (by omega) (by omega) (positiveRoot 3 2) (Or.inl rfl)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.real_geometric_multiplicity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.real_geometric_multiplicity, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.real_geometric_multiplicity) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.Relation_real_geometric_multiplicity.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.Relation_real_geometric_multiplicity.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_real_geometric_multiplicity

namespace Relation_unstable_finrank
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 3 ≤ m),
    T.readout () () (Module.finrank ℝ (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.unstableSpace m)) (2 * (m - 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.unstable_finrank) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.unstable_finrank, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.unstable_finrank) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.Relation_unstable_finrank.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.Relation_unstable_finrank.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_unstable_finrank

namespace Relation_stable_finrank
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 3 ≤ m),
    T.readout () () (Module.finrank ℝ (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.stableSpace m)) (2 * (m - 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.stable_finrank) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.stable_finrank, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.stable_finrank) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.Relation_stable_finrank.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces.Relation_stable_finrank.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_stable_finrank

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
