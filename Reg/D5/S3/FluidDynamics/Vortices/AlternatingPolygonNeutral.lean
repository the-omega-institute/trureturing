import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
noncomputable section
open scoped BigOperators
open Matrix Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters (Configuration)
open _root_.D5.S3.FluidDynamics.Vortices.InverseChordCirculant _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
namespace Relation_paired_neutral_iff
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {Q : Type*} (α β : Q → ℂ) (v : Q → ℂ × ℂ),
    T.readout () () (v ∈ (pairedOperator α β).maxGenEigenspace 0) (∀ q, α q * β q ≠ 0 → v q = 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (Q := PUnit) 0 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.paired_neutral_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.paired_neutral_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.paired_neutral_iff) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_paired_neutral_iff.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_paired_neutral_iff.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_paired_neutral_iff

namespace Relation_gamma_zero_iff_label
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)),
    T.readout () () (gamma m q = 0) (q = m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.gamma_zero_iff_label) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.gamma_zero_iff_label, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.gamma_zero_iff_label) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_gamma_zero_iff_label.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_gamma_zero_iff_label.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
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
end Relation_gamma_zero_iff_label

namespace Relation_actual_pow_coordinates
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Modes p) (fun p => Modes p → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m)
    (n : ℕ) (v : Cartesian m),
    T.readout () m (cartesianCoordinates m (((actualOperator m) ^ n) v)) (((modeOperator m) ^ n) (cartesianCoordinates m v))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Modes 1), (1 : Modes 1), ?_⟩
  intro he
  have hf : (1 : Modes 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.actual_pow_coordinates) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.actual_pow_coordinates, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.actual_pow_coordinates) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_actual_pow_coordinates.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_actual_pow_coordinates.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
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
end Relation_actual_pow_coordinates

namespace Relation_actual_neutral_iff
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m) (v : Cartesian m),
    T.readout () () (v ∈ (actualOperator m).maxGenEigenspace 0) (∀ q : ZMod (2 * m), q ≠ m → cartesianCoordinates m v q = 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.actual_neutral_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.actual_neutral_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.actual_neutral_iff) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_actual_neutral_iff.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_actual_neutral_iff.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_actual_neutral_iff

namespace Relation_neutral_chain
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m),
    T.readout () () (actualOperator m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral0 m) = 0) (actualOperator m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral1 m) = _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral0 m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ∧ True := Eq.mp (congrFun he True) ⟨trivial, trivial⟩
  exact hf.1
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_chain) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_chain, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_chain) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_chain.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_chain.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
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
end Relation_neutral_chain

namespace Relation_neutral_space
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Submodule ℂ (Cartesian p)) (fun p => Submodule ℂ (Cartesian p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m),
    T.readout () m ((actualOperator m).maxGenEigenspace 0) (invariantSpace m m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (⊥ : Submodule ℂ (Cartesian 1)), (⊤ : Submodule ℂ (Cartesian 1)), ?_⟩
  intro he
  have hf : (⊤ : Submodule ℂ (Cartesian 1)) = ⊥ := Eq.mp (congrFun he ⊥) rfl
  exact top_ne_bot hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_space) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_space, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_space) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_space.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_space.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_neutral_space

namespace Relation_neutral_generalized_finrank
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m),
    T.readout () () (Module.finrank ℂ ((actualOperator m).maxGenEigenspace 0)) (2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_generalized_finrank) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_generalized_finrank, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_generalized_finrank) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_generalized_finrank.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_generalized_finrank.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
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
end Relation_neutral_generalized_finrank

namespace Relation_neutral0_ne_zero
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop)
def actual : Realization signature := realize signature (fun _ _ P => ¬ P) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)],
    T.readout () () ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral0 m) = (0))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), False, True, ?_⟩
  intro he
  have hf : ¬ True := Eq.mp he (fun h => h)
  exact hf trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral0_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral0_ne_zero, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral0_ne_zero) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral0_ne_zero.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral0_ne_zero.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => ¬ P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_neutral0_ne_zero

namespace Relation_neutral_eigenspace
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Submodule ℂ (Cartesian p)) (fun p => Submodule ℂ (Cartesian p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m),
    T.readout () m ((actualOperator m).eigenspace 0) (Submodule.span ℂ {_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral0 m})
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (⊥ : Submodule ℂ (Cartesian 1)), (⊤ : Submodule ℂ (Cartesian 1)), ?_⟩
  intro he
  have hf : (⊤ : Submodule ℂ (Cartesian 1)) = ⊥ := Eq.mp (congrFun he ⊥) rfl
  exact top_ne_bot hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_eigenspace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_eigenspace, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_eigenspace) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_eigenspace.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_eigenspace.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_neutral_eigenspace

namespace Relation_neutral_geometric_finrank
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m),
    T.readout () () (Module.finrank ℂ ((actualOperator m).eigenspace 0)) (1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_geometric_finrank) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_geometric_finrank, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_geometric_finrank) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_geometric_finrank.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_geometric_finrank.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
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
end Relation_neutral_geometric_finrank

namespace Relation_neutral_chain_independent
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m)
    (a b : ℂ) (h : a • _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral0 m + b • _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral1 m = 0),
    T.readout () () (a = 0) (b = 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) 0 0 (by simp)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ∧ True := Eq.mp (congrFun he True) ⟨trivial, trivial⟩
  exact hf.1
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_chain_independent) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_chain_independent, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_chain_independent) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_chain_independent.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_chain_independent.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
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
end Relation_neutral_chain_independent

namespace Relation_neutral_drift
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Cartesian p) (fun p => Cartesian p → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m) (t : ℂ),
    T.readout () m (actualOperator m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral1 m + t • _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral0 m)) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral0 m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Cartesian 1), (1 : Cartesian 1), ?_⟩
  intro he
  have hf : (1 : Cartesian 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_drift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_drift, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.neutral_drift) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_drift.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral.Relation_neutral_drift.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
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
end Relation_neutral_drift

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
