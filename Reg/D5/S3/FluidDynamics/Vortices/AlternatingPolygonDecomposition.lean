import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
noncomputable section
open scoped BigOperators
open Matrix Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters (Configuration)
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonMultiplicity
namespace Relation_coordinates_block
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Modes p) (fun p => Modes p → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)]
    (q : ZMod (2 * m)) (w : ℂ × ℂ),
    T.readout () m (cartesianCoordinates m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.block m q w)) (Pi.single q w)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Modes 1), (1 : Modes 1), ?_⟩
  intro he
  have hf : (1 : Modes 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.coordinates_block) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.coordinates_block, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.coordinates_block) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_coordinates_block.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_coordinates_block.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
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
end Relation_coordinates_block

namespace Relation_block_restriction
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Cartesian p) (fun p => Cartesian p → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m)
    (q : ZMod (2 * m)) (w : ℂ × ℂ),
    T.readout () m (actualOperator m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.block m q w)) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.block m q
      ((ell m q : ℂ) * w.2, ((ell m (q + m) + 1 : ℝ) : ℂ) * w.1))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Cartesian 1), (1 : Cartesian 1), ?_⟩
  intro he
  have hf : (1 : Cartesian 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.block_restriction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.block_restriction, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.block_restriction) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_block_restriction.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_block_restriction.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
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
end Relation_block_restriction

namespace Relation_reconstruct
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Cartesian p) (fun p => Cartesian p → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (v : Cartesian m),
    T.readout () m (v) (∑ q : ZMod (2 * m), _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.block m q (cartesianCoordinates m v q))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Cartesian 1), (1 : Cartesian 1), ?_⟩
  intro he
  have hf : (1 : Cartesian 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.reconstruct) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.reconstruct, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.reconstruct) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_reconstruct.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_reconstruct.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
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
end Relation_reconstruct

namespace Relation_unique_coefficients
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (w : Modes m),
    T.readout () () ((∑ q : ZMod (2 * m), _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.block m q (w q)) = 0) (w = 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.unique_coefficients) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.unique_coefficients, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.unique_coefficients) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_unique_coefficients.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_unique_coefficients.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
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
end Relation_unique_coefficients

namespace Relation_invariantSpace_finrank
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)),
    T.readout () () (Module.finrank ℂ (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.invariantSpace m q)) (2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.invariantSpace_finrank) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.invariantSpace_finrank, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.invariantSpace_finrank) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_invariantSpace_finrank.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_invariantSpace_finrank.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
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
end Relation_invariantSpace_finrank

namespace Relation_geometric_eq_algebraic
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m)
    {μ : ℂ} (_hμ : μ ≠ 0),
    T.readout () () (Module.finrank ℂ ((actualOperator m).eigenspace μ)) ((((jacobian (2 * m)).map Complex.ofRealHom).charpoly).rootMultiplicity μ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (μ := 1) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.geometric_eq_algebraic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.geometric_eq_algebraic, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.geometric_eq_algebraic) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_geometric_eq_algebraic.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_geometric_eq_algebraic.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
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
end Relation_geometric_eq_algebraic

namespace Relation_geometric_multiplicity_of_mode
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m)
    {r : ℕ} (_hr : r ≤ m) (μ : ℂ) (_hμ : μ ≠ 0)
    (_hroot : μ ^ 2 = (squaredValue m r : ℂ)),
    T.readout () () (Module.finrank ℂ ((actualOperator m).eigenspace μ)) (if r = 0 ∨ r = m then 1 else 2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (r := 0) (by omega) (spectralRoot 1 0) (spectralRoot_ne_zero 1 (by omega) (by omega : 0 < 1)) (spectralRoot_sq 1 (by omega : 0 ≤ 1))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.geometric_multiplicity_of_mode) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.geometric_multiplicity_of_mode, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.geometric_multiplicity_of_mode) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_geometric_multiplicity_of_mode.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition.Relation_geometric_multiplicity_of_mode.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
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
end Relation_geometric_multiplicity_of_mode

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
