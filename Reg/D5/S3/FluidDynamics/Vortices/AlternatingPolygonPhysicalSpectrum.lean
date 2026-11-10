import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
noncomputable section
open scoped BigOperators
open Matrix Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters (Configuration)
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
namespace Relation_physical_algebraic_multiplicity
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω)
    (μ : ℂ),
    T.readout () () ((parameterOperator m b Ω).charpoly.rootMultiplicity ((2 * Ω : ℂ) * μ)) ((actualOperator m).charpoly.rootMultiplicity μ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (b := 1) (Ω := 1) (by norm_num) (by norm_num) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_algebraic_multiplicity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_algebraic_multiplicity, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_algebraic_multiplicity) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_algebraic_multiplicity.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_algebraic_multiplicity.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
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
end Relation_physical_algebraic_multiplicity

namespace Relation_physical_geometric_multiplicity
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω)
    (μ : ℂ),
    T.readout () () (Module.finrank ℂ ((parameterOperator m b Ω).eigenspace ((2 * Ω : ℂ) * μ))) (Module.finrank ℂ ((actualOperator m).eigenspace μ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (b := 1) (Ω := 1) (by norm_num) (by norm_num) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_geometric_multiplicity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_geometric_multiplicity, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_geometric_multiplicity) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_geometric_multiplicity.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_geometric_multiplicity.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
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
end Relation_physical_geometric_multiplicity

namespace Relation_physical_nonzero_semisimple
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Submodule ℂ (Cartesian p)) (fun p => Submodule ℂ (Cartesian p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m)
    {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω) {ν : ℂ} (_hν : ν ≠ 0),
    T.readout () m ((parameterOperator m b Ω).maxGenEigenspace ν) ((parameterOperator m b Ω).eigenspace ν)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (b := 1) (Ω := 1) (by norm_num) (by norm_num) (ν := 1) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (⊥ : Submodule ℂ (Cartesian 1)), (⊤ : Submodule ℂ (Cartesian 1)), ?_⟩
  intro he
  have hf : (⊤ : Submodule ℂ (Cartesian 1)) = ⊥ := Eq.mp (congrFun he ⊥) rfl
  exact top_ne_bot hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_nonzero_semisimple) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_nonzero_semisimple, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_nonzero_semisimple) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_nonzero_semisimple.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_nonzero_semisimple.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_physical_nonzero_semisimple

namespace Relation_physical_block_restriction
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Cartesian p) (fun p => Cartesian p → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m)
    {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω) (q : ZMod (2 * m)) (w : ℂ × ℂ),
    T.readout () m (parameterOperator m b Ω (block m q w)) (block m q
      ((2 * Ω : ℂ) * ((ell m q : ℂ) * w.2),
        (2 * Ω : ℂ) * (((ell m (q + m) + 1 : ℝ) : ℂ) * w.1)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (b := 1) (Ω := 1) (by norm_num) (by norm_num) 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Cartesian 1), (1 : Cartesian 1), ?_⟩
  intro he
  have hf : (1 : Cartesian 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_block_restriction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_block_restriction, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_block_restriction) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_block_restriction.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_block_restriction.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_physical_block_restriction

namespace Relation_physicalRealOperator_eq
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Module.End ℝ (RealCartesian p)) (fun p => Module.End ℝ (RealCartesian p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalRealOperator m b Ω) ((2 * Ω) • realOperator m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Module.End ℝ (RealCartesian 1)), (1 : Module.End ℝ (RealCartesian 1)), ?_⟩
  intro he
  have hf : (1 : Module.End ℝ (RealCartesian 1)) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalRealOperator_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalRealOperator_eq, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalRealOperator_eq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physicalRealOperator_eq.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physicalRealOperator_eq.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
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
end Relation_physicalRealOperator_eq

namespace Relation_physical_real_eigenspace
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Submodule ℝ (RealCartesian p)) (fun p => Submodule ℝ (RealCartesian p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω) (μ : ℝ),
    T.readout () m ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalRealOperator m b Ω).eigenspace (2 * Ω * μ)) ((realOperator m).eigenspace μ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (b := 1) (Ω := 1) (by norm_num) (by norm_num) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (⊥ : Submodule ℝ (RealCartesian 1)), (⊤ : Submodule ℝ (RealCartesian 1)), ?_⟩
  intro he
  have hf : (⊤ : Submodule ℝ (RealCartesian 1)) = ⊥ := Eq.mp (congrFun he ⊥) rfl
  exact top_ne_bot hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_real_eigenspace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_real_eigenspace, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_real_eigenspace) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_real_eigenspace.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_real_eigenspace.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_physical_real_eigenspace

namespace Relation_physical_positive_eigenvalue_iff
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 3 ≤ m)
    {b Ω μ : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω) (_hμ : 0 < μ),
    T.readout () () ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalRealOperator m b Ω).HasEigenvalue μ) (∃ k : Fin (m - 2), μ = 2 * Ω * positiveRoot m (k.val + 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 (by omega) (b := 1) (Ω := 1) (μ := 1) (by norm_num) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_positive_eigenvalue_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_positive_eigenvalue_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_positive_eigenvalue_iff) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_positive_eigenvalue_iff.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_positive_eigenvalue_iff.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
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
end Relation_physical_positive_eigenvalue_iff

namespace Relation_physical_negative_eigenvalue_iff
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 3 ≤ m)
    {b Ω μ : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω) (_hμ : μ < 0),
    T.readout () () ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalRealOperator m b Ω).HasEigenvalue μ) (∃ k : Fin (m - 2), μ = 2 * Ω * (-positiveRoot m (k.val + 2)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 (by omega) (b := 1) (Ω := 1) (μ := -1) (by norm_num) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_negative_eigenvalue_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_negative_eigenvalue_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_negative_eigenvalue_iff) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_negative_eigenvalue_iff.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_negative_eigenvalue_iff.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
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
end Relation_physical_negative_eigenvalue_iff

namespace Relation_physical_stable_exhaustive
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Submodule ℝ (RealCartesian p)) (fun p => Submodule ℝ (RealCartesian p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 3 ≤ m)
    {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalStableSpace m b Ω) (⨆ μ : ℝ, ⨆ _ : μ < 0, (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalRealOperator m b Ω).eigenspace μ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 (by omega) (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (⊥ : Submodule ℝ (RealCartesian 1)), (⊤ : Submodule ℝ (RealCartesian 1)), ?_⟩
  intro he
  have hf : (⊤ : Submodule ℝ (RealCartesian 1)) = ⊥ := Eq.mp (congrFun he ⊥) rfl
  exact top_ne_bot hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_stable_exhaustive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_stable_exhaustive, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_stable_exhaustive) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_stable_exhaustive.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_stable_exhaustive.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_physical_stable_exhaustive

namespace Relation_physical_unstable_exhaustive
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Submodule ℝ (RealCartesian p)) (fun p => Submodule ℝ (RealCartesian p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 3 ≤ m)
    {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalUnstableSpace m b Ω) (⨆ μ : ℝ, ⨆ _ : 0 < μ, (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalRealOperator m b Ω).eigenspace μ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 (by omega) (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (⊥ : Submodule ℝ (RealCartesian 1)), (⊤ : Submodule ℝ (RealCartesian 1)), ?_⟩
  intro he
  have hf : (⊤ : Submodule ℝ (RealCartesian 1)) = ⊥ := Eq.mp (congrFun he ⊥) rfl
  exact top_ne_bot hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_unstable_exhaustive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_unstable_exhaustive, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_unstable_exhaustive) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_unstable_exhaustive.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_unstable_exhaustive.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_physical_unstable_exhaustive

namespace Relation_physical_real_spaces
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () () (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalStableSpace m b Ω = stableSpace m) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalUnstableSpace m b Ω = unstableSpace m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ∧ True := Eq.mp (congrFun he True) ⟨trivial, trivial⟩
  exact hf.1
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_real_spaces) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_real_spaces, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_real_spaces) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_real_spaces.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_real_spaces.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
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
end Relation_physical_real_spaces

namespace Relation_physical_real_dimensions
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 3 ≤ m)
    {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () () (Module.finrank ℝ (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalStableSpace m b Ω) = 2 * (m - 2)) (Module.finrank ℝ (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physicalUnstableSpace m b Ω) = 2 * (m - 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 3 (by omega) (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ∧ True := Eq.mp (congrFun he True) ⟨trivial, trivial⟩
  exact hf.1
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_real_dimensions) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_real_dimensions, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.physical_real_dimensions) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_real_dimensions.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum.Relation_physical_real_dimensions.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
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
end Relation_physical_real_dimensions

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalSpectrum
