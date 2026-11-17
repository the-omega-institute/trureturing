import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
import Reg.Support.SingleDependentReadout

/-! Author-owned four-slot attempt for the actual collision-free field scaling law.
The readout is the actual Cartesian field, with its complete original telescope. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
namespace FieldScaling

abbrev Params := ℕ × ℝ × ℝ × ℝ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Params
  (fun p => Configuration p.1) (fun p => Configuration p.1)

def actual : Realization signature :=
  realize signature (fun _ p w => field p.1 p.2.1 p.2.2.1 (p.2.2.2 • w))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p w => field p.1 p.2.1 p.2.2.1 (p.2.2.2 • w) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law T := ∀ (N : ℕ) {b Ω R : ℝ} (_hR : R ≠ 0) (_hb : b = 4 * Ω * R ^ 2)
    (w : Configuration N) (_hw : CollisionFree w),
      T.readout () (N, b, Ω, R) w = (2 * Ω * R) •
        _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.field N w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : CollisionFree (0 : Configuration 1) := by
    intro j k hjk
    exact (hjk (Subsingleton.elim _ _)).elim
  have he := h 1 (b := 4) (Ω := 1) (R := 1) (by norm_num) (by norm_num) 0 hz
  have hx := congrArg (fun v : Configuration 1 => v (.inl 0)) he
  norm_num [rejected, realize, field,
    _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.field,
    Pi.add_apply, Pi.one_apply, Pi.zero_apply] at hx
  change field 1 4 1 0 (.inl 0) + 1 = 0 at hx
  norm_num [field] at hx

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(1, 4, 1, 1), 0, Pi.single (.inr 0) 1, ?_⟩
  intro he
  have hx := congrArg (fun v : Configuration 1 => v (.inl 0)) he
  norm_num [actual, realize, field, Fin.sum_univ_one, Pi.zero_apply,
    _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.charge] at hx
  change (0 : ℝ) = 1 at hx
  norm_num at hx

def source : Registration arena (type_of% @field_scaling) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@field_scaling, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@field_scaling) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.FieldScaling.unit
  realizationName :=
    `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.FieldScaling.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p w => field p.1 p.2.1 p.2.2.1 (p.2.2.2 • w)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end FieldScaling
end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
noncomputable section
open scoped BigOperators
open Matrix Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters (Configuration)
open Matrix
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
namespace Relation_collision_free_smul
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {N : ℕ} {z : _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Configuration N} {R : ℝ}
    (_hR : R ≠ 0),
    T.readout () () (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.CollisionFree (R • z)) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.CollisionFree z)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 0) (z := 0) (R := 1) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.collision_free_smul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.collision_free_smul, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.collision_free_smul) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_collision_free_smul.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_collision_free_smul.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
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
end Relation_collision_free_smul

namespace Relation_radius_sq
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℝ) (fun p => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {b Ω : ℝ} (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () () ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.radius b Ω) ^ 2) (b / (4 * Ω))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.radius_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.radius_sq, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.radius_sq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_radius_sq.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_radius_sq.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
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
end Relation_radius_sq

namespace Relation_normalized_field
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Configuration p → Configuration p) (fun p => (Configuration p → Configuration p) → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (N : ℕ),
    T.readout () N (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.field N 2 (1 / 2)) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.field N)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Configuration 1 → Configuration 1), (1 : Configuration 1 → Configuration 1), ?_⟩
  intro he
  have hf : (1 : Configuration 1 → Configuration 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.normalized_field) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.normalized_field, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.normalized_field) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_normalized_field.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_normalized_field.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_normalized_field

namespace Relation_jacobian_scaling
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) ℝ) (fun p => Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (N : ℕ) {b Ω R : ℝ} (_hR : R ≠ 0)
    (_hb : b = 4 * Ω * R ^ 2),
    T.readout () N (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.jacobian N b Ω (R • polygon N)) ((2 * Ω) • _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.jacobian N)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (b := 4) (Ω := 1) (R := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ), (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ), ?_⟩
  intro he
  have hf : (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.jacobian_scaling) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.jacobian_scaling, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.jacobian_scaling) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_jacobian_scaling.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_jacobian_scaling.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
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
end Relation_jacobian_scaling

namespace Relation_scaled_equilibrium
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 1 ≤ m) {b Ω : ℝ}
    (_hb : 0 < b) (_hΩ : 0 < Ω),
    T.readout () () (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.CollisionFree ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.radius b Ω) • polygon (2 * m))) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.field (2 * m) b Ω ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.radius b Ω) • polygon (2 * m)) = 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (b := 1) (Ω := 1) (by norm_num) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ∧ True := Eq.mp (congrFun he True) ⟨trivial, trivial⟩
  exact hf.1
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.scaled_equilibrium) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.scaled_equilibrium, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.scaled_equilibrium) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_scaled_equilibrium.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_scaled_equilibrium.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
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
end Relation_scaled_equilibrium

namespace Relation_collision_free_rotate
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {N : ℕ} {z : _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Configuration N} (θ : ℝ),
    T.readout () () (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.CollisionFree (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.rotate θ z)) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.CollisionFree z)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 0) (z := 0) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.collision_free_rotate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.collision_free_rotate, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.collision_free_rotate) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_collision_free_rotate.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_collision_free_rotate.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
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
end Relation_collision_free_rotate

namespace Relation_field_rotation
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature ℕ
  (fun p => Configuration p) (fun p => Configuration p → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {N : ℕ} (b Ω θ : ℝ) (z : _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Configuration N),
    T.readout () N (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.field N b Ω (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.rotate θ z)) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.rotate θ (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.field N b Ω z))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 0) 0 0 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Configuration 1), (1 : Configuration 1), ?_⟩
  intro he
  have hf : (1 : Configuration 1) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.field_rotation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.field_rotation, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.field_rotation) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_field_rotation.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_field_rotation.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
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
end Relation_field_rotation

namespace Relation_total_charge
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℝ) (fun p => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (N : ℕ),
    T.readout () () ((∑ j : Fin N, charge N j)) (if Even N then 0 else 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.total_charge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.total_charge, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.total_charge) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_total_charge.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_total_charge.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_total_charge

namespace Relation_regular_equilibrium_iff
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {N : ℕ} (_hN : 3 ≤ N) {b Ω ρ : ℝ}
    (_hb : 0 < b) (_hΩ : 0 < Ω) (_hρ : 0 < ρ) (θ : ℝ),
    T.readout () () (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.field N b Ω (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.regular N ρ θ) = 0) (Even N ∧ ρ ^ 2 = b / (4 * Ω))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 3) (by omega) (b := 1) (Ω := 1) (ρ := 1) (by norm_num) (by norm_num) (by norm_num) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.regular_equilibrium_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.regular_equilibrium_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.regular_equilibrium_iff) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_regular_equilibrium_iff.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_regular_equilibrium_iff.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_regular_equilibrium_iff

namespace Relation_regular_equilibrium_iff_radius
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {N : ℕ} (_hN : 3 ≤ N) {b Ω ρ : ℝ}
    (_hb : 0 < b) (_hΩ : 0 < Ω) (_hρ : 0 < ρ) (θ : ℝ),
    T.readout () () (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.field N b Ω (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.regular N ρ θ) = 0) (Even N ∧ ρ = _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.radius b Ω)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 3) (by omega) (b := 1) (Ω := 1) (ρ := 1) (by norm_num) (by norm_num) (by norm_num) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.regular_equilibrium_iff_radius) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.regular_equilibrium_iff_radius, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.regular_equilibrium_iff_radius) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_regular_equilibrium_iff_radius.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters.Relation_regular_equilibrium_iff_radius.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_regular_equilibrium_iff_radius

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters
