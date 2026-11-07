import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
import Reg.Support.SingleDependentReadout

/-! Author registration of the exact complex square-root family. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonMultiplicity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ m r => spectralRoot m r ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ m r => spectralRoot m r ^ 2 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) {r : ℕ}, r ≤ m → R.readout () m r = (squaredValue m r : ℂ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (r := 0) (by omega)
  change spectralRoot 1 0 ^ 2 + 1 = (squaredValue 1 0 : ℂ) at hb
  rw [spectralRoot_sq 1 (by omega : 0 ≤ 1)] at hb
  have h01 : (1 : ℂ) = 0 := by linear_combination hb
  exact one_ne_zero h01

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change spectralRoot 1 0 ^ 2 ≠ spectralRoot 1 1 ^ 2
  rw [spectralRoot_sq 1 (by omega : 0 ≤ 1), spectralRoot_sq 1 (le_refl 1)]
  norm_num [squaredValue]

def source : Registration arena (type_of% @spectralRoot_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectralRoot_sq, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@spectralRoot_sq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m r => spectralRoot m r ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
noncomputable section
open scoped BigOperators
open Matrix Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonParameters (Configuration)
open _root_.D5.S3.FluidDynamics.Vortices.InverseChordCirculant _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonModes
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonMultiplicity _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonJordan _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition
namespace Relation_all_complex_roots
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ↔ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m) (μ : ℂ),
    T.readout () () ((((jacobian (2 * m)).map Complex.ofRealHom).charpoly).IsRoot μ) (∃ r : ℕ, r ≤ m ∧ (μ = _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot m r ∨ μ = -_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot m r))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact hf.mpr trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.all_complex_roots) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.all_complex_roots, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.all_complex_roots) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.Relation_all_complex_roots.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.Relation_all_complex_roots.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
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
end Relation_all_complex_roots

namespace Relation_spectralRoot_ne_zero
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop)
def actual : Realization signature := realize signature (fun _ _ P => ¬ P) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 1 ≤ m) {r : ℕ} (_hr : r < m),
    T.readout () () ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot m r) = (0))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (r := 0) (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), False, True, ?_⟩
  intro he
  have hf : ¬ True := Eq.mp he (fun h => h)
  exact hf trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot_ne_zero, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot_ne_zero) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.Relation_spectralRoot_ne_zero.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.Relation_spectralRoot_ne_zero.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_spectralRoot_ne_zero

namespace Relation_no_cross_label_collision
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => ℕ) (fun p => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 1 ≤ m) {r s : ℕ}
    (_hr : r ≤ m) (_hs : s ≤ m) (μ : ℂ)
    (_hμr : μ = _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot m r ∨ μ = -_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot m r)
    (_hμs : μ = _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot m s ∨ μ = -_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot m s),
    T.readout () () (r) (s)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (r := 0) (s := 0) (by omega) (by omega) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot 1 0) (Or.inl rfl) (Or.inl rfl)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hf
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.no_cross_label_collision) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.no_cross_label_collision, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.no_cross_label_collision) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.Relation_no_cross_label_collision.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.Relation_no_cross_label_collision.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
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
end Relation_no_cross_label_collision

namespace Relation_signed_root_multiplicities
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) [NeZero (2 * m)] (_hm : 1 ≤ m)
    {r : ℕ} (_hr : r < m) (μ : ℂ)
    (_hμ : μ = _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot m r ∨ μ = -_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot m r),
    T.readout () () ((((jacobian (2 * m)).map Complex.ofRealHom).charpoly).rootMultiplicity μ =
        (if r = 0 then 1 else 2)) (Module.finrank ℂ ((actualOperator m).eigenspace μ) = (if r = 0 then 1 else 2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega) (r := 0) (by omega) (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.spectralRoot 1 0) (Or.inl rfl)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ∧ True := Eq.mp (congrFun he True) ⟨trivial, trivial⟩
  exact hf.1
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.signed_root_multiplicities) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.signed_root_multiplicities, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.signed_root_multiplicities) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.Relation_signed_root_multiplicities.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.Relation_signed_root_multiplicities.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
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
end Relation_signed_root_multiplicities

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
