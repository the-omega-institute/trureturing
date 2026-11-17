import Reg.Support.UniverseSingleReadout
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonPhysicalDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSmallCases
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonOrientation
import LeanInformationAuditInterface.Contract.Registration

/- Additional original-source relation audits. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain
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
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
namespace Relation_cartesian_chain
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 1 ≤ m),
    T.readout () () (realOperator m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian0 m) = 0) (realOperator m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian1 m) = _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian0 m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ∧ True := Eq.mp (congrFun he True) ⟨trivial, trivial⟩
  exact hf.1
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian_chain) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian_chain, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian_chain) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.Relation_cartesian_chain.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.Relation_cartesian_chain.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_cartesian_chain

namespace Relation_cartesian0_ne_zero
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop)
def actual : Realization signature := realize signature (fun _ _ P => ¬ P) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 1 ≤ m),
    T.readout () () ((_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian0 m) = (0))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), False, True, ?_⟩
  intro he
  have hf : ¬ True := Eq.mp he (fun h => h)
  exact hf trivial
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian0_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian0_ne_zero, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian0_ne_zero) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.Relation_cartesian0_ne_zero.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.Relation_cartesian0_ne_zero.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain
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
end Relation_cartesian0_ne_zero

namespace Relation_unbounded_linear_drift
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Unit
  (fun p => Prop) (fun p => Prop → Prop)
def actual : Realization signature := realize signature (fun _ _ P Q => (P ∧ Q)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ (m : ℕ) (_hm : 1 ≤ m),
    T.readout () () ((∀ t : ℝ, HasDerivAt (fun τ : ℝ => _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian1 m + τ • _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian0 m)
      (realOperator m (_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian1 m + t • _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian0 m)) t)) (¬ Bornology.IsBounded (Set.range (fun t : ℝ => _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian1 m + t • _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.cartesian0 m)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have hf : False ∧ True := Eq.mp (congrFun he True) ⟨trivial, trivial⟩
  exact hf.1
def source : Registration arena (type_of% @_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.unbounded_linear_drift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.unbounded_linear_drift, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.unbounded_linear_drift) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.Relation_unbounded_linear_drift.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain.Relation_unbounded_linear_drift.source
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
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Relation_unbounded_linear_drift

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonCartesianChain
