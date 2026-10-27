import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.ActualTruncatedPathComponents
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

/-! # Registration for the full retained quotient component classification -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Gluing.ActualLinkAffineFan
open _root_.D5.S3.Geometry.Gluing.ActualTruncatedPathComponents
open _root_.D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits (act)

namespace Reg.D5.S3.Geometry.Gluing.ActualTruncatedPathComponents
universe a b

structure ActionData where
  G : Type a
  Ω : Type b
  groupG : Group G
  action : letI := groupG; MulAction Gᵐᵒᵖ Ω
  topologyΩ : TopologicalSpace Ω
  discreteΩ : letI := topologyΩ; DiscreteTopology Ω
  u : G
  v : G
  point : TruncatedPoint Ω

attribute [instance] ActionData.groupG ActionData.action ActionData.topologyΩ ActionData.discreteΩ

abbrev signature : Signature where
  Params := ActionData.{a, b}
  State p := TruncatedPoint p.Ω
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Ω
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{a, b} :=
  realize signature (fun _ _ s => s.1)
    (fun e => nomatch e)

def rejected : Realization signature.{a, b} :=
  realize signature (fun _ p _ => p.point.1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{a, b}
  Law R := ∀ (p : ActionData.{a, b}) (s : TruncatedPoint p.Ω),
    Joined (Quotient.mk (Relation.EqvGen.setoid (TruncatedStep p.u p.v)) p.point)
      (Quotient.mk (Relation.EqvGen.setoid (TruncatedStep p.u p.v)) s) ↔
      ∃ g ∈ Subgroup.closure ({p.u,p.v} : Set p.G), act p.point.1 g = R.readout () p s

theorem bridge :
    (type_of% (@actual_truncated_joined_iff.{a, b})) ↔ arena.{a, b}.Law actual := by
  constructor
  · intro h p s
    exact h p.u p.v p.point s
  · intro h G Ω groupG action topologyΩ discreteΩ u v x y
    exact h ⟨G,Ω,groupG,action,topologyΩ,discreteΩ,u,v,x⟩ y

private def center : TruncatedTetrahedron :=
  ⟨fun _ => 1/4, by constructor <;> norm_num [Fin.sum_univ_succ]⟩

private def testData : ActionData.{a, b} := by
  let G := Equiv.Perm (ULift.{a} (Fin 1))
  let Ω := ULift.{b} Bool
  letI : MulAction Gᵐᵒᵖ Ω := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl }
  letI : TopologicalSpace Ω := ⊥
  letI : DiscreteTopology Ω := ⟨rfl⟩
  exact ⟨G,Ω,inferInstance,inferInstance,inferInstance,inferInstance,1,1,(⟨false⟩,center)⟩

private def low : TruncatedPoint testData.{a, b}.Ω := testData.point
private def high : TruncatedPoint testData.{a, b}.Ω := (⟨true⟩,center)

private theorem test_act (x : testData.{a, b}.Ω) (g : testData.{a, b}.G) : act x g = x := rfl

private theorem separated : ¬ Joined
    (Quotient.mk (Relation.EqvGen.setoid (TruncatedStep testData.{a, b}.u testData.v)) low)
    (Quotient.mk (Relation.EqvGen.setoid (TruncatedStep testData.u testData.v)) high) := by
  intro h
  obtain ⟨g,_,he⟩ := (actual_truncated_joined_iff testData.u testData.v low high).mp h
  rw [test_act] at he
  have hf : (false : Bool) = true := congrArg ULift.down he
  cases hf

theorem rejected_law : ¬ arena.{a, b}.Law rejected := by
  intro h
  apply separated
  exact (h testData high).mpr ⟨1,
    (Subgroup.closure ({testData.u,testData.v} : Set testData.G)).one_mem,rfl⟩

theorem dependence : ObservationalDependence signature.{a, b} actual := by
  intro i
  refine ⟨testData.{a, b},low.{a, b},high.{a, b},?_⟩
  intro he
  change low.{a, b}.1 = high.{a, b}.1 at he
  have hf : (false : Bool) = true := congrArg ULift.down he
  cases hf

def registration : Registration arena.{a, b}
    (type_of% (@actual_truncated_joined_iff.{a, b})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @actual_truncated_joined_iff,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_truncated_joined_iff.{a, b})
    (type_of% (realize signature.{a, b} (fun _ _ s => s.1)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.ActualTruncatedPathComponents.actual_truncated_joined_iff.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.ActualTruncatedPathComponents.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{a, b}⟩,
  objectArena := .source ⟨arena.{a, b}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{a, b} ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{a, b} (fun _ _ s => s.1)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.ActualTruncatedPathComponents,
    definition := none,
    coordinates := #[0,1,6,7,8],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "arg","arg","body","arg","arg"],
      stateBinder := 9,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1

end Reg.D5.S3.Geometry.Gluing.ActualTruncatedPathComponents
