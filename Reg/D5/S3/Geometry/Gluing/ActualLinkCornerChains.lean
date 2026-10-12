import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.ActualLinkCornerChains
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.ActualCornerTransport
open _root_.D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open _root_.D5.S3.Geometry.Gluing.ActualLinkCornerChains

namespace Reg.D5.S3.Geometry.Gluing.ActualLinkCornerChains
noncomputable section
universe a b

/-- The complete source family, including arbitrary groups, actions and actual corner classes. -/
structure ActionData where
  G : Type a
  Ω : Type b
  groupG : Group G
  action : letI := groupG; MulAction Gᵐᵒᵖ Ω
  u : G
  v : G
  ν : letI := groupG; letI := action; Vertex (pairing (Ω := Ω) u v)

attribute [instance] ActionData.groupG ActionData.action

abbrev signature : Signature where
  Params := (p : ActionData.{a,b}) × Point p.u p.v p.ν
  State p := Point p.1.u p.1.v p.1.ν
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{a,b} :=
  realize signature (fun _ p y => Related p.1.u p.1.v p.2 y) (fun e => nomatch e)

def rejected : Realization signature.{a,b} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{a,b}
  Law R := ∀ q : signature.{a,b}.Params,
    let p := q.1
    let x := q.2
    ∀ y : Point p.u p.v p.ν,
    (Interior x → (R.readout () q y ↔ y = x)) ∧
    (∀ (f : Fin 4) (hx : EdgePoint x f),
      pairedPoint p.u p.v x f hx.1 ≠ x ∧
        (R.readout () q y ↔ y = x ∨ y = pairedPoint p.u p.v x f hx.1)) ∧
    (∀ d : Dart p.Ω, R.readout () q y →
      (x ∈ Neighborhood p.u p.v d ↔ y ∈ Neighborhood p.u p.v d)) ∧
    (∀ (d : Dart p.Ω) (hx : x ∈ Neighborhood p.u p.v d)
        (hy : y ∈ Neighborhood p.u p.v d),
      R.readout () q y ↔
        Relation.EqvGen (fun z w : ↥(Neighborhood p.u p.v (ν := p.ν) d) =>
          Step p.u p.v z.val w.val) ⟨x,hx⟩ ⟨y,hy⟩)

theorem bridge :
    (type_of% (@actual_guarded_point_analysis.{a,b})) ↔ arena.{a,b}.Law actual := by
  constructor
  · intro h q
    dsimp only
    exact fun y => @h q.1.G q.1.Ω q.1.groupG q.1.action q.1.u q.1.v q.1.ν q.2 y
  · intro h G Ω gg action u v ν x y
    exact h ⟨⟨G,Ω,gg,action,u,v,ν⟩,x⟩ y

def testData : ActionData.{a,b} := by
  let G := Equiv.Perm (ULift.{a} (Fin 1))
  let Ω := ULift.{b} Unit
  letI : MulAction Gᵐᵒᵖ Ω := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl }
  exact ⟨G,Ω,inferInstance,inferInstance,1,1,label (pairing 1 1) (⟨()⟩,0)⟩

def sample : Point testData.{a,b}.u testData.v testData.ν :=
  ⟨((⟨()⟩,0), ![0,1/3,1/3,1/3]), by
    refine ⟨rfl,?_,?_,rfl⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_succ]⟩

def other : Point testData.{a,b}.u testData.v testData.ν :=
  ⟨((⟨()⟩,0), ![0,1/2,1/4,1/4]), by
    refine ⟨rfl,?_,?_,rfl⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_succ]⟩

private theorem sample_interior : Interior sample.{a,b} := by
  intro f hf
  fin_cases f
  all_goals norm_num [sample] at *

private theorem other_ne_sample : other.{a,b} ≠ sample.{a,b} := by
  intro h
  have hh := congrArg (fun x => x.val.2 1) h
  norm_num [other,sample] at hh

theorem rejected_law : ¬ arena.{a,b}.Law rejected := by
  intro h
  exact ((h ⟨testData,sample⟩ sample).1 sample_interior).mpr rfl

theorem dependence : ObservationalDependence signature.{a,b} actual := by
  intro _
  refine ⟨⟨testData,sample⟩,sample,other,?_⟩
  change Related testData.u testData.v sample sample ≠
    Related testData.u testData.v sample other
  intro he
  have h : Related testData.u testData.v sample other :=
    Eq.mp he (Relation.EqvGen.refl _)
  exact other_ne_sample
    (((actual_guarded_point_analysis testData.u testData.v sample other).1
      sample_interior).mp h)

def registration : Registration arena.{a,b}
    (type_of% (@actual_guarded_point_analysis.{a,b})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @actual_guarded_point_analysis,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := dependence

def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_guarded_point_analysis.{a,b})
    (type_of% (realize signature.{a,b}
      (fun _ p y => Related p.1.u p.1.v p.2 y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.ActualLinkCornerChains.actual_guarded_point_analysis.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.ActualLinkCornerChains.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{a,b}⟩,
  objectArena := .source ⟨arena.{a,b}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{a,b} ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{a,b}
    (fun _ p y => Related p.1.u p.1.v p.2 y) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.ActualLinkCornerChains,
    definition := none,
    coordinates := #[0,1,4,5,6,7],
    readouts := #[
      { path := #["body","body","body","body","body","body","body","body","body",
          "fn","arg","body","fn","arg"],
        stateBinder := 8, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body","body","body","body","body","body","body","body","body",
          "arg","fn","arg","body","body","arg","fn","arg"],
        stateBinder := 8, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body","body","body","body","body","body","body","body","body",
          "arg","arg","fn","arg","body","domain"],
        stateBinder := 8, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body","body","body","body","body","body","body","body","body",
          "arg","arg","arg","body","body","body","fn","arg"],
        stateBinder := 8, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end
end Reg.D5.S3.Geometry.Gluing.ActualLinkCornerChains
