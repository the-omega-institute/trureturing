import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.ActualEndpointReturnClasses
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.ActualCornerTransport
open _root_.D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open _root_.D5.S3.Geometry.Gluing.ActualLinkCornerChains
open _root_.D5.S3.Geometry.Gluing.ActualCornerPointPeriods
open _root_.D5.S3.Geometry.Gluing.ActualEndpointReturnClasses

namespace Reg.D5.S3.Geometry.Gluing.ActualEndpointReturnClasses
noncomputable section
universe a b

structure ActionData where
  G : Type a
  Ω : Type b
  groupG : Group G
  action : letI := groupG; MulAction Gᵐᵒᵖ Ω
  finiteΩ : Finite Ω
  u : G
  v : G
  ν : letI := groupG; letI := action; Vertex (pairing (Ω := Ω) u v)

attribute [instance] ActionData.groupG ActionData.action ActionData.finiteΩ

abbrev signature : Signature where
  Params := ActionData.{a,b}
  State p := Flag p.u p.v p.ν × Flag p.u p.v p.ν
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{a,b} :=
  realize signature (fun _ p d => Related p.u p.v (endpoint p.u p.v d.1) (endpoint p.u p.v d.2))
    (fun e => nomatch e)

def rejected : Realization signature.{a,b} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{a,b}
  Law R := ∀ p : ActionData.{a,b},
    (∀ d e : Flag p.u p.v p.ν, R.readout () p (d,e) ↔
      DartRelated p.u p.v d.val e.val) ∧
    (∀ d e : Flag p.u p.v p.ν, DartRelated p.u p.v d.val e.val ↔
      Relation.EqvGen (fun a b : Flag p.u p.v p.ν => DartStep p.u p.v a.val b.val) d e) ∧
    (∀ x y : Point p.u p.v p.ν, Related p.u p.v x y →
      (x ∈ Endpoints p.u p.v p.ν ↔ y ∈ Endpoints p.u p.v p.ν)) ∧
    (∀ x y : ↥(Endpoints p.u p.v p.ν), Related p.u p.v x.val y.val ↔
      Relation.EqvGen (fun a b : ↥(Endpoints p.u p.v p.ν) => Step p.u p.v a.val b.val) x y) ∧
    (∀ a : ReturnClasses p.u p.v p.ν,
      (endpointClassesEquiv p.u p.v p.ν a).val =
        endpointClassMap p.u p.v p.ν (returnClassesEquiv p.u p.v p.ν a)) ∧
    (∀ (c : Fin 4) (x : Root p.u p.v p.ν c),
      0 < pointPeriod p.u p.v c x.val ∧
      Function.minimalPeriod (tour p.u p.v c) (x.val,0) = 3 * pointPeriod p.u p.v c x.val) ∧
    (∀ (c : Fin 4) (x : ZeroFiber p.u p.v p.ν),
      (zeroReturn p.u p.v p.ν c x).val = act x.val (normalizedWord p.u p.v c)) ∧
    (∀ (c : Fin 4) (x y : Root p.u p.v p.ν c),
      (rootReturn p.u p.v p.ν c).SameCycle x y ↔
        (zeroReturn p.u p.v p.ν c).SameCycle (rootToZero p.u p.v p.ν c x) (rootToZero p.u p.v p.ν c y)) ∧
    (∀ (i : Fin 4) (x : ZeroFiber p.u p.v p.ν),
      (boundaryReturn p.u p.v p.ν i x).val = act x.val (boundaryWord p.u p.v i)) ∧
    (∀ a : BoundaryClasses p.u p.v p.ν,
      (boundaryEndpointEquiv p.u p.v p.ν a).val =
        endpointClassMap p.u p.v p.ν (returnClassesEquiv p.u p.v p.ν (boundaryClassesEquiv p.u p.v p.ν a)))

theorem bridge :
    (type_of% (@actual_endpoint_return_classes.{a,b})) ↔ arena.{a,b}.Law actual := by
  constructor
  · intro h p
    exact h p.u p.v p.ν
  · intro h G Ω gg action u v finiteΩ ν
    exact h ⟨G,Ω,gg,action,finiteΩ,u,v,ν⟩

def testData : ActionData.{a,b} := by
  let G := Equiv.Perm (ULift.{a} (Fin 1))
  let Ω := ULift.{b} Unit
  letI : MulAction Gᵐᵒᵖ Ω := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl }
  exact ⟨G,Ω,inferInstance,inferInstance,inferInstance,1,1,label (pairing 1 1) (⟨()⟩,0)⟩

def root (c : Fin 4) (h : corner c 0 = 0) : Root testData.u testData.v testData.ν c :=
  ⟨⟨()⟩,by simp only [h]; rfl⟩

def sample : signature.{a,b}.State testData :=
  let d := rootFlag testData.u testData.v 0 (root 0 rfl)
  (d,d)

def other : signature.{a,b}.State testData :=
  (rootFlag testData.u testData.v 0 (root 0 rfl),
   rootFlag testData.u testData.v 3 (root 3 rfl))

theorem rejected_law : ¬ arena.{a,b}.Law rejected := by
  intro h
  exact ((h testData).1 sample.1 sample.2).mpr (Relation.EqvGen.refl _)

theorem other_not_related : ¬ Related testData.u testData.v
    (endpoint testData.u testData.v other.1) (endpoint testData.u testData.v other.2) := by
  intro h
  have hd := (actual_endpoint_return_classes testData.u testData.v testData.ν).1
    other.1 other.2 |>.mp h
  let q0 : ReturnClasses testData.u testData.v testData.ν :=
    ⟨0,Quotient.mk _ (root 0 rfl)⟩
  let q3 : ReturnClasses testData.u testData.v testData.ν :=
    ⟨3,Quotient.mk _ (root 3 rfl)⟩
  have heq : returnClassesEquiv testData.u testData.v testData.ν q0 =
      returnClassesEquiv testData.u testData.v testData.ν q3 := Quotient.sound hd
  have hq := (returnClassesEquiv testData.u testData.v testData.ν).injective heq
  have hc : (0 : Fin 4) = 3 := congrArg Sigma.fst hq
  contradiction

theorem dependence : ObservationalDependence signature.{a,b} actual := by
  intro _
  refine ⟨testData,sample,other,?_⟩
  intro h
  apply other_not_related
  exact Eq.mp h (Relation.EqvGen.refl _)

def registration : Registration arena.{a,b}
    (type_of% (@actual_endpoint_return_classes.{a,b})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @actual_endpoint_return_classes,rejected,rejected_law⟩
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
    (@actual_endpoint_return_classes.{a,b})
    (type_of% (realize signature.{a,b}
      (fun _ p d => Related p.u p.v (endpoint p.u p.v d.1) (endpoint p.u p.v d.2))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.ActualEndpointReturnClasses.actual_endpoint_return_classes.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.ActualEndpointReturnClasses.registration,
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
    (fun _ p d => Related p.u p.v (endpoint p.u p.v d.1) (endpoint p.u p.v d.2))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.ActualEndpointReturnClasses,
    definition := none,
    coordinates := #[0,1,4,5,7],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "fn","arg","body","body","fn","arg"],
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
end Reg.D5.S3.Geometry.Gluing.ActualEndpointReturnClasses
