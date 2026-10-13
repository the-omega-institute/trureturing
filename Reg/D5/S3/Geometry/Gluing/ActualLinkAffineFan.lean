import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.ActualLinkAffineFan
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open _root_.D5.S3.Geometry.Gluing.ActualLinkCornerChains
open _root_.D5.S3.Geometry.Gluing.ActualCornerPointPeriods

open _root_.D5.S3.Geometry.Gluing.ActualLinkAffineFan

namespace Reg.D5.S3.Geometry.Gluing.ActualLinkAffineFan
noncomputable section
open scoped Fin.NatCast
universe a b

structure ActionData where
  G : Type a
  Ω : Type b
  groupG : Group G
  action : letI := groupG; MulAction Gᵐᵒᵖ Ω
  u : G
  v : G
  c : Fin 4
  x : Ω
  finiteΩ : Finite Ω

attribute [instance] ActionData.groupG ActionData.action ActionData.finiteΩ

abbrev Input (p : ActionData.{a, b}) := Fin (3 * pointPeriod p.u p.v p.c p.x) × Sector
abbrev Target (p : ActionData.{a, b}) :=
  ↥(Neighborhood p.u p.v (ν := vertex p.u p.v p.c p.x) (encode p.u p.v p.c (p.x,0)))

abbrev signature : Signature where
  Params := ActionData.{a, b}
  State := Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := Target
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{a, b} :=
  realize signature (fun _ p => Phi p.u p.v p.c p.x) (fun e => nomatch e)

def zeroInput (p : ActionData.{a, b}) : Input p :=
  (⟨0,by have h := (actual_component_enumeration p.u p.v p.c p.x).1; omega⟩,
    ⟨(0,0),by norm_num⟩)
def otherInput (p : ActionData.{a, b}) : Input p :=
  ((zeroInput p).1,⟨(1/2,0),by norm_num⟩)

def rejected : Realization signature.{a, b} :=
  realize signature (fun _ p _ => Phi p.u p.v p.c p.x (zeroInput p)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{a, b}
  Law R := ∀ p : ActionData.{a, b}, Function.Bijective (R.readout () p)

theorem bridge :
    (type_of% (@actual_strict_coordinates.{a, b})) ↔ arena.{a, b}.Law actual := by
  constructor
  · intro h p
    exact h p.u p.v p.c p.x
  · intro h G Ω gg action u v c x finiteΩ
    exact h ⟨G,Ω,gg,action,u,v,c,x,finiteΩ⟩

def testData : ActionData.{a, b} := by
  let G := Equiv.Perm (ULift.{a} (Fin 1))
  let Ω := ULift.{b} Unit
  letI : MulAction Gᵐᵒᵖ Ω := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl }
  exact ⟨G,Ω,inferInstance,inferInstance,1,1,0,⟨()⟩,inferInstance⟩

theorem inputs_distinct (p : ActionData.{a, b}) : zeroInput p ≠ otherInput p := by
  intro h
  have hh := congrArg (fun z : Input p => z.2.val.1) h
  norm_num [zeroInput,otherInput] at hh

theorem rejected_law : ¬ arena.{a, b}.Law rejected := by
  intro h
  exact inputs_distinct testData ((h testData).1 (show rejected.readout () testData
    (zeroInput testData) = rejected.readout () testData (otherInput testData) from rfl))

theorem dependence : ObservationalDependence signature.{a, b} actual := by
  intro _
  refine ⟨testData,zeroInput testData,otherInput testData,?_⟩
  exact fun h => inputs_distinct testData
    ((actual_strict_coordinates testData.u testData.v testData.c testData.x).1 h)

def registration : Registration arena.{a, b}
    (type_of% (@actual_strict_coordinates.{a, b})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @actual_strict_coordinates,rejected,rejected_law⟩
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
    (@actual_strict_coordinates.{a, b})
    (type_of% (realize signature.{a, b}
      (fun _ p => Phi p.u p.v p.c p.x)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.ActualLinkAffineFan.actual_strict_coordinates.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.ActualLinkAffineFan.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{a, b}⟩,
  objectArena := .source ⟨arena.{a, b}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{a, b} ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{a, b}
    (fun _ p => Phi p.u p.v p.c p.x)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.ActualLinkAffineFan,
    definition := none,
    coordinates := #[0,1,2,3,4,5,6,7,8],
    readouts := #[
      { path := #["body","body","body","body","body","body","body","body","body",
          "arg"],
        stateBinder := 0, functionOperand := true, stateOperand := none,
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
end Reg.D5.S3.Geometry.Gluing.ActualLinkAffineFan
