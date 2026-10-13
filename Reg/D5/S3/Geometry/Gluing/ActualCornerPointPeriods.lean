import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.ActualCornerPointPeriods
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open _root_.D5.S3.Geometry.Gluing.ActualLinkCornerChains
open _root_.D5.S3.Geometry.Gluing.ActualCornerPointPeriods

namespace Reg.D5.S3.Geometry.Gluing.ActualCornerPointPeriods
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

abbrev signature : Signature where
  Params := ActionData.{a,b}
  State p := Dart p.Ω
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{a,b} :=
  realize signature (fun _ p d => DartRelated p.u p.v (encode p.u p.v p.c (p.x,0)) d)
    (fun e => nomatch e)

def rejected : Realization signature.{a,b} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{a,b}
  Law R := ∀ p : ActionData.{a,b},
    0 < pointPeriod p.u p.v p.c p.x ∧
    Function.Injective (occurrence p.u p.v p.c p.x) ∧
    (∀ d : Dart p.Ω, R.readout () p d ↔
      ∃ i : Fin (3 * pointPeriod p.u p.v p.c p.x), occurrence p.u p.v p.c p.x i = d) ∧
    (∀ j k : Fin 4, j ≠ k ↔
      ∃! cs : Fin 4 × Fin 3, corner cs.1 cs.2 = j ∧ tip cs.1 cs.2 = k) ∧
    (∀ (y : p.Ω × Fin 3) (d : Dart p.Ω), DartStep p.u p.v (encode p.u p.v p.c y) d ↔
      d = encode p.u p.v p.c (tour p.u p.v p.c y) ∨
        d = encode p.u p.v p.c ((tour p.u p.v p.c).symm y)) ∧
    Function.minimalPeriod (tour p.u p.v p.c) (p.x,0) = 3 * pointPeriod p.u p.v p.c p.x ∧
    (∀ i : Fin (3 * pointPeriod p.u p.v p.c p.x), occurrence p.u p.v p.c p.x i =
      encode p.u p.v p.c (((fun y : p.Ω => act y (returnWord p.u p.v p.c))^[i.val/3] p.x),
        (i.val : Fin 3)))

theorem bridge :
    (type_of% (@actual_component_enumeration.{a,b})) ↔ arena.{a,b}.Law actual := by
  constructor
  · intro h p
    exact h p.u p.v p.c p.x
  · intro h G Ω gg action u v c x finiteΩ
    exact h ⟨G,Ω,gg,action,u,v,c,x,finiteΩ⟩

def testData : ActionData.{a,b} := by
  let G := Equiv.Perm (ULift.{a} (Fin 1))
  let Ω := ULift.{b} Unit
  letI : MulAction Gᵐᵒᵖ Ω := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl }
  exact ⟨G,Ω,inferInstance,inferInstance,1,1,0,⟨()⟩,inferInstance⟩

def sample : Dart testData.{a,b}.Ω :=
  encode testData.{a,b}.u testData.{a,b}.v testData.{a,b}.c (testData.{a,b}.x,0)
def other : Dart testData.{a,b}.Ω := ((testData.{a,b}.x,0),0)

theorem rejected_law : ¬ arena.{a,b}.Law rejected := by
  intro h
  have hp := (actual_component_enumeration testData.u testData.v testData.c testData.x).1
  apply ((h testData).2.2.1 sample).mpr
  exact ⟨⟨0,by omega⟩,rfl⟩

theorem dependence : ObservationalDependence signature.{a,b} actual := by
  intro _
  refine ⟨testData,sample,other,?_⟩
  change DartRelated testData.u testData.v sample sample ≠
    DartRelated testData.u testData.v sample other
  intro he
  have h : DartRelated testData.u testData.v sample other :=
    Eq.mp he (Relation.EqvGen.refl _)
  obtain ⟨i,hi⟩ :=
    ((actual_component_enumeration testData.u testData.v testData.c testData.x).2.2.1 other).mp h
  have hj := congrArg (fun d : Dart testData.Ω => (d.1.2,d.2)) hi
  change (corner 0 _, tip 0 _) = (0,0) at hj
  have hn (s : Fin 3) : corner 0 s ≠ tip 0 s := by
    fin_cases s <;> decide
  exact hn _ ((congrArg Prod.fst hj).trans (congrArg Prod.snd hj).symm)

def registration : Registration arena.{a,b}
    (type_of% (@actual_component_enumeration.{a,b})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @actual_component_enumeration,rejected,rejected_law⟩
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
    (@actual_component_enumeration.{a,b})
    (type_of% (realize signature.{a,b}
      (fun _ p d => DartRelated p.u p.v (encode p.u p.v p.c (p.x,0)) d)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.ActualCornerPointPeriods.actual_component_enumeration.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.ActualCornerPointPeriods.registration,
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
    (fun _ p d => DartRelated p.u p.v (encode p.u p.v p.c (p.x,0)) d)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.ActualCornerPointPeriods,
    definition := none,
    coordinates := #[0,1,4,5,6,7],
    readouts := #[
      { path := #["body","body","body","body","body","body","body","body","body",
          "arg","arg","fn","arg","body","fn","arg"],
        stateBinder := 9, functionOperand := false, stateOperand := none,
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
end Reg.D5.S3.Geometry.Gluing.ActualCornerPointPeriods
