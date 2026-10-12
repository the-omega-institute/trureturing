import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.ActualLinkAffineFan
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.ActualCornerTransport
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

-- Full source telescopes for the new relation claims. The four-slot
-- registrations remain unfinished under issue 15679; these exact bridges
-- are not asserted to be declared_validated registrations.
abbrev relationSignature : Signature where
  Params := ActionData.{a,b}
  State p := Input p × Input p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def stepActual : Realization relationSignature.{a,b} :=
  realize relationSignature
    (fun _ p z => Step p.u p.v (Phi p.u p.v p.c p.x z.1).val
      (Phi p.u p.v p.c p.x z.2).val) (fun e => nomatch e)

abbrev stepArena : Arena where
  signature := relationSignature.{a,b}
  Law R := ∀ p : ActionData.{a,b}, ∀ z : Input p × Input p,
    R.readout () p z ↔ seam z.1 z.2 ∨ seam z.2 z.1

theorem step_bridge :
    (type_of% (@actual_step_iff.{a,b})) ↔ stepArena.{a,b}.Law stepActual := by
  constructor
  · intro h p z
    exact h p.u p.v p.c p.x z.1 z.2
  · intro h G Ω gg action u v c x finiteΩ z w
    exact h ⟨G,Ω,gg,action,u,v,c,x,finiteΩ⟩ (z,w)

def chainActual : Realization relationSignature.{a,b} :=
  realize relationSignature
    (fun _ p z => Related p.u p.v (Phi p.u p.v p.c p.x z.1).val
      (Phi p.u p.v p.c p.x z.2).val) (fun e => nomatch e)

abbrev chainArena : Arena where
  signature := relationSignature.{a,b}
  Law R := ∀ p : ActionData.{a,b}, ∀ z : Input p × Input p,
    R.readout () p z ↔ Relation.EqvGen seam z.1 z.2

theorem chain_bridge :
    (type_of% (@actual_eqvgen_iff.{a,b})) ↔ chainArena.{a,b}.Law chainActual := by
  constructor
  · intro h p z
    exact h p.u p.v p.c p.x z.1 z.2
  · intro h G Ω gg action u v c x finiteΩ z w
    exact h ⟨G,Ω,gg,action,u,v,c,x,finiteΩ⟩ (z,w)

abbrev fullFanArena : Arena where
  signature := relationSignature.{a,b}
  Law R := ∀ p : ActionData.{a,b}, ∀ z : Input p × Input p,
    R.readout () p z ↔ _root_.D5.S3.Geometry.Gluing.CyclicTriangleDisk.Related
      (closedInput z.1) (closedInput z.2)

theorem full_fan_bridge :
    (type_of% (@actual_full_fan_correspondence.{a,b})) ↔
      fullFanArena.{a,b}.Law chainActual := by
  constructor
  · intro h p z
    exact h p.u p.v p.c p.x z.1 z.2
  · intro h G Ω gg action u v c x finiteΩ z w
    exact h ⟨G,Ω,gg,action,u,v,c,x,finiteΩ⟩ (z,w)

structure OpenData where
  G : Type a
  Ω : Type b
  groupG : Group G
  action : letI := groupG; MulAction Gᵐᵒᵖ Ω
  topology : TopologicalSpace Ω
  discrete : letI := topology; DiscreteTopology Ω
  u : G
  v : G
  c : Fin 4
  x : Ω

attribute [instance] OpenData.groupG OpenData.action OpenData.topology OpenData.discrete

abbrev openSignature : Signature where
  Params := OpenData.{a,b}
  State _ := Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def openActual : Realization openSignature.{a,b} :=
  realize openSignature (fun _ p k =>
    let q := @Quotient.mk' _ (Relation.EqvGen.setoid
      (Step p.u p.v (ν := vertex p.u p.v p.c p.x)))
    let U := quotientNeighborhood p.u p.v p.c p.x
    if k = 0 then q ⁻¹' U = Neighborhood p.u p.v (ν := vertex p.u p.v p.c p.x)
      (encode p.u p.v p.c (p.x,0))
    else if k = 1 then IsOpen U
    else Topology.IsQuotientMap (U.restrictPreimage q)) (fun e => nomatch e)

abbrev openArena : Arena where
  signature := openSignature.{a,b}
  Law R := ∀ p : OpenData.{a,b}, ∀ k : Fin 3, R.readout () p k

theorem open_bridge :
    (type_of% (@actual_open_quotient_neighborhood.{a,b})) ↔
      openArena.{a,b}.Law openActual := by
  constructor
  · intro h p k
    fin_cases k
    · exact (h p.u p.v p.c p.x).1
    · exact (h p.u p.v p.c p.x).2.1
    · exact (h p.u p.v p.c p.x).2.2
  · intro h G Ω gg action topology discrete u v c x
    let p : OpenData.{a,b} := ⟨G,Ω,gg,action,topology,discrete,u,v,c,x⟩
    exact ⟨h p 0,h p 1,h p 2⟩

-- This faithful proposition readout has no observational state variation:
-- all three actual observations are true. It cannot supply the dependence
-- field of a four-slot registration; issue 15679 remains unfinished.
theorem open_observation_constant (p : OpenData.{a,b}) (i j : Fin 3) :
    openActual.readout () p i = openActual.readout () p j := by
  have h := open_bridge.mp @actual_open_quotient_neighborhood
  exact propext ⟨fun _ => h p j,fun _ => h p i⟩

structure SliceData where
  G : Type a
  Ω : Type b
  groupG : Group G
  action : letI := groupG; MulAction Gᵐᵒᵖ Ω
  u : G
  v : G
  ν : letI := groupG; letI := action; Vertex (pairing (Ω := Ω) u v)
attribute [instance] SliceData.groupG SliceData.action

namespace sliceCarrierAudit
abbrev signature : Signature where
  Params := SliceData.{a,b}
  State p := Point p.u p.v p.ν
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ↥(Slice p.u p.v p.ν)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{a,b} := realize signature
  (fun _ p z => ⟨toTruncation p.u p.v z,by
    exact ⟨z.val.1.2,by simp [toTruncation,alpha,z.property.1],z.property.2.2.2⟩⟩) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{a,b}
  Law R := ∀ p : SliceData.{a,b}, Function.Bijective (R.readout () p)
theorem bridge : (type_of% (@actual_slice_carriers.{a,b})) ↔ arena.{a,b}.Law actual := by
  constructor
  · intro h p; exact h p.u p.v p.ν
  · intro h G Ω gg action u v ν; exact h ⟨G,Ω,gg,action,u,v,ν⟩

def collapse (p : SliceData.{a,b}) (z : Point p.u p.v p.ν) : Point p.u p.v p.ν :=
  ⟨(z.val.1,fun i => if i = z.val.1.2 + 1 then 1 else 0),by
    refine ⟨?_,?_,by simp,z.property.2.2.2⟩
    · have h : z.val.1.2 ≠ z.val.1.2 + 1 := by
        generalize z.val.1.2 = j
        fin_cases j <;> decide
      simp [h]
    · intro i; dsimp; split_ifs <;> norm_num⟩
def rejected : Realization signature.{a,b} := realize signature
  (fun _ p z => actual.readout () p (collapse p z)) (fun e => nomatch e)

def test : SliceData.{a,b} :=
  ⟨testData.G,testData.Ω,inferInstance,inferInstance,testData.u,testData.v,
    label (pairing testData.u testData.v) (testData.x,0)⟩
def p0 : Point test.u test.v test.ν :=
  ⟨((testData.x,0),fun i => if i = 1 then 1 else 0),by
    refine ⟨by norm_num [Fin.ext_iff],?_,by simp,rfl⟩
    intro i; dsimp; split_ifs <;> norm_num⟩
def p1 : Point test.u test.v test.ν :=
  ⟨((testData.x,0),fun i => if i = 2 then 1 else 0),by
    refine ⟨by norm_num [Fin.ext_iff],?_,by simp,rfl⟩
    intro i; dsimp; split_ifs <;> norm_num⟩
theorem distinct : p0.{a,b} ≠ p1 := by
  intro h
  have hh := congrArg (fun z : Point test.u test.v test.ν => z.val.2 1) h
  norm_num [p0,p1,Fin.ext_iff] at hh

theorem rejected_law : ¬ arena.{a,b}.Law rejected := by
  intro h
  exact distinct ((h test).1 (show rejected.readout () test p0 =
    rejected.readout () test p1 from rfl))
def registration : Registration arena.{a,b} (type_of% (@actual_slice_carriers.{a,b})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @actual_slice_carriers,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,rfl,rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨test,p0,p1,fun h => distinct ((actual_slice_carriers test.u test.v test.ν).1 h)⟩

def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_slice_carriers.{a, b})
    (type_of% (realize signature.{a, b}
      (fun _ p => actual.readout () p)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.ActualLinkAffineFan.actual_slice_carriers.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.ActualLinkAffineFan.sliceCarrierAudit.registration,
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
    (fun _ p => actual.readout () p)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.ActualLinkAffineFan,
    definition := none,
    coordinates := #[0,1,2,3,4,5,6],
    readouts := #[
      { path := #["body","body","body","body","body","body","body",
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
end sliceCarrierAudit

-- Exact source-law bridges for the full slice relations. These remain
-- source-selection-incomplete attempts under issue 15679; the exact four-slot
-- objects below are not claimed to have native audit admission.
abbrev sliceRelationSignature : Signature where
  Params := SliceData.{a,b}
  State p := Point p.u p.v p.ν × Point p.u p.v p.ν
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def sliceStepActual : Realization sliceRelationSignature.{a,b} :=
  realize sliceRelationSignature (fun _ p z => Step p.u p.v z.1 z.2) (fun e => nomatch e)
abbrev sliceStepArena : Arena where
  signature := sliceRelationSignature.{a,b}
  Law R := ∀ p : SliceData.{a,b}, ∀ z : Point p.u p.v p.ν × Point p.u p.v p.ν,
    R.readout () p z ↔ TruncatedStep p.u p.v (toTruncation p.u p.v z.1)
      (toTruncation p.u p.v z.2)
theorem slice_step_bridge : (type_of% (@actual_slice_step_iff.{a,b})) ↔
    sliceStepArena.{a,b}.Law sliceStepActual := by
  constructor
  · intro h p z; exact h p.u p.v z.1 z.2
  · intro h G Ω gg action u v ν p q; exact h ⟨G,Ω,gg,action,u,v,ν⟩ (p,q)

def sliceChainActual : Realization sliceRelationSignature.{a,b} :=
  realize sliceRelationSignature (fun _ p z => Related p.u p.v z.1 z.2) (fun e => nomatch e)
abbrev sliceChainArena : Arena where
  signature := sliceRelationSignature.{a,b}
  Law R := ∀ p : SliceData.{a,b}, ∀ z : Point p.u p.v p.ν × Point p.u p.v p.ν,
    R.readout () p z ↔ Relation.EqvGen (TruncatedStep p.u p.v)
      (toTruncation p.u p.v z.1) (toTruncation p.u p.v z.2)
theorem slice_chain_bridge : (type_of% (@actual_slice_eqvgen_iff.{a,b})) ↔
    sliceChainArena.{a,b}.Law sliceChainActual := by
  constructor
  · intro h p z; exact h p.u p.v z.1 z.2
  · intro h G Ω gg action u v ν p q; exact h ⟨G,Ω,gg,action,u,v,ν⟩ (p,q)
namespace sliceRelationAudit
open sliceCarrierAudit (test p0 p1)

def paired : Point test.u test.v test.ν := pairedPoint test.u test.v p0 2 (by change (2 : Fin 4) ≠ 0; decide)
private theorem step_yes : Step test.u test.v p0 paired :=
  ⟨2,by decide,by norm_num [p0,Fin.ext_iff],rfl⟩
private theorem step_no : ¬ Step test.u test.v p0 p0 := by
  rintro ⟨f,_,_,h⟩
  have hh := congrArg (fun z : Raw test.Ω => z.1.2) h
  change (0 : Fin 4) = facePerm f 0 at hh
  fin_cases f <;> norm_num [facePerm,Fin.ext_iff] at hh

def stepRejected : Realization sliceRelationSignature.{a,b} :=
  realize sliceRelationSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem step_rejected_law : ¬ sliceStepArena.{a,b}.Law stepRejected := by
  intro h
  exact (h test (p0,paired)).mpr ((actual_slice_step_iff test.u test.v p0 paired).mp step_yes)

def stepRegistration : Registration sliceStepArena.{a,b}
    (type_of% (@actual_slice_step_iff.{a,b})) where
  actual := sliceStepActual
  bridge := slice_step_bridge
  variation := ⟨slice_step_bridge.mp @actual_slice_step_iff,stepRejected,step_rejected_law⟩
  sensitivity := ⟨fun i => ⟨stepRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,rfl,step_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨test,(p0,paired),(p0,p0),?_⟩
    intro h
    exact step_no (Eq.mp h step_yes)

def interiorA : Point test.u test.v test.ν :=
  ⟨((testData.x,0),fun i => if i = 0 then 0 else 1/3),by
    refine ⟨by norm_num,?_,?_,rfl⟩
    · intro i; dsimp; split_ifs <;> norm_num
    · norm_num [Fin.sum_univ_succ]⟩
def interiorB : Point test.u test.v test.ν :=
  ⟨((testData.x,0),![0,1/2,1/4,1/4]),by
    refine ⟨by norm_num,?_,?_,rfl⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_succ]⟩
private theorem interiorA_interior : Interior (interiorA.{a,b}) := by
  intro f hf
  change (if f = 0 then (0 : ℝ) else 1/3) ≠ 0
  change f ≠ 0 at hf
  norm_num [hf]
private theorem interior_ne : interiorB.{a,b} ≠ interiorA := by
  intro h
  have hh := congrArg (fun z : Point test.u test.v test.ν => z.val.2 1) h
  norm_num [interiorA,interiorB] at hh
private theorem chain_no : ¬ Related test.u test.v (interiorA.{a,b}) interiorB := by
  intro h
  exact interior_ne (((actual_guarded_point_analysis test.u test.v interiorA interiorB).1
    interiorA_interior).mp h)

def chainRejected : Realization sliceRelationSignature.{a,b} :=
  realize sliceRelationSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem chain_rejected_law : ¬ sliceChainArena.{a,b}.Law chainRejected := by
  intro h
  exact (h test (interiorA,interiorA)).mpr (Relation.EqvGen.refl _)

def chainRegistration : Registration sliceChainArena.{a,b}
    (type_of% (@actual_slice_eqvgen_iff.{a,b})) where
  actual := sliceChainActual
  bridge := slice_chain_bridge
  variation := ⟨slice_chain_bridge.mp @actual_slice_eqvgen_iff,chainRejected,chain_rejected_law⟩
  sensitivity := ⟨fun i => ⟨chainRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,rfl,chain_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨test,(interiorA,interiorA),(interiorA,interiorB),?_⟩
    intro h
    exact chain_no (Eq.mp h (Relation.EqvGen.refl _))

-- The exact four-slot objects above are compiled attempts. Mapping the paired
-- state to the two original relation binders for a Contract source selection
-- remains issue 15679; no artificial constant-truth source readout is registered.
#print axioms stepRegistration
#print axioms chainRegistration
end sliceRelationAudit

#print axioms slice_step_bridge
#print axioms slice_chain_bridge
#print axioms actualOpenDiskChart
#print axioms actualSliceQuotientHomeomorph

#print axioms registration
#print axioms actual_step_iff
#print axioms actual_eqvgen_iff
#print axioms actual_open_quotient_neighborhood
#print axioms actual_full_fan_correspondence
#print axioms actualSeamQuotientHomeomorph
#print axioms step_bridge
#print axioms chain_bridge
#print axioms open_bridge
end
end Reg.D5.S3.Geometry.Gluing.ActualLinkAffineFan
