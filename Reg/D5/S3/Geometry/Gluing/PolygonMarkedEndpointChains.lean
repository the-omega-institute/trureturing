import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.PolygonMarkedEndpointChains
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanEval.Topology.ClassificationOfSurfaces
open _root_.D5.S3.Geometry.Gluing.PolygonMarkedEndpointChains

namespace Reg.D5.S3.Geometry.Gluing.PolygonMarkedEndpointChains
noncomputable section
universe u

structure PolygonData where
  Face : Type u
  count : Face → ℕ
  I : Set (PolygonGluing.Identification Face count)

abbrev signature : Signature where
  Params := PolygonData.{u}
  State p := PolygonGluing.Side p.Face p.count × PolygonGluing.Side p.Face p.count
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ p s => PolygonGluing.setoid p.I (s.1.point 0) (s.2.point 0))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : PolygonData.{u},
    (∀ x y : PolygonGluing.PreRealization p.Face p.count,
      PolygonGluing.setoid p.I x y →
        ((∃ s : PolygonGluing.Side p.Face p.count, x = s.point 0) ↔
          (∃ s : PolygonGluing.Side p.Face p.count, y = s.point 0))) ∧
    (∀ s t : PolygonGluing.Side p.Face p.count,
      R.readout () p (s,t) ↔ Relation.EqvGen (EndpointStep p.I) s t)

theorem bridge :
    (type_of% (@polygon_marked_endpoint_chains.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p
    exact h p.I
  · intro h Face count I
    exact h ⟨Face,count,I⟩

def testData : PolygonData.{u} := ⟨ULift.{u} Unit,fun _ => 2,∅⟩

def zeroSide : PolygonGluing.Side testData.Face testData.count := ⟨⟨()⟩,⟨0, by change 0 < 2; decide⟩⟩
def oneSide : PolygonGluing.Side testData.Face testData.count := ⟨⟨()⟩,⟨1, by change 1 < 2; decide⟩⟩
def sample : signature.{u}.State testData := (zeroSide,zeroSide)
def other : signature.{u}.State testData := (zeroSide,oneSide)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact ((h testData).2 zeroSide zeroSide).mpr (Relation.EqvGen.refl _)

theorem other_not_related : ¬ PolygonGluing.setoid testData.I
    (other.1.point 0) (other.2.point 0) := by
  intro h
  have he := ((polygon_marked_endpoint_chains testData.I).2 other.1 other.2).mp h
  have same : ∀ s t : PolygonGluing.Side testData.Face testData.count,
      Relation.EqvGen (EndpointStep testData.I) s t → s = t := by
    intro s t hh
    induction hh with
    | rel s t hh =>
      cases hh with
      | glue a ha b => exact False.elim ha
    | refl s => rfl
    | symm s t _ ih => exact ih.symm
    | trans s t r _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hs := same other.1 other.2 he
  have hi := congrArg
    (fun s : PolygonGluing.Side testData.Face testData.count => s.index.val) hs
  change (0 : ℕ) = 1 at hi
  exact Nat.zero_ne_one hi

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨testData,sample,other,?_⟩
  intro h
  apply other_not_related
  exact Eq.mp h (Relation.EqvGen.refl _)

def registration : Registration arena.{u}
    (type_of% (@polygon_marked_endpoint_chains.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @polygon_marked_endpoint_chains,rejected,rejected_law⟩
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
    (@polygon_marked_endpoint_chains.{u})
    (type_of% (realize signature.{u}
      (fun _ p s => PolygonGluing.setoid p.I (s.1.point 0) (s.2.point 0))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.PolygonMarkedEndpointChains.polygon_marked_endpoint_chains.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.PolygonMarkedEndpointChains.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u}
    (fun _ p s => PolygonGluing.setoid p.I (s.1.point 0) (s.2.point 0))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.PolygonMarkedEndpointChains,
    definition := none,
    coordinates := #[0,1,2],
    readouts := #[{
      path := #["body","body","body","arg","body","body","fn","arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Geometry.Gluing.PolygonMarkedEndpointChains
