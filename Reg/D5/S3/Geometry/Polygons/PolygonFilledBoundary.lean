import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Polygons.PolygonFilledBoundary
import Reg.Support.DependentFamily

/-! Full coordinate, region and size family for the filled polygon bridge. -/

namespace Reg.D5.S3.Geometry.Polygons.PolygonFilledBoundary
open _root_.D5.S3.Geometry.Polygons.PolygonFilledBoundary
open _root_.D5.S3.Geometry.Polygons.PolygonInteriorDiagonals
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Module
universe u

abbrev source_scope := type_of% (@boundaryModel_of_filled.{u})
def source : source_scope.{u} := @boundaryModel_of_filled.{u}

structure Parameters where
  E : Type u
  group : NormedAddCommGroup E
  space : @NormedSpace ℝ E _ group.toSeminormedAddCommGroup
  n : ℕ
  nonzero : NeZero n

attribute [instance] Parameters.group Parameters.space Parameters.nonzero

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Polygon p.E p.n × Set p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature.{u}
    (fun _ _ q => q.2 = convexHull ℝ (range q.1.vertices) ∧ BoundaryModel q.1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ (p : Parameters.{u}) (hdim : finrank ℝ p.E = 2)
    (poly : Polygon p.E p.n) (C : Set p.E) (h : FilledModel poly C),
    O.readout () p (poly,C)

theorem bridge : source_scope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p hdim poly C model
    exact @h p.E p.group p.space p.n p.nonzero hdim poly C model
  · intro h E group space n nonzero hdim poly C model
    exact h ⟨E,group,space,n,nonzero⟩ hdim poly C model

theorem actual_law : arena.{u}.Law actual.{u} := bridge.{u}.mp source.{u}

noncomputable def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => False) (fun e => nomatch e)

theorem rejected_of_model (p : Parameters.{u}) (hdim : finrank ℝ p.E = 2)
    (poly : Polygon p.E p.n) (C : Set p.E) (h : FilledModel poly C) :
    ¬ arena.{u}.Law rejected.{u} := by
  intro law
  exact law p hdim poly C h

end Reg.D5.S3.Geometry.Polygons.PolygonFilledBoundary
