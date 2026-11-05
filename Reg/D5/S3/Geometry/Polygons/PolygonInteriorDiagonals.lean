import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Polygons.PolygonInteriorDiagonals
import Reg.Support.DependentFamily

/-! Native diagonal readout on the complete coordinate and size family. -/

namespace Reg.D5.S3.Geometry.Polygons.PolygonInteriorDiagonals
open _root_.D5.S3.Geometry.Polygons.PolygonInteriorDiagonals
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Module
universe u

abbrev source_scope := type_of% (@isDiagonal_iff_openSegment_subset_interior.{u})
def source : source_scope.{u} := @isDiagonal_iff_openSegment_subset_interior.{u}

structure Parameters where
  E : Type u
  group : NormedAddCommGroup E
  space : @NormedSpace ℝ E _ group.toSeminormedAddCommGroup
  n : ℕ
  nonzero : NeZero n

attribute [instance] Parameters.group Parameters.space Parameters.nonzero

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Sym2 (ZMod p.n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p e => Carrier.IsDiagonal e) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ (p : Parameters.{u}) (hdim : finrank ℝ p.E = 2) (hn : 3 ≤ p.n)
    (poly : Polygon p.E p.n) (B : BoundaryModel poly) (i j : ZMod p.n),
    O.readout () p s(i,j) ↔ vertex poly i ≠ vertex poly j ∧
      openSegment ℝ (vertex poly i) (vertex poly j) ⊆
        interior (convexHull ℝ (range poly.vertices))

theorem bridge : source_scope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p hdim hn poly B i j
    exact @h p.E p.group p.space p.n p.nonzero hdim hn poly B i j
  · intro h E group space n nonzero hdim hn poly B i j
    exact h ⟨E,group,space,n,nonzero⟩ hdim hn poly B i j

theorem actual_law : arena.{u}.Law actual.{u} := bridge.{u}.mp source.{u}

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  let p : Parameters.{u} := ⟨PUnit.{u+1}, inferInstance, inferInstance, 4, inferInstance⟩
  refine ⟨p, s((0 : ZMod 4),0), s((0 : ZMod 4),2), ?_⟩
  change Carrier.IsDiagonal s((0 : ZMod 4),0) ≠ Carrier.IsDiagonal s((0 : ZMod 4),2)
  decide

noncomputable def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => True) (fun e => nomatch e)

theorem rejected_of_model (p : Parameters.{u}) (hdim : finrank ℝ p.E = 2)
    (hn : 3 ≤ p.n) (poly : Polygon p.E p.n) (B : BoundaryModel poly) :
    ¬ arena.{u}.Law rejected.{u} := by
  intro law
  have h := (law p hdim hn poly B 0 0).mp trivial
  exact h.1 rfl

/-!
The enrolled readout is the native diagonal predicate over all unordered label
pairs. Parameters retain the complete ambient coordinate and size family; the law
retains the plane dimension, boundary model, and every pair of labels. Neither
finite roles nor the size lower bound truncates the source coordinate family.
-/

end Reg.D5.S3.Geometry.Polygons.PolygonInteriorDiagonals
