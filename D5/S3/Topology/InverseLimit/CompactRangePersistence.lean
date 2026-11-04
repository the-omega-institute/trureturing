/- GID: D5/S3/Topology/InverseLimit/CompactRangePersistence
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/CompactRangePersistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual compact natural ranges persist at arbitrary cofiltered limits. -/

import Mathlib.Topology.Category.TopCat.Limits.Konig
import Mathlib.Topology.Separation.Hausdorff

/-!
Closed fibres over a specified actual thread form a compact nonempty
cofiltered system. The existing topological Koenig theorem pays finite
consistency through an upper named stage; no fibre bonding map is required
to be onto. No countability or ordinal cofinality hypothesis occurs.
Source: supplied 4 November 2026 reservoir theorem and independent review.
This is a classical supplier, with original Efimov KPI 0.
-/

open CategoryTheory CategoryTheory.Limits Set Function Topology

namespace D5.S3.Topology.InverseLimit.CompactRangePersistence

universe u v
variable {J : Type u} [SmallCategory J]
variable (F G : J ⥤ TopCat.{max u v}) (t : F ⟶ G)

/-- The actual coordinatewise map of concrete coherent-thread spaces. -/
def limitMap : C((TopCat.limitCone F).pt, (TopCat.limitCone G).pt) where
  toFun x := ⟨fun j => t.app j (x.val j), fun {i j} f => by
    have h := ConcreteCategory.congr_hom (t.naturality f) (x.val i)
    change t.app j (F.map f (x.val i)) = G.map f (t.app i (x.val i)) at h
    rw [← h,x.property f]⟩
  continuous_toFun := (continuous_pi fun j =>
    (t.app j).hom.continuous.comp ((continuous_apply j).comp continuous_subtype_val)).subtype_mk _

/-- The actual continuous restriction of a bonding map to one thread fibre. -/
def fiberMap (b : (TopCat.limitCone G).pt) {i j : J} (f : i ⟶ j) :
    C({x : F.obj i // t.app i x = b.val i}, {x : F.obj j // t.app j x = b.val j}) where
  toFun x := ⟨F.map f x.val, by
    exact (ConcreteCategory.congr_hom (t.naturality f) x.val).trans
      ((congrArg (fun y => G.map f y) x.property).trans (b.property f))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (F.map f).hom.continuous.comp continuous_subtype_val

/-- Fibres are actual closed subspaces, with their actual restricted maps. -/
def fiberDiagram (b : (TopCat.limitCone G).pt) : J ⥤ TopCat.{max u v} where
  obj j := TopCat.of {x : F.obj j // t.app j x = b.val j}
  map f := TopCat.ofHom (fiberMap F G t b f)
  map_id j := by ext x; exact ConcreteCategory.congr_hom (F.map_id j) x.val
  map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x.val

/-- Proper-stage membership in every actual natural range forces membership
in the actual final range. Fibre maps need not be onto. The index may have
any cofinality, and need not be an ordinal. -/
theorem mem_range_limit_map [IsCofilteredOrEmpty J]
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)] [∀ j, T2Space (G.obj j)]
    (b : (TopCat.limitCone G).pt) (hb : ∀ j, b.val j ∈ range (t.app j)) :
    b ∈ range (limitMap F G t) := by
  classical
  let H := fiberDiagram F G t b
  let : ∀ j, Nonempty (H.obj j) := fun j => by
    obtain ⟨z,hz⟩ := hb j
    exact ⟨⟨z,hz⟩⟩
  let : ∀ j, CompactSpace (H.obj j) := fun j =>
    (isClosed_eq (t.app j).hom.continuous continuous_const).isClosedEmbedding_subtypeVal.compactSpace
  let : ∀ j, T2Space (H.obj j) := fun j => inferInstanceAs (T2Space {x : F.obj j // t.app j x = b.val j})
  obtain ⟨z⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system H
  let x : (TopCat.limitCone F).pt :=
    ⟨fun j => (z.val j).val,fun {i j} f => congrArg Subtype.val (z.property f)⟩
  refine ⟨x,?_⟩
  apply Subtype.ext
  funext j
  exact (z.val j).property

end D5.S3.Topology.InverseLimit.CompactRangePersistence
