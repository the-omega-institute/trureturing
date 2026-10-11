/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteFreeSolid
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteFreeSolid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationDifferenceRelation
import D5.S3.HomologicalAlgebra.Solid.BoundedMeasures
import D5.S3.HomologicalAlgebra.Solid.Supplier.FreeAugmentation

/-!
Actual solidity of the free object on a finite light-profinite space,
including the empty case. The point/free/discrete comparison is reused
from the immutable, independently audited Apache-2.0 CWComparison supplier.
This supplies the finite initial term in the concrete generator retract;
it makes no bounded-only replacement of the full target.
New proofs, Apache-2.0; finite coproduct/limits APIs are from pinned Mathlib.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite LightCondensed

namespace LightCondensed.Solid
open IntProof
attribute [local instance] FintypeCat.botTopology FintypeCat.discreteTopology

/-- The genuine free light-profinite point, with its actual topology. -/
def freeProfinitePointIsoInt : freeOn (LightProfinite.of PUnit.{1}) ≅ Zdisc :=
  (Functor.isoWhiskerRight lightProfiniteToLightCondSetIsoTopCatToLightCondSet
    (free ℤ)).app (LightProfinite.of PUnit.{1}) ≪≫ CWComparison.freePointIsoInt

theorem isSolid_freeProfinitePoint : isSolid (freeOn (LightProfinite.of PUnit.{1})) :=
  isSolid.prop_of_iso freeProfinitePointIsoInt.symm isSolid_int

/-- The finite discrete space really is the finite coproduct of its points. -/
def finiteProfinitePointsIso (S : LightProfinite) [Finite S] [DiscreteTopology S] :
    CompHausLike.finiteCoproduct (fun _ : S => LightProfinite.of PUnit.{1}) ≅ S where
  hom := ConcreteCategory.ofHom ⟨fun p => p.1, continuous_of_discreteTopology⟩
  inv := ConcreteCategory.ofHom ⟨fun s => ⟨s, PUnit.unit⟩, continuous_of_discreteTopology⟩
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, u⟩
    cases u
    rfl
  inv_hom_id := by ext s; rfl

/-- Solidity follows from a genuine preserved finite coproduct, also for
an empty index. No comparison only on ordinary points is substituted. -/
theorem isSolid_free_finite (S : LightProfinite) [Finite S] [DiscreteTopology S] :
    isSolid (freeOn S) := by
  let F := lightProfiniteToLightCondSet ⋙ free ℤ
  have h : isSolid (F.obj (CompHausLike.finiteCoproduct
      (fun _ : S => LightProfinite.of PUnit.{1}))) := by
    apply isSolid.prop_of_isColimit (isColimitOfPreserves F
      (CompHausLike.finiteCoproduct.isColimit
        (fun _ : S => LightProfinite.of PUnit.{1})))
    rintro ⟨s⟩
    exact isSolid_freeProfinitePoint
  exact isSolid.prop_of_iso (F.mapIso (finiteProfinitePointsIso S)) h

/-- In particular the actual initial finite quotient used in the retract
has a solid free object; it is not silently treated as an infinite space. -/
theorem isSolid_free_initialComponent (S : LightProfinite) :
    isSolid (freeOn (S.component 0)) := by
  letI : Finite (S.component 0) :=
    inferInstanceAs (Finite (S.fintypeDiagram.obj ⟨0⟩))
  haveI : DiscreteTopology (S.component 0) := by
    change DiscreteTopology (S.fintypeDiagram.obj ⟨0⟩)
    infer_instance
  exact isSolid_free_finite (S.component 0)

end LightCondensed.Solid
