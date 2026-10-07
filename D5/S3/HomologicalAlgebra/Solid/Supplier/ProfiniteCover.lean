/- GID: D5/S3/HomologicalAlgebra/Solid/Supplier/ProfiniteCover
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/Supplier/ProfiniteCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.

Uses Mathlib's Hausdorff–Alexandroff theorem by Vasilii Nesterov and the
light-condensed local-surjectivity API by Dagur Asgeirsson.
-/
import D5.S3.HomologicalAlgebra.Solid.Supplier.FreeAugmentation
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Condensed.Light.Epi

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite LightCondensed

namespace CWComparison

/-- The actual closed pullback of a light-profinite cover along a test section. -/
def coverFiber {T S : LightProfinite} {X : TopCat} (f : C(T, X)) (g : C(S, X)) :
    Set (S × T) := {p | g p.1 = f p.2}

theorem coverFiber_isClosed {T S : LightProfinite} {X : TopCat} [T2Space X]
    (f : C(T, X)) (g : C(S, X)) : IsClosed (coverFiber f g) :=
  isClosed_eq (g.continuous.comp continuous_fst) (f.continuous.comp continuous_snd)

/-- This pullback is light profinite, including for nonconstant test sections. -/
def coverPullback {T S : LightProfinite} {X : TopCat} [T2Space X]
    (f : C(T, X)) (g : C(S, X)) : LightProfinite := by
  letI : CompactSpace (coverFiber f g) :=
    isCompact_iff_compactSpace.mp (coverFiber_isClosed f g).isCompact
  exact LightProfinite.of (coverFiber f g)

def coverPullbackFst {T S : LightProfinite} {X : TopCat} [T2Space X]
    (f : C(T, X)) (g : C(S, X)) : coverPullback f g ⟶ S :=
  ConcreteCategory.ofHom ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

def coverPullbackSnd {T S : LightProfinite} {X : TopCat} [T2Space X]
    (f : C(T, X)) (g : C(S, X)) : C(coverPullback f g, T) :=
  ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩

theorem coverPullbackFst_surjective {T S : LightProfinite} {X : TopCat} [T2Space X]
    (f : C(T, X)) (g : C(S, X)) (hf : Function.Surjective f) :
    Function.Surjective (coverPullbackFst f g) := by
  intro s
  obtain ⟨t, ht⟩ := hf (g s)
  exact ⟨⟨(s, t), ht.symm⟩, rfl⟩

/-- A continuous surjection from a light profinite space to a Hausdorff space
is genuinely an epimorphism of light condensed sets. -/
theorem profiniteCover_condensed_epi {T : LightProfinite} {X : TopCat} [T2Space X]
    (f : C(T, X)) (hf : Function.Surjective f) :
    Epi (topCatToLightCondSet.map (TopCat.ofHom f)) := by
  rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite]
  intro S g
  change C(S, X) at g
  refine ⟨coverPullback f g, coverPullbackFst f g,
    coverPullbackFst_surjective f g hf, coverPullbackSnd f g, ?_⟩
  change f.comp (coverPullbackSnd f g) =
    g.comp (coverPullbackFst f g).hom.hom
  ext p
  exact p.property.symm

/-- The same covering augmentation is epimorphic for the protected free functor. -/
theorem profiniteCover_free_epi {T : LightProfinite} {X : TopCat} [T2Space X]
    (f : C(T, X)) (hf : Function.Surjective f) :
    Epi (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map (TopCat.ofHom f)) := by
  have := profiniteCover_condensed_epi f hf
  exact (free ℤ).map_epi _

/-- The binary Cantor cover uses the genuine interval topology. -/
abbrev cantorProfinite : LightProfinite := LightProfinite.of (ℕ → Bool)

def binaryIntervalCover : C(cantorProfinite, unitInterval) :=
  ⟨Real.fromBinary, Real.fromBinary_continuous⟩

/-- Its free augmentation onto the actual free condensed interval object. -/
theorem binaryIntervalCover_free_epi :
    Epi (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map
      (TopCat.ofHom binaryIntervalCover)) :=
  profiniteCover_free_epi (X := TopCat.of unitInterval)
    binaryIntervalCover Real.fromBinary_surjective

end CWComparison
