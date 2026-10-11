/- GID: D5/S3/HomologicalAlgebra/Solid/DerivedAdjunction
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/DerivedAdjunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.ComplexAdjunction
import D5.S3.HomologicalAlgebra.Solid.Reflection

/-!
Supporting results for the unbounded derived adjunction.  These do not assume
existence of derived solidification or import the upstream derived gaps.
-/

noncomputable section
open CategoryTheory Limits

namespace CWSolid

/-- An additive adjunction descends to homotopy categories, without any
boundedness hypothesis. -/
def mapHomotopyCategoryAdjunction
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    (adj : F ⊣ G) :
    F.mapHomotopyCategory (.up ℤ) ⊣ G.mapHomotopyCategory (.up ℤ) := by
  let c := ComplexShape.up ℤ
  letI : CatCommSq (F.mapHomologicalComplex c)
      (HomotopyCategory.quotient C c) (HomotopyCategory.quotient D c)
      (F.mapHomotopyCategory c) := ⟨(F.mapHomotopyCategoryFactors c).symm⟩
  letI : CatCommSq (G.mapHomologicalComplex c)
      (HomotopyCategory.quotient D c) (HomotopyCategory.quotient C c)
      (G.mapHomotopyCategory c) := ⟨(G.mapHomotopyCategoryFactors c).symm⟩
  exact (mapHomologicalComplexAdjunction adj c).localization
    (HomotopyCategory.quotient C c) (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quotient D c) (HomologicalComplex.homotopyEquivalences D c)
    (F.mapHomotopyCategory c) (G.mapHomotopyCategory c)

set_option backward.isDefEq.respectTransparency false in
/-- The left adjoint of an exact additive functor sends unbounded
K-projective complexes to K-projective complexes. -/
theorem map_isKProjective_of_exact_rightAdjoint
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (K : CochainComplex C ℤ) [K.IsKProjective] :
    CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  rw [CochainComplex.isKProjective_iff_leftOrthogonal]
  intro L f hL
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
  have hGL : HomotopyCategory.subcategoryAcyclic C
      ((G.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient D (.up ℤ)).obj L)) := by
    change HomotopyCategory.subcategoryAcyclic C
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj L))
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    intro n
    exact (hL n).map G
  let adjh := mapHomotopyCategoryAdjunction adj
  apply (adjh.homEquiv _ _).injective
  have hf := CochainComplex.IsKProjective.leftOrthogonal K
    (adjh.homEquiv _ _ f) hGL
  exact hf.trans (adjh.homAddEquiv_zero _ _).symm

end CWSolid

namespace LightCondensed.Solid

/-- The actual protected reflector preserves K-projectivity.  This result
asserts no existence of replacements for general light condensed complexes. -/
theorem reflection_map_isKProjective
    (K : CochainComplex LightCondAb ℤ) [K.IsKProjective] :
    CochainComplex.IsKProjective
      ((isSolid.ι.leftAdjoint.mapHomologicalComplex (.up ℤ)).obj K) := by
  have : isSolid.ι.leftAdjoint.Additive :=
    (Adjunction.ofIsRightAdjoint isSolid.ι).left_adjoint_additive
  exact CWSolid.map_isKProjective_of_exact_rightAdjoint
    (Adjunction.ofIsRightAdjoint isSolid.ι) K

end LightCondensed.Solid
