/- GID: D5/S3/HomologicalAlgebra/Solid/FreeFlat
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FreeFlat
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.Colimits
import D5.S3.HomologicalAlgebra.Solid.DerivedAdjunction

/-!
Tensor exactness for the concrete cells used in solidification.  The proof
uses flat free modules in presheaves and left exact sheafification; it does
not assume enough projectives in light condensed abelian groups.
-/

noncomputable section
open CategoryTheory Limits MonoidalCategory MonoidalClosed LightProfinite OnePoint

namespace LightCondensed.Solid

set_option backward.isDefEq.respectTransparency false in
/-- Free light condensed abelian groups are flat, including free groups on
arbitrary light condensed sets. -/
theorem tensorFree_preservesFiniteLimits (X : LightCondSet) :
    PreservesFiniteLimits (tensorLeft ((free ℤ).obj X)) := by
  let Q : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := X.obj ⋙ ModuleCat.free ℤ
  have hQ : PreservesFiniteLimits (tensorLeft Q) := by
    constructor
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation
    intro S
    let e : tensorLeft Q ⋙ (evaluation _ _).obj S ≅
        (evaluation _ _).obj S ⋙ tensorLeft (Q.obj S) := Iso.refl _
    have : PreservesFiniteLimits (tensorLeft (Q.obj S)) := by
      dsimp [Q]
      infer_instance
    exact preservesLimitsOfShape_of_natIso e.symm
  let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  let R := sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  let adj := sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)
  let e : tensorLeft ((free ℤ).obj X) ≅ R ⋙ tensorLeft Q ⋙ L :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.counit).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R (Functor.Monoidal.commTensorLeft L Q) ≪≫
      (Functor.associator _ _ _).symm
  exact preservesFiniteLimits_of_natIso e.symm

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring with the protected `P` is exact.  This is a tensor-flatness
statement, separate from the protected internal-projectivity instance. -/
theorem tensorP_preservesFiniteLimits : PreservesFiniteLimits (tensorLeft P) := by
  have : PreservesFiniteLimits
      (tensorLeft ((free ℤ).obj (ℕ∪{∞}).toCondensed)) :=
    tensorFree_preservesFiniteLimits _
  have : (tensorLeft P).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.ofRetract (P_retract.map (tensoringLeft LightCondAb))
  have : PreservesBinaryBiproducts (tensorLeft P) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (tensorLeft P).Additive := Functor.additive_of_preservesBinaryBiproducts _
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have : Mono S.f := hS.mono_f
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (tensorLeft P)).1 inferInstance S hS).1, inferInstance⟩

attribute [instance] tensorP_preservesFiniteLimits

instance tensorP_additive : (tensorLeft P).Additive := by
  have : PreservesBinaryBiproducts (tensorLeft P) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The tensor/internal-Hom adjunction for the actual protected `P`
descends to the whole unbounded derived category, since both functors are
exact.  This supplies the adjunction for the proposed localization cells. -/
def derivedTensorPAdjunction :
    (tensorLeft P).mapDerivedCategory ⊣ (ihom P).mapDerivedCategory := by
  letI : CatCommSq ((tensorLeft P).mapHomotopyCategory (.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh (tensorLeft P).mapDerivedCategory :=
    ⟨(tensorLeft P).mapDerivedCategoryFactorsh.symm⟩
  letI : CatCommSq ((ihom P).mapHomotopyCategory (.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh (ihom P).mapDerivedCategory :=
    ⟨(ihom P).mapDerivedCategoryFactorsh.symm⟩
  exact (CWSolid.mapHomotopyCategoryAdjunction (ihom.adjunction P)).localization
    DerivedCategory.Qh (HomotopyCategory.quasiIso LightCondAb (.up ℤ))
    DerivedCategory.Qh (HomotopyCategory.quasiIso LightCondAb (.up ℤ))
    (tensorLeft P).mapDerivedCategory (ihom P).mapDerivedCategory

end LightCondensed.Solid
