/- GID: D5/S3/HomologicalAlgebra/Solid/DerivedGeneratorSums
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/DerivedGeneratorSums
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DerivedGeneratorComparison
import D5.S3.HomologicalAlgebra.Solid.SolidTruncationTelescopes

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
Full faithfulness of the exact protected derived inclusion on arbitrary
small sums of the concrete generator, in every integer degree and against
arbitrary unbounded solid targets. The sums are actual colimits, and the
comparison is the literal derivedInclusion.map. No all-source full
faithfulness, realization, or derived adjunction is assumed.
Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits LightCondensed

namespace LightCondensed.Solid

private theorem map_bijective_from_colimit
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    (G : C ⥤ D) {F : J ⥤ C} (c : Cocone F)
    (hc : IsColimit c) (hGc : IsColimit (G.mapCocone c)) (Y : C)
    (h : ∀ j, Function.Bijective (fun f : F.obj j ⟶ Y => G.map f)) :
    Function.Bijective (fun f : c.pt ⟶ Y => G.map f) := by
  constructor
  · intro f g hfg
    change G.map f = G.map g at hfg
    apply hc.hom_ext
    intro j
    apply (h j).injective
    simpa only [Functor.map_comp] using congrArg (G.map (c.ι.app j) ≫ ·) hfg
  · intro f
    let a j := ((h j).surjective (G.map (c.ι.app j) ≫ f)).choose
    have ha j : G.map (a j) = G.map (c.ι.app j) ≫ f :=
      ((h j).surjective (G.map (c.ι.app j) ≫ f)).choose_spec
    let d : Cocone F :=
      { pt := Y
        ι :=
          { app := a
            naturality j k u := by
              dsimp
              rw [Category.comp_id]
              apply (h j).injective
              change G.map (F.map u ≫ a k) = G.map (a j)
              rw [G.map_comp, ha, ha, ← G.map_comp_assoc, c.w u] } }
    refine ⟨hc.desc d, hGc.hom_ext (fun j => ?_)⟩
    change G.map (c.ι.app j) ≫ G.map (hc.desc d) = G.map (c.ι.app j) ≫ f
    rw [← G.map_comp, hc.fac d j]
    exact ha j

private theorem solidSingle_preservesCoproduct {I : Type}
    (A : I → Solid) (n : ℤ) :
    PreservesColimit (Discrete.functor A) (DerivedCategory.singleFunctor Solid n) := by
  let S := CochainComplex.singleFunctor Solid n
  let K i := S.obj (A i)
  haveI : PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := Solid)) :=
    CWSolid.derivedQ_preservesCoproduct K
  haveI : PreservesColimit (Discrete.functor A ⋙ S) (DerivedCategory.Q (C := Solid)) :=
    preservesColimit_of_iso_diagram _ (Discrete.natIso (F := Discrete.functor K) (G := Discrete.functor A ⋙ S)
      (fun j => Iso.refl (S.obj (A j.as))))
  haveI : PreservesColimit (Discrete.functor A) S := by
    dsimp [S, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    infer_instance
  change PreservesColimit (Discrete.functor A) (S ⋙ DerivedCategory.Q)
  infer_instance

private theorem ambientSingle_preservesCoproduct {I : Type}
    (A : I → LightCondAb) (n : ℤ) :
    PreservesColimit (Discrete.functor A) (DerivedCategory.singleFunctor LightCondAb n) := by
  let S := CochainComplex.singleFunctor LightCondAb n
  let K i := S.obj (A i)
  haveI : PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := LightCondAb)) :=
    lightCondensedDerivedQ_preservesCoproduct K
  haveI : PreservesColimit (Discrete.functor A ⋙ S) (DerivedCategory.Q (C := LightCondAb)) :=
    preservesColimit_of_iso_diagram _ (Discrete.natIso (F := Discrete.functor K) (G := Discrete.functor A ⋙ S)
      (fun j => Iso.refl (S.obj (A j.as))))
  haveI : PreservesColimit (Discrete.functor A) S := by
    dsimp [S, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    infer_instance
  change PreservesColimit (Discrete.functor A) (S ⋙ DerivedCategory.Q)
  infer_instance

/-- This is the actual map on derived morphisms from any generator
copower, for every integer n and every arbitrary unbounded target. -/
theorem derivedInclusion_generatorCopower_map_bijective
    (I : Type) (n : ℤ) (Y : DSolid) :
    Function.Bijective (fun f :
      (DerivedCategory.singleFunctor Solid n).obj
        (∐ fun _ : I => solidification.obj P) ⟶ Y => derivedInclusion.map f) := by
  let A : I → Solid := fun _ => solidification.obj P
  let S := DerivedCategory.singleFunctor Solid n
  let T := DerivedCategory.singleFunctor LightCondAb n
  let c := Cofan.mk (∐ A) (Sigma.ι A)
  haveI : PreservesColimit (Discrete.functor A) S := solidSingle_preservesCoproduct A n
  let hc := isColimitOfPreserves S (coproductIsCoproduct A)
  haveI : PreservesColimit (Discrete.functor (fun i => isSolid.ι.obj (A i))) T :=
    ambientSingle_preservesCoproduct (fun i => isSolid.ι.obj (A i)) n
  haveI : PreservesColimit (Discrete.functor A ⋙ isSolid.ι) T :=
    preservesColimit_of_iso_diagram _
      (Discrete.natIso (F := Discrete.functor (fun i => isSolid.ι.obj (A i)))
        (G := Discrete.functor A ⋙ isSolid.ι)
        (fun j => Iso.refl (isSolid.ι.obj (A j.as))))
  haveI : PreservesColimit (Discrete.functor A) (isSolid.ι ⋙ T) := by infer_instance
  haveI : PreservesColimit (Discrete.functor A) (S ⋙ derivedInclusion) :=
    preservesColimit_of_natIso _ (isSolid.ι.mapDerivedCategorySingleFunctor n).symm
  let hGc := isColimitOfPreserves (S ⋙ derivedInclusion) (coproductIsCoproduct A)
  exact map_bijective_from_colimit derivedInclusion (S.mapCocone c) hc hGc Y
    (fun _ => derivedInclusion_solidP_map_bijective n Y)

end LightCondensed.Solid

#print axioms LightCondensed.Solid.derivedInclusion_generatorCopower_map_bijective
