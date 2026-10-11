/- GID: D5/S3/HomologicalAlgebra/Solid/CellularTelescope
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/CellularTelescope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DerivedCellAttachment
import D5.S3.HomologicalAlgebra.Solid.DerivedCoproduct

/-! The actual mapping telescope of the saved unbounded cellular sequence.
Its derived universal comparison is proved against all derived-local targets.
A quasi-isomorphism to the ordinary cellular colimit and realization in
D(Solid) remain separate obligations. New proofs, Apache 2.0. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits HomologicalComplex Pretriangulated

namespace LightCondensed.Solid

local instance cellularCountableCoproducts :
    HasColimitsOfShape (Discrete ℕ) (CochainComplex LightCondAb ℤ) where
  has_colimit F := by
    haveI : HasColimitsOfShape (Discrete ℕ) LightCondAb := solidification_hasSmallCoproducts ℕ
    haveI (n : ℤ) : HasColimit (F ⋙ eval LightCondAb (.up ℤ) n) := inferInstance
    exact ⟨⟨⟨HomologicalComplex.coconeOfHasColimitEval F,
      HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩

/-- The concrete one-minus-transition map on the sum of the saved stages. -/
def solidCellularTelescopeDifferential (K : CochainComplex LightCondAb ℤ) :
    (∐ solidCellularStage K) ⟶ ∐ solidCellularStage K :=
  𝟙 _ - Limits.Sigma.desc (fun n => solidCellularStepι (solidCellularStage K n) ≫
    Sigma.ι (solidCellularStage K) (n + 1))

/-- The actual mapping-cone telescope, starting at an arbitrary unbounded K. -/
def solidCellularTelescope (K : CochainComplex LightCondAb ℤ) :
    CochainComplex LightCondAb ℤ :=
  CochainComplex.mappingCone (solidCellularTelescopeDifferential K)

/-- The original input maps to stage zero of the actual telescope. -/
def solidCellularTelescopeι (K : CochainComplex LightCondAb ℤ) :
    K ⟶ solidCellularTelescope K :=
  Sigma.ι (solidCellularStage K) 0 ≫
    CochainComplex.mappingCone.inr (solidCellularTelescopeDifferential K)

private theorem telescopeDifferential_leg (K : CochainComplex LightCondAb ℤ) (n : ℕ) :
    Sigma.ι (solidCellularStage K) n ≫ solidCellularTelescopeDifferential K =
      Sigma.ι (solidCellularStage K) n -
        solidCellularStepι (solidCellularStage K n) ≫ Sigma.ι (solidCellularStage K) (n + 1) := by
  simp [solidCellularTelescopeDifferential, Preadditive.comp_sub]

private theorem derivedTelescopeDifferential_leg (K : CochainComplex LightCondAb ℤ) (n : ℕ) :
    DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫
        DerivedCategory.Q.map (solidCellularTelescopeDifferential K) =
      DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) -
        DerivedCategory.Q.map (solidCellularStepι (solidCellularStage K n)) ≫
          DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) (n + 1)) := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_sub] using
    congrArg DerivedCategory.Q.map (telescopeDifferential_leg K n)

private def cellularDerivedSumIsColimit (K : CochainComplex LightCondAb ℤ) :
    IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ solidCellularStage K))
      (fun n => DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n))) := by
  have := lightCondensedDerivedQ_preservesCoproduct (solidCellularStage K)
  exact isColimitOfHasCoproductOfPreservesColimit DerivedCategory.Q (solidCellularStage K)

private def cellularRecursiveFamily (K : CochainComplex LightCondAb ℤ)
    (Y : DLightCondAb) [IsIso (solidDerivedEndomorphism.app Y)]
    (g₀ : DerivedCategory.Q.obj K ⟶ Y)
    (v : ∀ n, DerivedCategory.Q.obj (solidCellularStage K n) ⟶ Y) :
    ∀ n, DerivedCategory.Q.obj (solidCellularStage K n) ⟶ Y
  | 0 => g₀
  | n + 1 => (Equiv.ofBijective _
      (solidCellularStep_derivedPrecomp_bijective (solidCellularStage K n) Y)).symm
        (cellularRecursiveFamily K Y g₀ v n - v n)

private theorem cellularRecursiveFamily_step (K : CochainComplex LightCondAb ℤ)
    (Y : DLightCondAb) [IsIso (solidDerivedEndomorphism.app Y)]
    (g₀ : DerivedCategory.Q.obj K ⟶ Y)
    (v : ∀ n, DerivedCategory.Q.obj (solidCellularStage K n) ⟶ Y) (n : ℕ) :
    DerivedCategory.Q.map (solidCellularStepι (solidCellularStage K n)) ≫
        cellularRecursiveFamily K Y g₀ v (n + 1) =
      cellularRecursiveFamily K Y g₀ v n - v n :=
  (Equiv.ofBijective _
    (solidCellularStep_derivedPrecomp_bijective (solidCellularStage K n) Y)).apply_symm_apply _

private theorem telescopeDifferential_precomp_surjective
    (K : CochainComplex LightCondAb ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Surjective (fun (g : DerivedCategory.Q.obj (∐ solidCellularStage K) ⟶ Y) =>
      DerivedCategory.Q.map (solidCellularTelescopeDifferential K) ≫ g) := by
  intro u
  let t := cellularRecursiveFamily K Y 0
    (fun n => DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ u)
  let H := cellularDerivedSumIsColimit K
  let g := H.desc (Cofan.mk Y t)
  have hg n : DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ g = t n :=
    H.fac _ ⟨n⟩
  have hr n : DerivedCategory.Q.map (solidCellularStepι (solidCellularStage K n)) ≫
      t (n + 1) = t n - DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ u :=
    cellularRecursiveFamily_step K Y 0
      (fun n => DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ u) n
  refine ⟨g, H.hom_ext (fun ⟨n⟩ => ?_)⟩
  change DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫
      DerivedCategory.Q.map (solidCellularTelescopeDifferential K) ≫ g =
    DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ u
  rw [← Category.assoc, derivedTelescopeDifferential_leg, Preadditive.sub_comp,
    Category.assoc, hg, hg, hr]
  exact sub_sub_cancel _ _

set_option backward.isDefEq.respectTransparency false in
/-- The saved sequence's actual mapping telescope has a universal derived
comparison to every derived-local object: existence and uniqueness hold
for all roofs and for arbitrary unbounded starting complexes. -/
theorem solidCellularTelescope_derivedPrecomp_bijective
    (K : CochainComplex LightCondAb ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : DerivedCategory.Q.obj (solidCellularTelescope K) ⟶ Y) =>
      DerivedCategory.Q.map (solidCellularTelescopeι K) ≫ g) := by
  let d := solidCellularTelescopeDifferential K
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle d)
  have hT := DerivedCategory.mappingCone_triangle_distinguished d
  let H := cellularDerivedSumIsColimit K
  haveI : IsIso ((MonoidalClosed.pre oneMinusShift).mapDerivedCategory.app Y) :=
    (inferInstance : IsIso (solidDerivedEndomorphism.app Y))
  have : IsIso (solidDerivedEndomorphism.app (Y⟦(-1 : ℤ)⟧)) := by
    unfold solidDerivedEndomorphism
    rw [NatTrans.app_shift _ (-1 : ℤ) Y]
    infer_instance
  have hshift : Function.Surjective
      (fun (g : T.obj₂⟦(1 : ℤ)⟧ ⟶ Y) => T.mor₁⟦(1 : ℤ)⟧' ≫ g) := by
    intro u
    let e := (shiftEquiv DLightCondAb (1 : ℤ)).toAdjunction.homEquiv T.obj₁ Y
    obtain ⟨v, hv⟩ := telescopeDifferential_precomp_surjective K (Y⟦(-1 : ℤ)⟧) (e u)
    refine ⟨e.symm v, e.injective ?_⟩
    have he : e (T.mor₁⟦(1 : ℤ)⟧' ≫ e.symm v) = T.mor₁ ≫ e (e.symm v) :=
      (shiftEquiv DLightCondAb (1 : ℤ)).toAdjunction.homEquiv_naturality_left T.mor₁ (e.symm v)
    exact he.trans (by rw [e.apply_symm_apply]; exact hv)
  constructor
  · intro g h hgh
    let u := T.mor₂ ≫ (g - h)
    have hd : T.mor₁ ≫ u = 0 := by
      simp only [u, ← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]
    have hleg (n : ℕ) : DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ u = 0 := by
      induction n with
      | zero =>
          change DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) 0) ≫
            DerivedCategory.Q.map (CochainComplex.mappingCone.inr d) ≫ (g - h) = 0
          rw [← Category.assoc, ← DerivedCategory.Q.map_comp]
          change DerivedCategory.Q.map (solidCellularTelescopeι K) ≫ (g - h) = 0
          simp only [Preadditive.comp_sub, hgh, sub_self]
      | succ n ih =>
          apply (solidCellularStep_derivedPrecomp_bijective (solidCellularStage K n) Y).injective
          change DerivedCategory.Q.map (solidCellularStepι (solidCellularStage K n)) ≫
            (DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) (n + 1)) ≫ u) =
              DerivedCategory.Q.map (solidCellularStepι (solidCellularStage K n)) ≫ 0
          have hn := congrArg (DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ ·) hd
          change DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫
            DerivedCategory.Q.map d ≫ u = _ at hn
          rw [← Category.assoc, derivedTelescopeDifferential_leg, Preadditive.sub_comp,
            Category.assoc, ih, zero_sub, comp_zero] at hn
          simpa only [comp_zero] using neg_eq_zero.mp hn
    have hu : u = 0 := H.hom_ext (fun ⟨n⟩ => by
      change DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ u =
        DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ 0
      rw [hleg, comp_zero])
    obtain ⟨v, hv⟩ := T.yoneda_exact₃ hT (g - h) hu
    obtain ⟨w, hw⟩ := hshift v
    exact sub_eq_zero.mp (by
      rw [hv, ← hw, ← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp])
  · intro g₀
    let t := cellularRecursiveFamily K Y g₀ (fun _ => 0)
    let u := H.desc (Cofan.mk Y t)
    have hu n : DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ u = t n :=
      H.fac _ ⟨n⟩
    have ht n : DerivedCategory.Q.map (solidCellularStepι (solidCellularStage K n)) ≫
        t (n + 1) = t n := by
      simpa only [sub_zero] using cellularRecursiveFamily_step K Y g₀ (fun _ => 0) n
    have hd : T.mor₁ ≫ u = 0 := H.hom_ext (fun ⟨n⟩ => by
      change DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫
        DerivedCategory.Q.map d ≫ u =
          DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) n) ≫ 0
      rw [← Category.assoc, derivedTelescopeDifferential_leg, Preadditive.sub_comp,
        Category.assoc, hu, hu, ht, sub_self, comp_zero])
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT u hd
    refine ⟨g, ?_⟩
    change DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) 0 ≫
      CochainComplex.mappingCone.inr d) ≫ g = g₀
    rw [DerivedCategory.Q.map_comp, Category.assoc]
    change DerivedCategory.Q.map (Sigma.ι (solidCellularStage K) 0) ≫ T.mor₂ ≫ g = g₀
    rw [← hg, hu]
    rfl

end LightCondensed.Solid
