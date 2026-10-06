/- GID: D5/S3/HomologicalAlgebra/Solid/LocalizationCoproduct
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/LocalizationCoproduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Preadditive
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Coproduct preservation for a localization with a right calculus of
fractions. This is the specific missing sum argument needed for the actual
unbounded cellular telescope. New proofs, released under Apache 2.0. -/

noncomputable section
open CategoryTheory Limits

namespace CWSolid

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D]
  (L : C ⥤ D) [L.Additive] (W : MorphismProperty C) [L.IsLocalization W]
  [W.HasRightCalculusOfFractions]
  {I : Type} [HasColimitsOfShape (Discrete I) C]
  [W.IsStableUnderCoproductsOfShape I]

include W

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing on every summand detects zero after localization, including
all roofs. The proof refines the denominators separately and then sums
the actual weak equivalences. -/
theorem localization_coproduct_hom_zero (X : I → C) (Y : C)
    (g : L.obj (∐ X) ⟶ L.obj Y)
    (hg : ∀ i, L.map (Sigma.ι X i) ≫ g = 0) : g = 0 := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L W g
  let ψ (i : I) : W.RightFraction (X i) φ.X' :=
    (MorphismProperty.LeftFraction.mk (Sigma.ι X i) φ.s φ.hs).rightFraction
  have hψ (i : I) : (ψ i).s ≫ Sigma.ι X i = (ψ i).f ≫ φ.s :=
    MorphismProperty.LeftFraction.rightFraction_fac _
  have hz (i : I) : L.map ((ψ i).f ≫ φ.f) = L.map (0 : (ψ i).X' ⟶ Y) := by
    rw [L.map_comp, L.map_zero, ← φ.map_s_comp_map L (Localization.inverts L W),
      ← hφ, ← Category.assoc, ← L.map_comp, ← hψ, L.map_comp, Category.assoc,
      hg, comp_zero]
  choose Z t ht he using fun i => (MorphismProperty.map_eq_iff_precomp L W _ _).1 (hz i)
  let s i := t i ≫ (ψ i).s
  let a : (∐ Z) ⟶ φ.X' := Sigma.desc (fun i => t i ≫ (ψ i).f)
  let b : (∐ Z) ⟶ ∐ X := Limits.Sigma.map s
  have hb : W b := W.colimMap
    (Discrete.natTrans (F := Discrete.functor Z) (G := Discrete.functor X) (fun j => s j.as))
    (fun j => W.comp_mem _ _ (ht j.as) (ψ j.as).hs)
  haveI : IsIso (L.map b) := Localization.inverts L W b hb
  have hab : a ≫ φ.s = b := by
    apply Sigma.hom_ext
    intro i
    simp only [a, b, Sigma.ι_desc_assoc, Sigma.ι_map, s, Category.assoc, ← hψ]
  have haf : a ≫ φ.f = 0 := by
    apply Sigma.hom_ext
    intro i
    simpa only [a, Sigma.ι_desc_assoc, Category.assoc, comp_zero] using he i
  rw [← cancel_epi (L.map b), comp_zero, ← hab, L.map_comp, Category.assoc,
    hφ, φ.map_s_comp_map, ← L.map_comp, haf, L.map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The actual image of a coproduct cofan is colimiting after localization.
No restriction to finite families or bounded complexes is made. -/
def localizationCoproductIsColimit (X : I → C) :
    IsColimit (Cofan.mk (L.obj (∐ X)) (fun i => L.map (Sigma.ι X i))) := by
  haveI : L.EssSurj := Localization.essSurj L W
  have existsDesc (Y : D) (g : ∀ i, L.obj (X i) ⟶ Y) :
      ∃ d : L.obj (∐ X) ⟶ Y, ∀ i, L.map (Sigma.ι X i) ≫ d = g i := by
    let Y₀ := L.objPreimage Y
    let e := L.objObjPreimageIso Y
    choose φ hφ using fun i => Localization.exists_rightFraction L W (g i ≫ e.inv)
    let Z i := (φ i).X'
    let b : (∐ Z) ⟶ ∐ X := Limits.Sigma.map (fun i => (φ i).s)
    let a : (∐ Z) ⟶ Y₀ := Sigma.desc (fun i => (φ i).f)
    have hb : W b := W.colimMap
      (Discrete.natTrans (F := Discrete.functor Z) (G := Discrete.functor X)
        (fun j => (φ j.as).s))
      (fun j => (φ j.as).hs)
    haveI : IsIso (L.map b) := Localization.inverts L W b hb
    refine ⟨inv (L.map b) ≫ L.map a ≫ e.hom, fun i => ?_⟩
    have hleg : L.map (Sigma.ι X i) ≫ inv (L.map b) =
        inv (L.map (φ i).s) ≫ L.map (Sigma.ι Z i) := by
      rw [← cancel_epi (L.map (φ i).s)]
      simp only [IsIso.hom_inv_id_assoc, ← L.map_comp_assoc]
      have hbι : (φ i).s ≫ Sigma.ι X i = Sigma.ι Z i ≫ b :=
        (Sigma.ι_map (fun j => (φ j).s) i).symm
      rw [hbι, L.map_comp]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, ← Category.assoc, hleg]
    simp only [Category.assoc]
    rw [← L.map_comp_assoc, Sigma.ι_desc]
    rw [← Category.assoc]
    change (φ i).map L (Localization.inverts L W) ≫ e.hom = g i
    rw [← hφ]
    simp
  have homExt (Y : D) (f g : L.obj (∐ X) ⟶ Y)
      (h : ∀ i, L.map (Sigma.ι X i) ≫ f = L.map (Sigma.ι X i) ≫ g) : f = g := by
    let e := L.objObjPreimageIso Y
    have hz : (f - g) ≫ e.inv = 0 :=
      localization_coproduct_hom_zero L W X (L.objPreimage Y) _ (fun i => by
        simp only [← Category.assoc, Preadditive.comp_sub, h, sub_self, zero_comp])
    apply sub_eq_zero.mp
    rw [← cancel_mono e.inv, hz, zero_comp]
  exact Cofan.IsColimit.mk _
    (fun s => (existsDesc s.pt s.inj).choose)
    (fun s => (existsDesc s.pt s.inj).choose_spec)
    (fun s m hm => homExt s.pt m _ (fun i =>
      (hm i).trans ((existsDesc s.pt s.inj).choose_spec i).symm))

end CWSolid
