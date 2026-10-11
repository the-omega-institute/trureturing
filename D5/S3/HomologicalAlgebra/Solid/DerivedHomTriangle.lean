/- GID: D5/S3/HomologicalAlgebra/Solid/DerivedHomTriangle
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/DerivedHomTriangle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.CategoryTheory.Triangulated.Functor

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
The actual Hom diagram chase needed to extend the protected generator
comparison through finite complex filtrations. This proves a transfer
across a distinguished triangle; it assumes no derived adjunction,
unbounded resolution, or full faithfulness of the functor.
Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1.
The chase uses Mathlib's proved yoneda exactness at commit
5e0c4e5239cb0a2d86d68a884bf52cfd963fce22 (Joël Riou, Apache-2.0).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Pretriangulated

namespace CWSolid

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- A five-term Hom chase, with the comparison the literal functor map.
Only the four adjacent source Hom comparisons are used. -/
theorem mapHom_bijective_triangle_middle
    (G : C ⥤ D) [G.Additive] [G.CommShift ℤ] [G.IsTriangulated]
    (T : Triangle C) (hT : T ∈ distTriang C) (Y : C)
    (h₁ : Function.Bijective (fun f : T.obj₁ ⟶ Y => G.map f))
    (h₃ : Function.Bijective (fun f : T.obj₃ ⟶ Y => G.map f))
    (h₁plus : Function.Surjective (fun f : T.obj₁⟦(1 : ℤ)⟧ ⟶ Y => G.map f))
    (h₃minus : Function.Injective (fun f : T.invRotate.obj₁ ⟶ Y => G.map f)) :
    Function.Bijective (fun f : T.obj₂ ⟶ Y => G.map f) := by
  let S := G.mapTriangle.obj T
  have hS : S ∈ distTriang D := G.map_distinguished T hT
  have hz {f : T.obj₂ ⟶ Y} (hf : G.map f = 0) : f = 0 := by
    have ha : T.mor₁ ≫ f = 0 := h₁.injective (by
      rw [G.map_comp, hf, comp_zero, G.map_zero])
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT f ha
    have hb : S.mor₂ ≫ G.map g = 0 := by
      change G.map T.mor₂ ≫ G.map g = 0
      rw [← G.map_comp, ← hg, hf]
    obtain ⟨a, ha⟩ := S.yoneda_exact₃ hS (G.map g) hb
    obtain ⟨b, hb⟩ := h₁plus
      ((G.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ a)
    change G.map b = (G.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ a at hb
    have hg' : g = T.mor₃ ≫ b := h₃.injective (by
      change G.map g = G.map (T.mor₃ ≫ b)
      rw [G.map_comp, hb]
      simpa only [S, Functor.mapTriangle, Triangle.mk, Category.assoc] using ha)
    rw [hg, hg', ← Category.assoc, comp_distTriang_mor_zero₂₃ _ hT, zero_comp]
  constructor
  · intro f g hfg
    change G.map f = G.map g at hfg
    have h : G.map (f - g) = 0 := by rw [G.map_sub, hfg, sub_self]
    exact sub_eq_zero.mp (hz h)
  · intro f
    obtain ⟨a, ha⟩ := h₁.surjective (G.map T.mor₁ ≫ f)
    change G.map a = G.map T.mor₁ ≫ f at ha
    let R := G.mapTriangle.obj T.invRotate
    have hR : R ∈ distTriang D :=
      G.map_distinguished T.invRotate (inv_rot_of_distTriang T hT)
    have hz' : T.invRotate.mor₁ ≫ a = 0 := h₃minus (by
      change G.map (T.invRotate.mor₁ ≫ a) = G.map 0
      rw [G.map_comp, ha]
      change R.mor₁ ≫ R.mor₂ ≫ f = G.map 0
      rw [← Category.assoc, comp_distTriang_mor_zero₁₂ _ hR, zero_comp, G.map_zero])
    obtain ⟨b, hb⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) a hz'
    change T.obj₂ ⟶ Y at b
    change a = T.mor₁ ≫ b at hb
    have hbf : S.mor₁ ≫ (f - G.map b) = 0 := by
      change G.map T.mor₁ ≫ (f - G.map b) = 0
      rw [Preadditive.comp_sub, ← G.map_comp, ← hb, ha, sub_self]
    obtain ⟨c, hc⟩ := S.yoneda_exact₂ hS (f - G.map b) hbf
    change G.obj T.obj₃ ⟶ G.obj Y at c
    change f - G.map b = G.map T.mor₂ ≫ c at hc
    obtain ⟨d, hd⟩ := h₃.surjective c
    change G.map d = c at hd
    refine ⟨b + T.mor₂ ≫ d, ?_⟩
    change G.map (b + T.mor₂ ≫ d) = f
    rw [G.map_add, G.map_comp, hd]
    rw [← hc, add_sub_cancel]

end CWSolid

#print axioms CWSolid.mapHom_bijective_triangle_middle
