/- GID: D5/S3/HomologicalAlgebra/Solid/FreeDetect
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FreeDetect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.Reflection

/-! Free light-profinite generators detect morphisms and exactness.
New proofs, released under the Apache 2.0 license. -/

noncomputable section
open CategoryTheory Limits

namespace LightCondensed.Solid

set_option backward.isDefEq.respectTransparency false in
theorem hom_eq_zero_of_free
    {X Y : LightCondAb} (f : X ⟶ Y)
    (h : ∀ (S : LightProfinite) (g : (free ℤ).obj S.toCondensed ⟶ X), g ≫ f = 0) :
    f = 0 := by
  apply LightCondensed.hom_ext
  intro S
  ext x
  let e := LightSolidFilteredScaffold.hom_free_lightProfinite_iso_points S.unop
  let g := (e.inv.app X) (ULift.up x)
  have hg : (e.hom.app X) g = ULift.up x := by
    exact types_congr_hom (e.inv_hom_id_app X) (ULift.up x)
  have h₁ := ConcreteCategory.congr_hom (e.hom.naturality f) g
  have h₂ := ConcreteCategory.congr_hom (e.hom.naturality (0 : X ⟶ Y)) g
  have hgf : g ≫ f = g ≫ (0 : X ⟶ Y) := by simpa using h S.unop g
  have he : (e.hom.app Y) (g ≫ f) = (e.hom.app Y) (g ≫ (0 : X ⟶ Y)) :=
    congrArg (e.hom.app Y) hgf
  change (e.hom.app Y) (g ≫ f) =
    ULift.up ((f.hom.app S) ((e.hom.app X) g).down) at h₁
  change (e.hom.app Y) (g ≫ (0 : X ⟶ Y)) =
    ULift.up (((0 : X ⟶ Y).hom.app S) ((e.hom.app X) g).down) at h₂
  rw [hg] at h₁ h₂
  have := congrArg ULift.down (h₁.symm.trans (he.trans h₂))
  simpa using this

set_option backward.isDefEq.respectTransparency false in
theorem exact_of_free_boundaries (S : ShortComplex LightCondAb)
    (h : ∀ (T : LightProfinite) (g : (free ℤ).obj T.toCondensed ⟶ S.X₂),
      g ≫ S.g = 0 → ∃ a : (free ℤ).obj T.toCondensed ⟶ S.X₁, a ≫ S.f = g) :
    S.Exact := by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  apply hom_eq_zero_of_free
  intro T g
  obtain ⟨a, ha⟩ := h T (g ≫ kernel.ι S.g) (by simp)
  rw [← Category.assoc, ← ha]
  simp

end LightCondensed.Solid
