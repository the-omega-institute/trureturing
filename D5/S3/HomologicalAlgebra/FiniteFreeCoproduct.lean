/- GID: D5/S3/HomologicalAlgebra/FiniteFreeCoproduct
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FiniteFreeCoproduct
   mirror-E: none(waiver:finite-free-modules)
   anchors: []
   utility: none
   digest: Explicit finite basis coordinates for a coproduct of copies of Z. -/

import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! Finite coordinates obtained from Mathlib's actual Finsupp coproduct cocone. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open CategoryTheory Limits

namespace D5.S3.HomologicalAlgebra.FiniteFreeCoproduct

variable {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J] (e : I ≃ J)

/-- Reindex Mathlib's concrete coproduct and pass to finite function coordinates. -/
def coordinateIso : (∐ fun _ : J => ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℤ (I → ℤ) :=
  colimit.isoColimitCocone ⟨_, ModuleCat.finsuppCoconeIsColimit ℤ ℤ J⟩ ≪≫
    ((Finsupp.domLCongr e.symm : (J →₀ ℤ) ≃ₗ[ℤ] I →₀ ℤ).trans
      (Finsupp.linearEquivFunOnFinite ℤ ℤ I)).toModuleIso

@[reassoc (attr := simp)]
theorem ι_coordinateIso (j : J) :
    Sigma.ι (fun _ : J => ModuleCat.of ℤ ℤ) j ≫ (coordinateIso e).hom =
      ModuleCat.ofHom ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight
        (fun i => if e i = j then (1 : ℤ) else 0)) := by
  dsimp only [coordinateIso, Iso.trans_hom]
  rw [colimit.isoColimitCocone_ι_hom_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  ext i
  simp [ModuleCat.finsuppCocone, ModuleCat.hom_comp,
    LinearEquiv.toModuleIso, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.single_apply, eq_comm]
  by_cases h : i = e.symm j
  · subst i
    simp
  · have hj : j ≠ e i := by
      intro hj
      exact h (e.eq_symm_apply.mpr hj.symm)
    simp [h, hj]

@[simp]
theorem coordinateIso_basis (i : I) :
    (coordinateIso e).hom.hom ((Sigma.ι (fun _ : J => ModuleCat.of ℤ ℤ) (e i)).hom 1) =
      Pi.single i 1 := by
  change (Sigma.ι (fun _ : J => ModuleCat.of ℤ ℤ) (e i) ≫
    (coordinateIso e).hom).hom 1 = _
  rw [ι_coordinateIso]
  ext k
  simp [LinearMap.smulRight_apply, e.injective.eq_iff, Pi.single_apply, eq_comm]

end D5.S3.HomologicalAlgebra.FiniteFreeCoproduct
