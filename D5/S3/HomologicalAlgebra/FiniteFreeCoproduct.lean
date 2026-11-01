/- GID: D5/S3/HomologicalAlgebra/FiniteFreeCoproduct
   generality: G
   mirror-B: none(waiver:source-artifact-awaiting-canonical-validation)
   mirror-E: none(waiver:finite-free-modules)
   anchors: []
   utility: none
   digest: Explicit finite basis coordinates for a coproduct of copies of Z. -/

import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
open CategoryTheory Limits
open scoped BigOperators

namespace D5.S3.HomologicalAlgebra.FiniteFreeCoproduct

variable {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J] (e : I ≃ J)

private def column (j : J) : I → ℤ := fun i => if e i = j then 1 else 0

private theorem column_image (i : I) : column e (e i) = Pi.single i 1 := by
  ext k
  simp [column, e.injective.eq_iff, Pi.single_apply, eq_comm]

/-- A finite coproduct basis is sent to its actual integer coordinate vector. -/
def coordinateIso : (∐ fun _ : J => ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℤ (I → ℤ) where
  hom := Sigma.desc fun j => ModuleCat.ofHom (LinearMap.id.smulRight (column e j))
  inv := ModuleCat.ofHom (Fintype.linearCombination ℤ
    (fun i => (Sigma.ι (fun _ : J => ModuleCat.of ℤ ℤ) (e i)) 1))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    rw [Sigma.ι_comp_desc_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change Fintype.linearCombination ℤ _ (column e (e i)) = _
    rw [column_image, Fintype.linearCombination_apply_single, one_smul]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change (Sigma.desc fun j => ModuleCat.ofHom (LinearMap.id.smulRight (column e j)))
      (∑ i, f i • (Sigma.ι (fun _ : J => ModuleCat.of ℤ ℤ) (e i)) 1) = f
    simp only [map_sum, map_smul]
    have hcol (i : I) :
        (Sigma.desc fun j => ModuleCat.ofHom (LinearMap.id.smulRight (column e j)))
          ((Sigma.ι (fun _ : J => ModuleCat.of ℤ ℤ) (e i)) 1) = Pi.single i 1 := by
      have h := congrArg (fun f => f (1 : ℤ))
        (Sigma.ι_comp_desc (fun j => ModuleCat.ofHom (LinearMap.id.smulRight (column e j))) (e i))
      simpa only [ModuleCat.comp_apply, ModuleCat.ofHom_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply, one_smul, column_image] using h
    simp only [hcol]
    ext i
    simp [Pi.single_apply]

@[reassoc (attr := simp)]
theorem ι_coordinateIso (j : J) :
    Sigma.ι (fun _ : J => ModuleCat.of ℤ ℤ) j ≫ (coordinateIso e).hom =
      ModuleCat.ofHom (LinearMap.id.smulRight (fun i => if e i = j then 1 else 0)) :=
  Sigma.ι_comp_desc _ _

@[simp]
theorem coordinateIso_basis (i : I) :
    (coordinateIso e).hom ((Sigma.ι (fun _ : J => ModuleCat.of ℤ ℤ) (e i)) 1) =
      Pi.single i 1 := by
  have h := congrArg (fun f => f (1 : ℤ)) (ι_coordinateIso e (e i))
  have h' : (coordinateIso e).hom
      ((Sigma.ι (fun _ : J => ModuleCat.of ℤ ℤ) (e i)) 1) = column e (e i) := by
    simpa only [ModuleCat.comp_apply, ModuleCat.ofHom_apply, LinearMap.smulRight_apply,
      LinearMap.id_apply, one_smul] using h
  exact h'.trans (column_image e i)

end D5.S3.HomologicalAlgebra.FiniteFreeCoproduct
