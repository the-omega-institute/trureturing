/- GID: D5/S3/HomologicalAlgebra/DetectedOrderTwoHomology
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/DetectedOrderTwoHomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Homology.ShortComplex.ModuleCat]
   utility: none
   digest: A detected integral cycle whose double bounds gives an order-two class in ModuleCat homology. -/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.ZMod.Basic

/-!
The quotient used here is Mathlib's explicit left homology data, transported
through `ShortComplex.moduleCatHomologyIso` to `ShortComplex.homology` itself.
The finite independence-complex seed consumes this construction.

The declarations are general module-homology constructions, not finite
enumerations or numerical certificates; computational utility kind is none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.HomologicalAlgebra.DetectedOrderTwoHomology

open CategoryTheory

-- Keep the kernel module structure carried by Mathlib's quotient map.
attribute [local instance 2000] Submodule.module

universe u

/-- The actual homology class map on the concrete kernel of the outgoing map. -/
noncomputable def cycleClassMap (S : ShortComplex (ModuleCat.{u} ℤ)) :
    LinearMap.ker S.g.hom →ₗ[ℤ] S.homology :=
  S.moduleCatHomologyIso.symm.toLinearEquiv.toLinearMap.comp
    (LinearMap.range S.moduleCatToCycles).mkQ

/-- A concrete cycle has zero class in categorical homology precisely when it bounds. -/
theorem cycleClassMap_eq_zero_iff (S : ShortComplex (ModuleCat.{u} ℤ))
    (z : LinearMap.ker S.g.hom) :
    cycleClassMap S z = 0 ↔ ∃ c : S.X₁, S.f c = (z : S.X₂) := by
  change S.moduleCatHomologyIso.symm.toLinearEquiv
    ((LinearMap.range S.moduleCatToCycles).mkQ z) = 0 ↔ _
  erw [S.moduleCatHomologyIso.symm.toLinearEquiv.map_eq_zero_iff]
  erw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc⟩

/-- If a mod-two linear functional kills boundaries and detects a cycle whose
double bounds, the displayed class in `S.homology` is nonzero and killed by two. -/
theorem detected_order_two (S : ShortComplex (ModuleCat.{u} ℤ))
    (z : LinearMap.ker S.g.hom) (c : S.X₁)
    (hc : S.f c = (2 : ℕ) • (z : S.X₂))
    (φ : S.X₂ →ₗ[ℤ] ZMod 2)
    (hφ : ∀ b : S.X₁, φ (S.f b) = 0)
    (hz : φ (z : S.X₂) ≠ 0) :
    cycleClassMap S z ≠ 0 ∧ (2 : ℕ) • cycleClassMap S z = 0 := by
  constructor
  · intro hzero
    obtain ⟨b, hb⟩ := (cycleClassMap_eq_zero_iff S z).mp hzero
    apply hz
    rw [← hb]
    exact hφ b
  · rw [← map_nsmul]
    apply (cycleClassMap_eq_zero_iff S ((2 : ℕ) • z)).mpr
    exact ⟨c, hc⟩

end D5.S3.HomologicalAlgebra.DetectedOrderTwoHomology
