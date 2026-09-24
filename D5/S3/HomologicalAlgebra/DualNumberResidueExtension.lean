/- GID: D5/S3/HomologicalAlgebra/DualNumberResidueExtension
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/DualNumberResidueExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences]
   utility: none
   digest: The rational dual-number residue sequence has a nonzero Ext-one class. -/

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/- Library-search audit (2026-09-23):
   * All repository refs were searched for `DualNumber`, `TrivSqZeroExt`,
     `ShortExact`, `extClass`, the nonzero extension conclusion, and its
     negation. No declaration of this concrete Ext class was found.
   * Pinned Mathlib provides the dual-number coordinates, `ModuleCat` short
     exactness, `ShortExact.extClass`, the contravariant long exact Ext
     sequence, and the Ext-zero/Hom equivalence. They are reused directly.
   * The Stacks Project tags 0A5Q, 065P, and 06XU provide respectively the
     dual-number residue resolution, the contravariant Hom/Ext sequence, and
     the Yoneda interpretation. The concrete nonvanishing proof below is a
     repository-derived synthesis; no source is claimed to state it verbatim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.HomologicalAlgebra.DualNumberResidueExtension

open CategoryTheory TrivSqZeroExt
open CategoryTheory.Abelian
open scoped DualNumber

private abbrev A := DualNumber ℚ

private noncomputable instance : Module A ℚ :=
  Module.compHom ℚ (fstHom ℚ ℚ ℚ).toRingHom

private noncomputable def epsilonInclusion : ℚ →ₗ[A] A where
  toFun := inr
  map_add' x y := inr_add ℚ x y
  map_smul' a q := by
    apply TrivSqZeroExt.ext
    · simp
    · change fst a * q = snd (a * inr q)
      simp [mul_comm]

private noncomputable def augmentation : A →ₗ[A] ℚ where
  toFun := fst
  map_add' := fst_add
  map_smul' a x := by
    change fst (a * x) = fst a * fst x
    simp

/-- The residue-module complex `ℚ --q ↦ qε--> ℚ[ε] --fst--> ℚ`. -/
noncomputable def dualNumberResidueComplex : ShortComplex (ModuleCat A) :=
  ShortComplex.moduleCatMk epsilonInclusion augmentation (by
    ext
    simp [epsilonInclusion, augmentation])

set_option maxHeartbeats 400000 in
-- Constructing Ext for ModuleCat needs the derived-category instance search.
set_option synthInstance.maxHeartbeats 200000 in
/-- The epsilon-ideal short exact sequence is a nonzero self-extension of the
residue module over the rational dual numbers. -/
theorem dual_number_residue_extension_nonzero :
    ∃ hS : dualNumberResidueComplex.ShortExact, hS.extClass ≠ 0 := by
  let hS : dualNumberResidueComplex.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · intro x
      constructor
      · intro hx
        refine ⟨snd x, ?_⟩
        change inr (snd x) = x
        apply TrivSqZeroExt.ext
        · change fst x = 0 at hx
          exact hx.symm
        · rfl
      · rintro ⟨q, rfl⟩
        rfl
    · intro x y h
      change inr x = inr y at h
      simpa using congrArg snd h
    · intro q
      exact ⟨inl q, rfl⟩
  refine ⟨hS, ?_⟩
  intro hzero
  have hcomp :
      hS.extClass.comp
          (Ext.mk₀ (𝟙 dualNumberResidueComplex.X₁))
          (show 1 + 0 = 1 by rfl) = 0 := by
    rw [hzero]
    simp
  obtain ⟨x₂, hx₂⟩ :=
    Ext.contravariant_sequence_exact₁ hS
      dualNumberResidueComplex.X₁
      (Ext.mk₀ (𝟙 dualNumberResidueComplex.X₁))
      (show 1 + 0 = 1 by rfl) hcomp
  let r : dualNumberResidueComplex.X₂ ⟶ dualNumberResidueComplex.X₁ :=
    Ext.addEquiv₀ x₂
  have hx₂mk : Ext.mk₀ r = x₂ := Ext.mk₀_addEquiv₀_apply x₂
  have hmk :
      Ext.mk₀ (dualNumberResidueComplex.f ≫ r) =
        Ext.mk₀ (𝟙 dualNumberResidueComplex.X₁) := by
    rw [← Ext.mk₀_comp_mk₀, hx₂mk]
    exact hx₂
  have hr : dualNumberResidueComplex.f ≫ r = 𝟙 dualNumberResidueComplex.X₁ :=
    (Ext.mk₀_bijective _ _).injective hmk
  let r' : A →ₗ[A] ℚ := r.hom
  let one₁ : dualNumberResidueComplex.X₁ := by
    change ℚ
    exact 1
  have hretract : r' (DualNumber.eps : A) = (1 : ℚ) := by
    have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hr) one₁
    change r' (inr (1 : ℚ)) = (1 : ℚ) at h
    exact h
  have hlinear : r' (DualNumber.eps : A) = 0 := by
    have h := r'.map_smul (DualNumber.eps : A) (1 : A)
    change r' ((DualNumber.eps : A) * 1) =
      fst (DualNumber.eps : A) * r' 1 at h
    simpa using h
  exact (one_ne_zero : (1 : ℚ) ≠ 0) (hretract.symm.trans hlinear)

#print axioms dual_number_residue_extension_nonzero

end D5.S3.HomologicalAlgebra.DualNumberResidueExtension
