/- GID: D5/S3/HomologicalAlgebra/Solid/FreeGeneratorAugmentation
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FreeGeneratorAugmentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FreeDetect
import D5.S3.HomologicalAlgebra.Solid.SolidTruncationTelescopes
import D5.S3.HomologicalAlgebra.Solid.AugmentedKernelResolution
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
An actual augmented resolution by coproducts of free light-profinite
objects. The evaluation is epimorphic by the proved free-generator
morphism detection; ambient projectivity is neither asserted nor needed.
Successive kernels give every negative cochain degree. This is the
concrete ambient resolution used in unbounded derived-local realization.
Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry,
Theorem 3.3.1. Kernel iteration reuses Mathlib's LeftResolution API,
copyright (c) 2025 Joël Riou, Apache-2.0, at Mathlib
5e0c4e5239cb0a2d86d68a884bf52cfd963fce22.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits HomologicalComplex LightCondensed

namespace LightCondensed.Solid

def freeGeneratorSource (s : SmallModel.{0} LightProfinite) : LightCondAb :=
  (free ℤ).obj ((equivSmallModel LightProfinite).inverse.obj s).toCondensed

abbrev FreeGeneratorMaps (X : LightCondAb) :=
  Σ s : SmallModel.{0} LightProfinite, freeGeneratorSource s ⟶ X

abbrev FreeGeneratorIndex (X : LightCondAb) :=
  Σ s : SmallModel.{0} LightProfinite, Shrink.{0} (freeGeneratorSource s ⟶ X)

def freeGeneratorDatum (X : LightCondAb) (a : FreeGeneratorIndex X) :
    freeGeneratorSource a.1 ⟶ X :=
  (equivShrink.{0} (freeGeneratorSource a.1 ⟶ X)).symm a.2

def freeGeneratorCopower (X : LightCondAb) : LightCondAb :=
  ∐ fun a : FreeGeneratorIndex X => freeGeneratorSource a.1

def freeGeneratorEvaluation (X : LightCondAb) : freeGeneratorCopower X ⟶ X :=
  Limits.Sigma.desc (freeGeneratorDatum X)

@[reassoc (attr := simp)]
theorem freeGeneratorEvaluation_leg (X : LightCondAb) (a : FreeGeneratorIndex X) :
    Sigma.ι (fun a : FreeGeneratorIndex X => freeGeneratorSource a.1) a ≫
      freeGeneratorEvaluation X = freeGeneratorDatum X a := by
  simp [freeGeneratorEvaluation]

instance freeGeneratorEvaluation_epi (X : LightCondAb) : Epi (freeGeneratorEvaluation X) := by
  apply Preadditive.epi_of_cancel_zero
  intro Y f hf
  apply hom_eq_zero_of_free
  intro S g
  let E : LightProfinite ≌ SmallModel.{0} LightProfinite := equivSmallModel LightProfinite
  let s := E.functor.obj S
  let e := (lightProfiniteToLightCondSet ⋙ free ℤ).mapIso (E.unitIso.app S).symm
  let a : FreeGeneratorIndex X :=
    ⟨s, equivShrink.{0} (freeGeneratorSource s ⟶ X) (e.hom ≫ g)⟩
  have he : e.hom ≫ (g ≫ f) = 0 := by
    have h := congrArg (Sigma.ι (fun a : FreeGeneratorIndex X =>
      freeGeneratorSource a.1) a ≫ ·) hf
    change Sigma.ι (fun a : FreeGeneratorIndex X => freeGeneratorSource a.1) a ≫
      (freeGeneratorEvaluation X ≫ f) = 0 at h
    rw [← Category.assoc, freeGeneratorEvaluation_leg] at h
    change (equivShrink.{0} (freeGeneratorSource s ⟶ X)).symm
      (equivShrink.{0} (freeGeneratorSource s ⟶ X) (e.hom ≫ g)) ≫ f = 0 at h
    rw [(equivShrink.{0} (freeGeneratorSource s ⟶ X)).symm_apply_apply] at h
    exact (Category.assoc _ _ _).symm.trans h
  exact (cancel_epi e.hom).1 (by simpa only [comp_zero] using he)

/-- Postcomposition acts on the small Hom index, preserving its free source. -/
def freeGeneratorCopowerFunctor : LightCondAb ⥤ LightCondAb where
  obj := freeGeneratorCopower
  map {X Y} f := Limits.Sigma.desc (fun a : FreeGeneratorIndex X =>
    Sigma.ι (fun a : FreeGeneratorIndex Y => freeGeneratorSource a.1)
      ⟨a.1, equivShrink.{0} (freeGeneratorSource a.1 ⟶ Y) (freeGeneratorDatum X a ≫ f)⟩)
  map_id X := by
    apply Sigma.hom_ext
    intro a
    simp [freeGeneratorDatum, Category.comp_id]
    rw [Category.comp_id, (equivShrink.{0} (freeGeneratorSource a.1 ⟶ X)).apply_symm_apply]
    exact (Category.comp_id _).symm
  map_comp f g := by
    apply Sigma.hom_ext
    intro a
    simp [freeGeneratorDatum, Category.assoc]
    rw [(equivShrink.{0} _).symm_apply_apply]
    rw [Category.assoc]

def freeGeneratorAugmentation : freeGeneratorCopowerFunctor ⟶ 𝟭 LightCondAb where
  app := freeGeneratorEvaluation
  naturality X Y f := by
    apply Sigma.hom_ext
    intro a
    simp [freeGeneratorCopowerFunctor, freeGeneratorEvaluation,
      freeGeneratorDatum, Category.assoc]

def freeGeneratorLeftResolution : Abelian.LeftResolution (𝟭 LightCondAb) where
  F := freeGeneratorCopowerFunctor
  π := freeGeneratorAugmentation
  epi_π_app X := freeGeneratorEvaluation_epi X

def freeGeneratorResolution (X : LightCondAb) : ChainComplex LightCondAb ℕ :=
  freeGeneratorLeftResolution.chainComplex X

theorem freeGeneratorResolution_term_copower (X : LightCondAb) (n : ℕ) :
    ∃ Y : LightCondAb, Nonempty ((freeGeneratorResolution X).X n ≅ freeGeneratorCopower Y) := by
  cases n with
  | zero => exact ⟨X, ⟨freeGeneratorLeftResolution.chainComplexXZeroIso X⟩⟩
  | succ n =>
    cases n with
    | zero => exact ⟨kernel (freeGeneratorEvaluation X),
        ⟨freeGeneratorLeftResolution.chainComplexXOneIso X⟩⟩
    | succ n => exact ⟨kernel ((freeGeneratorResolution X).d (n + 1) n),
        ⟨freeGeneratorLeftResolution.chainComplexXIso X n⟩⟩

theorem freeGeneratorResolution_exactAt_succ (X : LightCondAb) (n : ℕ) :
    (freeGeneratorResolution X).ExactAt (n + 1) :=
  freeGeneratorLeftResolution.exactAt_map_chainComplex_succ X n

def freeGeneratorResolutionπ (X : LightCondAb) :
    freeGeneratorResolution X ⟶ (ChainComplex.single₀ LightCondAb).obj X :=
  CWSolid.kernelResolutionπ freeGeneratorLeftResolution X

theorem freeGeneratorResolutionπ_quasiIso (X : LightCondAb) :
    QuasiIso (freeGeneratorResolutionπ X) :=
  CWSolid.kernelResolutionπ_quasiIso freeGeneratorLeftResolution X

/-- The actual nonprojective free resolution extends through all negative
integer degrees, with a genuine quasi-isomorphic augmentation. -/
def freeGeneratorCochainResolution (X : LightCondAb) : CochainComplex LightCondAb ℤ :=
  CWSolid.kernelResolutionCochain freeGeneratorLeftResolution X

def freeGeneratorCochainResolutionπ (X : LightCondAb) :
    freeGeneratorCochainResolution X ⟶ (CochainComplex.singleFunctor LightCondAb 0).obj X :=
  CWSolid.kernelResolutionCochainπ freeGeneratorLeftResolution X

instance freeGeneratorCochainResolution_strictlyLE (X : LightCondAb) :
    (freeGeneratorCochainResolution X).IsStrictlyLE 0 :=
  CWSolid.kernelResolutionCochain_strictlyLE freeGeneratorLeftResolution X

theorem freeGeneratorCochainResolutionπ_quasiIso (X : LightCondAb) :
    QuasiIso (freeGeneratorCochainResolutionπ X) :=
  CWSolid.kernelResolutionCochainπ_quasiIso freeGeneratorLeftResolution X

theorem freeGeneratorCochainResolution_negative_term (X : LightCondAb) (n : ℕ) :
    ∃ Y : LightCondAb, Nonempty ((freeGeneratorCochainResolution X).X (-(n : ℤ)) ≅
      freeGeneratorCopower Y) := by
  obtain ⟨Y, ⟨e⟩⟩ := freeGeneratorResolution_term_copower X n
  exact ⟨Y, ⟨HomologicalComplex.extendXIso _ _ (show -(n : ℤ) = -(n : ℤ) by rfl) ≪≫ e⟩⟩

end LightCondensed.Solid

#print axioms LightCondensed.Solid.freeGeneratorSource
#print axioms LightCondensed.Solid.FreeGeneratorMaps
#print axioms LightCondensed.Solid.FreeGeneratorIndex
#print axioms LightCondensed.Solid.freeGeneratorDatum
#print axioms LightCondensed.Solid.freeGeneratorCopower
#print axioms LightCondensed.Solid.freeGeneratorEvaluation
#print axioms LightCondensed.Solid.freeGeneratorEvaluation_leg
#print axioms LightCondensed.Solid.freeGeneratorEvaluation_epi
#print axioms LightCondensed.Solid.freeGeneratorCopowerFunctor
#print axioms LightCondensed.Solid.freeGeneratorAugmentation
#print axioms LightCondensed.Solid.freeGeneratorLeftResolution
#print axioms LightCondensed.Solid.freeGeneratorResolution
#print axioms LightCondensed.Solid.freeGeneratorResolution_term_copower
#print axioms LightCondensed.Solid.freeGeneratorResolution_exactAt_succ
#print axioms LightCondensed.Solid.freeGeneratorResolutionπ
#print axioms LightCondensed.Solid.freeGeneratorResolutionπ_quasiIso
#print axioms LightCondensed.Solid.freeGeneratorCochainResolution
#print axioms LightCondensed.Solid.freeGeneratorCochainResolutionπ
#print axioms LightCondensed.Solid.freeGeneratorCochainResolution_strictlyLE
#print axioms LightCondensed.Solid.freeGeneratorCochainResolutionπ_quasiIso
#print axioms LightCondensed.Solid.freeGeneratorCochainResolution_negative_term
