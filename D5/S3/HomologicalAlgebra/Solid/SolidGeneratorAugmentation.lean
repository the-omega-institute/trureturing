/- GID: D5/S3/HomologicalAlgebra/Solid/SolidGeneratorAugmentation
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/SolidGeneratorAugmentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.GeneratorConstruction
import D5.S3.HomologicalAlgebra.Solid.DerivedGeneratorComparison
import D5.S3.HomologicalAlgebra.Solid.SolidTruncationTelescopes
import D5.S3.HomologicalAlgebra.Solid.AugmentedKernelResolution
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Extend

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
The concrete generator augmentation used in unbounded realization: sums of
the exact protected solidification(P) map epimorphically onto every solid
object, and iteration on kernels produces an actual exact augmented
resolution. This does not assume EnoughProjectives of LightCondAb, a
derived adjunction, derived full faithfulness, or unbounded realization.
Ambient P projectivity is reused from the immutable accepted CWComparison
checkpoint; its source attribution is preserved in that supplier.
Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry,
Theorem 3.3.1; the kernel resolution is Mathlib's proved LeftResolution API.
The augmentation quasi-isomorphism proof adapts the degree-zero/positive
degree argument of Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean
at 5e0c4e5239cb0a2d86d68a884bf52cfd963fce22, copyright (c) 2022 Jujian Zhang,
authors Markus Himmel, Kim Morrison, Jakob von Raumer and Joël Riou,
released under Apache 2.0.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits

namespace LightCondensed.Solid

/-- Actual generator maps form a small index, using the proved locally
small Hom structure. Only universe-zero coproducts are used. -/
abbrev SolidGeneratorIndex (X : Solid) :=
  Shrink.{0} (solidification.obj P ⟶ X)

def solidGeneratorIndexMap (X : Solid) :
    SolidGeneratorIndex X → (solidification.obj P ⟶ X) :=
  (equivShrink (solidification.obj P ⟶ X)).symm

/-- The sum is indexed by the small model of all actual generator maps. -/
def solidGeneratorCopower (X : Solid) : Solid :=
  ∐ fun _ : SolidGeneratorIndex X => solidification.obj P

/-- The concrete evaluation augmentation. -/
def solidGeneratorEvaluation (X : Solid) : solidGeneratorCopower X ⟶ X :=
  Limits.Sigma.desc (solidGeneratorIndexMap X)

@[reassoc (attr := simp)]
theorem solidGeneratorEvaluation_leg (X : Solid) (f : solidification.obj P ⟶ X) :
    Sigma.ι (fun _ : SolidGeneratorIndex X => solidification.obj P)
      (equivShrink (solidification.obj P ⟶ X) f) ≫ solidGeneratorEvaluation X = f := by
  simp [solidGeneratorEvaluation, solidGeneratorIndexMap]

/-- Actual surjectivity is proved using the canonical P unit and ambient
P projectivity. Zero detection alone is not treated as surjectivity. -/
instance solidGeneratorEvaluation_epi (X : Solid) : Epi (solidGeneratorEvaluation X) := by
  let p := solidGeneratorEvaluation X
  have hc : IsZero (cokernel p) := by
    apply solidP_detects_isZero
    intro f
    let e := solidificationAdjunction.homEquiv P (cokernel p)
    let g := Projective.factorThru (e f) (isSolid.ι.map (cokernel.π p))
    let g' := (solidificationAdjunction.homEquiv P X).symm g
    have hg : g' ≫ cokernel.π p = f := by
      apply e.injective
      rw [solidificationAdjunction.homEquiv_naturality_right]
      change (solidificationAdjunction.homEquiv P X) g' ≫
        isSolid.ι.map (cokernel.π p) = e f
      rw [Equiv.apply_symm_apply]
      exact Projective.factorThru_comp _ _
    rw [← hg, ← solidGeneratorEvaluation_leg X g', Category.assoc]
    change _ ≫ p ≫ cokernel.π p = 0
    rw [cokernel.condition, comp_zero]
  exact Abelian.epi_of_cokernel_π_eq_zero p (hc.eq_zero_of_tgt _)

/-- The same concrete augmentation proves the ordinary generator property. -/
theorem solidP_isSeparator : IsSeparator (solidification.obj P) := by
  apply (isSeparator_def _).2
  intro X Y f g hfg
  apply (cancel_epi (solidGeneratorEvaluation X)).1
  apply Sigma.hom_ext
  intro a
  change Sigma.ι (fun _ : SolidGeneratorIndex X => solidification.obj P) a ≫
    solidGeneratorEvaluation X ≫ f =
      Sigma.ι (fun _ : SolidGeneratorIndex X => solidification.obj P) a ≫
        solidGeneratorEvaluation X ≫ g
  simp only [solidGeneratorEvaluation, Sigma.ι_desc_assoc]
  exact hfg (solidGeneratorIndexMap X a)

/-- Small generator copowers are projective by explicit legwise lifting.
The proof works at the actual small index universe. -/
instance solidGeneratorCopower_projective (X : Solid) : Projective (solidGeneratorCopower X) where
  factors f e _ := by
    haveI : Projective (solidification.obj P) := CWSolid.U_projective
    refine ⟨Limits.Sigma.desc (fun a : SolidGeneratorIndex X =>
      Projective.factorThru (Sigma.ι (fun _ : SolidGeneratorIndex X =>
        solidification.obj P) a ≫ f) e), ?_⟩
    apply Sigma.hom_ext
    intro a
    simp only [Category.assoc, Sigma.ι_desc_assoc, Projective.factorThru_comp]

/-- Enough projectives is proved here ONLY for the protected Solid category,
using its actual generator sums and the already-proved ambient P projectivity.
No such assertion is made about LightCondAb or its unbounded complexes. -/
instance solid_enoughProjectives : EnoughProjectives Solid where
  presentation X := by
    haveI : Projective (solidification.obj P) := CWSolid.U_projective
    exact ⟨{ p := solidGeneratorCopower X, f := solidGeneratorEvaluation X }⟩

/-- Postcomposition gives the functor on these actual copowers. -/
def solidGeneratorCopowerFunctor : Solid ⥤ Solid where
  obj := solidGeneratorCopower
  map {X Y} f := Limits.Sigma.desc (fun a : SolidGeneratorIndex X =>
    Sigma.ι (fun _ : SolidGeneratorIndex Y => solidification.obj P)
      (equivShrink (solidification.obj P ⟶ Y) (solidGeneratorIndexMap X a ≫ f)))
  map_id X := by
    apply Sigma.hom_ext
    intro a
    simp [solidGeneratorIndexMap, Category.comp_id]
    exact (Category.comp_id _).symm
  map_comp f g := by
    apply Sigma.hom_ext
    intro a
    simp [solidGeneratorIndexMap, Category.assoc]

/-- This is the actual natural augmentation, with proved epi components. -/
def solidGeneratorAugmentation : solidGeneratorCopowerFunctor ⟶ 𝟭 Solid where
  app := solidGeneratorEvaluation
  naturality X Y f := by
    apply Sigma.hom_ext
    intro g
    simp [solidGeneratorCopowerFunctor, solidGeneratorEvaluation,
      solidGeneratorIndexMap, Category.assoc]

/-- The exact kernel iteration is supplied with actual data, rather than
an assumption that a generating resolution exists. -/
def solidGeneratorLeftResolution : Abelian.LeftResolution (𝟭 Solid) where
  F := solidGeneratorCopowerFunctor
  π := solidGeneratorAugmentation
  epi_π_app X := solidGeneratorEvaluation_epi X

def solidGeneratorResolution (X : Solid) : ChainComplex Solid ℕ :=
  solidGeneratorLeftResolution.chainComplex X

/-- Each actual term is a sum of the exact protected generator, with the
successive kernel object recorded rather than an unspecified resolution term. -/
theorem solidGeneratorResolution_term_copower (X : Solid) (n : ℕ) :
    ∃ Y : Solid, Nonempty ((solidGeneratorResolution X).X n ≅ solidGeneratorCopower Y) := by
  cases n with
  | zero => exact ⟨X, ⟨solidGeneratorLeftResolution.chainComplexXZeroIso X⟩⟩
  | succ n =>
    cases n with
    | zero => exact ⟨kernel (solidGeneratorEvaluation X),
        ⟨solidGeneratorLeftResolution.chainComplexXOneIso X⟩⟩
    | succ n => exact ⟨kernel ((solidGeneratorResolution X).d (n + 1) n),
        ⟨solidGeneratorLeftResolution.chainComplexXIso X n⟩⟩

/-- Every term of the specific augmented resolution is projective,
proved from its displayed generator copower. -/
instance solidGeneratorResolution_term_projective (X : Solid) (n : ℕ) :
    Projective ((solidGeneratorResolution X).X n) := by
  obtain ⟨Y, ⟨e⟩⟩ := solidGeneratorResolution_term_copower X n
  exact Projective.of_iso e.symm inferInstance

/-- The constructed resolution is exact in every positive degree. -/
theorem solidGeneratorResolution_exactAt_succ (X : Solid) (n : ℕ) :
    (solidGeneratorResolution X).ExactAt (n + 1) := by
  exact solidGeneratorLeftResolution.exactAt_map_chainComplex_succ X n

/-- The actual augmentation uses the canonical degree-zero resolution iso. -/
def solidGeneratorResolutionπ (X : Solid) :
    solidGeneratorResolution X ⟶ (ChainComplex.single₀ Solid).obj X :=
  CWSolid.kernelResolutionπ solidGeneratorLeftResolution X

/-- Exactness includes the actual augmentation in degree zero. -/
theorem solidGeneratorResolutionπ_quasiIso (X : Solid) :
    QuasiIso (solidGeneratorResolutionπ X) :=
  CWSolid.kernelResolutionπ_quasiIso solidGeneratorLeftResolution X

/-- The constructed augmentation is natural for the actual kernel
resolution functor, rather than a collection of unrelated objectwise maps. -/
@[reassoc]
theorem solidGeneratorResolutionπ_naturality {X Y : Solid} (f : X ⟶ Y) :
    solidGeneratorLeftResolution.chainComplexMap f ≫ solidGeneratorResolutionπ Y =
      solidGeneratorResolutionπ X ≫ (ChainComplex.single₀ Solid).map f := by
  exact CWSolid.kernelResolutionπ_naturality solidGeneratorLeftResolution f

def solidGeneratorResolutionAugmentation :
    solidGeneratorLeftResolution.chainComplexFunctor ⟶ ChainComplex.single₀ Solid where
  app := solidGeneratorResolutionπ
  naturality _ _ f := solidGeneratorResolutionπ_naturality f

/-- This bundles the concrete generator-kernel resolution, preserving its
terms and its actual augmentation, for Mathlib's integer extension. -/
def solidGeneratorProjectiveResolution (X : Solid) : ProjectiveResolution X where
  complex := solidGeneratorResolution X
  π := solidGeneratorResolutionπ X
  quasiIso := solidGeneratorResolutionπ_quasiIso X

/-- The actual cochain resolution has every negative degree, rather than
a finite truncation of the resolution. -/
def solidGeneratorCochainResolution (X : Solid) : CochainComplex Solid ℤ :=
  (solidGeneratorProjectiveResolution X).cochainComplex

def solidGeneratorCochainResolutionπ (X : Solid) :
    solidGeneratorCochainResolution X ⟶ (CochainComplex.singleFunctor Solid 0).obj X :=
  (solidGeneratorProjectiveResolution X).π'

theorem solidGeneratorCochainResolutionπ_quasiIso (X : Solid) :
    QuasiIso (solidGeneratorCochainResolutionπ X) := by
  unfold solidGeneratorCochainResolutionπ
  infer_instance

/-- The negative coefficients of this actual infinite cochain resolution
are the displayed copowers; positive coefficients are genuinely zero. -/
theorem solidGeneratorCochainResolution_negative_term (X : Solid) (n : ℕ) :
    ∃ Y : Solid, Nonempty ((solidGeneratorCochainResolution X).X (-(n : ℤ)) ≅
      solidGeneratorCopower Y) := by
  obtain ⟨Y, ⟨e⟩⟩ := solidGeneratorResolution_term_copower X n
  exact ⟨Y, ⟨(solidGeneratorProjectiveResolution X).cochainComplexXIso (-(n : ℤ)) n ≪≫ e⟩⟩

end LightCondensed.Solid

#print axioms LightCondensed.Solid.SolidGeneratorIndex
#print axioms LightCondensed.Solid.solidGeneratorIndexMap
#print axioms LightCondensed.Solid.solidGeneratorCopower
#print axioms LightCondensed.Solid.solidGeneratorEvaluation
#print axioms LightCondensed.Solid.solidGeneratorEvaluation_leg
#print axioms LightCondensed.Solid.solidGeneratorEvaluation_epi
#print axioms LightCondensed.Solid.solidP_isSeparator
#print axioms LightCondensed.Solid.solidGeneratorCopower_projective
#print axioms LightCondensed.Solid.solid_enoughProjectives
#print axioms LightCondensed.Solid.solid_isGrothendieckAbelian
#print axioms LightCondensed.Solid.solidGeneratorCopowerFunctor
#print axioms LightCondensed.Solid.solidGeneratorAugmentation
#print axioms LightCondensed.Solid.solidGeneratorLeftResolution
#print axioms LightCondensed.Solid.solidGeneratorResolution
#print axioms LightCondensed.Solid.solidGeneratorResolution_term_copower
#print axioms LightCondensed.Solid.solidGeneratorResolution_term_projective
#print axioms LightCondensed.Solid.solidGeneratorResolution_exactAt_succ
#print axioms LightCondensed.Solid.solidGeneratorResolutionπ
#print axioms LightCondensed.Solid.solidGeneratorResolutionπ_quasiIso
#print axioms LightCondensed.Solid.solidGeneratorResolutionπ_naturality
#print axioms LightCondensed.Solid.solidGeneratorResolutionAugmentation
#print axioms LightCondensed.Solid.solidGeneratorProjectiveResolution
#print axioms LightCondensed.Solid.solidGeneratorCochainResolution
#print axioms LightCondensed.Solid.solidGeneratorCochainResolutionπ
#print axioms LightCondensed.Solid.solidGeneratorCochainResolutionπ_quasiIso
#print axioms LightCondensed.Solid.solidGeneratorCochainResolution_negative_term
