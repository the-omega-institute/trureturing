/- GID: D5/S3/HomologicalAlgebra/Solid/AugmentedKernelResolution
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/AugmentedKernelResolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.Algebra.Homology.LeftResolution.Basic
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
The actual augmentation of Mathlib's successive-kernel left resolution
is quasi-isomorphic to the input object. This supplies both the solid
generator resolution and the ambient nonprojective free resolution.
The resolution is constructed from the given natural epi data; no
resolution-existence hypothesis is introduced.
Mathlib construction: copyright (c) 2025 Joël Riou, Apache-2.0, commit
5e0c4e5239cb0a2d86d68a884bf52cfd963fce22.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits HomologicalComplex

namespace CWSolid
variable {C : Type*} [Category* C] [Abelian C]
  (Λ : Abelian.LeftResolution (𝟭 C)) (X : C)

def kernelResolutionEvaluation : (Λ.chainComplex X).X 0 ⟶ X :=
  (Λ.chainComplexXZeroIso X).hom ≫ Λ.π.app X

private theorem kernelResolutionEvaluation_condition :
    (Λ.chainComplex X).d 1 0 ≫ kernelResolutionEvaluation Λ X = 0 := by
  have h := Λ.map_chainComplex_d_1_0 X
  simp only [Functor.id_map] at h
  rw [kernelResolutionEvaluation, ← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_assoc,
    kernel.condition, comp_zero]

def kernelResolutionπ : Λ.chainComplex X ⟶ (ChainComplex.single₀ C).obj X :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨kernelResolutionEvaluation Λ X, kernelResolutionEvaluation_condition Λ X⟩

theorem kernelResolutionEvaluation_exact :
    (ShortComplex.mk _ _ (kernelResolutionEvaluation_condition Λ X)).Exact := by
  let p := Λ.π.app X
  let q := Λ.π.app (kernel p)
  let S : ShortComplex C := ShortComplex.mk (q ≫ kernel.ι p) p (by simp)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have he : kernel.lift p (q ≫ kernel.ι p) S.zero = q := by
      apply (cancel_mono (kernel.ι p)).1
      rw [kernel.lift_ι]
    change Epi (kernel.lift p (q ≫ kernel.ι p) S.zero)
    rw [he]
    exact Λ.epi_π_app _
  let e : ShortComplex.mk _ _ (kernelResolutionEvaluation_condition Λ X) ≅ S :=
    ShortComplex.isoMk (Λ.chainComplexXOneIso X) (Λ.chainComplexXZeroIso X) (Iso.refl X)
      (by
        have h := Λ.map_chainComplex_d_1_0 X
        simp only [Functor.id_map] at h
        change (Λ.chainComplexXOneIso X).hom ≫ (q ≫ kernel.ι p) =
          (Λ.chainComplex X).d 1 0 ≫ (Λ.chainComplexXZeroIso X).hom
        rw [h]
        simp only [Category.assoc]
        rw [← Category.assoc, Iso.inv_hom_id, Category.comp_id]
        simp only [p, q, Category.assoc])
      (by simp [kernelResolutionEvaluation, S, p])
  exact (ShortComplex.exact_iff_of_iso e).2 hS

instance kernelResolutionEvaluation_epi : Epi (kernelResolutionEvaluation Λ X) := by
  haveI : Epi (Λ.π.app X) := Λ.epi_π_app X
  unfold kernelResolutionEvaluation
  infer_instance

theorem kernelResolutionπ_quasiIso : QuasiIso (kernelResolutionπ Λ X) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff,
      ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp) (by simp)]
    constructor
    · simpa [kernelResolutionπ, ChainComplex.toSingle₀Equiv] using
        kernelResolutionEvaluation_exact Λ X
    · simpa [kernelResolutionπ, ChainComplex.toSingle₀Equiv] using
        kernelResolutionEvaluation_epi Λ X
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact Λ.exactAt_map_chainComplex_succ X n

@[reassoc]
theorem kernelResolutionπ_naturality {X Y : C} (f : X ⟶ Y) :
    Λ.chainComplexMap f ≫ kernelResolutionπ Λ Y =
      kernelResolutionπ Λ X ≫ (ChainComplex.single₀ C).map f := by
  apply HomologicalComplex.to_single_hom_ext
  simp [kernelResolutionπ, kernelResolutionEvaluation,
    Abelian.LeftResolution.chainComplexMap_f_0, Λ.π.naturality f]

def kernelResolutionCochain : CochainComplex C ℤ :=
  (Λ.chainComplex X).extend ComplexShape.embeddingDownNat

def kernelResolutionCochainπ :
    kernelResolutionCochain Λ X ⟶ (CochainComplex.singleFunctor C 0).obj X :=
  (ComplexShape.embeddingDownNat.extendFunctor C).map (kernelResolutionπ Λ X) ≫
    (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).hom

instance kernelResolutionCochain_strictlyLE :
    (kernelResolutionCochain Λ X).IsStrictlyLE 0 := by
  dsimp [kernelResolutionCochain]
  infer_instance

theorem kernelResolutionCochainπ_quasiIso : QuasiIso (kernelResolutionCochainπ Λ X) := by
  haveI := kernelResolutionπ_quasiIso Λ X
  dsimp [kernelResolutionCochainπ]
  change QuasiIso (HomologicalComplex.extendMap (kernelResolutionπ Λ X)
    ComplexShape.embeddingDownNat ≫ _)
  infer_instance

end CWSolid

#print axioms CWSolid.kernelResolutionEvaluation
#print axioms CWSolid.kernelResolutionπ
#print axioms CWSolid.kernelResolutionEvaluation_exact
#print axioms CWSolid.kernelResolutionEvaluation_epi
#print axioms CWSolid.kernelResolutionπ_quasiIso
#print axioms CWSolid.kernelResolutionπ_naturality
#print axioms CWSolid.kernelResolutionCochain
#print axioms CWSolid.kernelResolutionCochainπ
#print axioms CWSolid.kernelResolutionCochain_strictlyLE
#print axioms CWSolid.kernelResolutionCochainπ_quasiIso
