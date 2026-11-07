/- GID: D5/S3/Quantum/Algebra/FinitePositiveKernelQuotient
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/FinitePositiveKernelQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite positive Gram matrices define complete matrix-kernel quotients and unique labelled isometries. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.InnerProductSpace.GramMatrix

noncomputable section
open scoped InnerProductSpace Matrix ComplexOrder
open Matrix
namespace D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient
variable {M : Type*} [Fintype M]

def Coefficients (D : Matrix M M ℂ) (_hD : D.PosSemidef) := M → ℂ
instance (D : Matrix M M ℂ) (hD : D.PosSemidef) : SeminormedAddCommGroup (Coefficients D hD) :=
  Matrix.toSeminormedAddCommGroup D hD
instance (D : Matrix M M ℂ) (hD : D.PosSemidef) : Module ℂ (Coefficients D hD) :=
  inferInstanceAs (Module ℂ (M → ℂ))
instance (D : Matrix M M ℂ) (hD : D.PosSemidef) : InnerProductSpace ℂ (Coefficients D hD) :=
  Matrix.toInnerProductSpace D hD

instance (D : Matrix M M ℂ) (hD : D.PosSemidef) : NormedSpace ℂ (Coefficients D hD) :=
  (Matrix.toInnerProductSpace D hD).toNormedSpace

private theorem inner_coeff (D : Matrix M M ℂ) (hD : D.PosSemidef)
    (c d : Coefficients D hD) :
    ⟪c, d⟫_ℂ = star c ⬝ᵥ D *ᵥ d := by
  change (D *ᵥ d) ⬝ᵥ star c = _
  exact dotProduct_comm _ _

private def projection (D : Matrix M M ℂ) (hD : D.PosSemidef) :
    (M → ℂ) →ₗ[ℂ] SeparationQuotient (Coefficients D hD) :=
  (SeparationQuotient.mkCLM ℂ (Coefficients D hD)).toLinearMap

private theorem projection_ker (D : Matrix M M ℂ) (hD : D.PosSemidef) :
    (projection D hD).ker = D.mulVecLin.ker := by
  ext c
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  change SeparationQuotient.mk (c : Coefficients D hD) = 0 ↔ D *ᵥ c = 0
  rw [← inner_self_eq_zero (𝕜 := ℂ)]
  change ⟪SeparationQuotient.mk (c : Coefficients D hD),
    SeparationQuotient.mk (c : Coefficients D hD)⟫_ℂ = 0 ↔ _
  rw [SeparationQuotient.inner_mk_mk, inner_coeff, hD.dotProduct_mulVec_zero_iff]

private def quotientEquiv (D : Matrix M M ℂ) (hD : D.PosSemidef) :
    ((M → ℂ) ⧸ D.mulVecLin.ker) ≃ₗ[ℂ] SeparationQuotient (Coefficients D hD) :=
  (Submodule.quotEquivOfEq _ _ (projection_ker D hD).symm).trans
    ((projection D hD).quotKerEquivOfSurjective (fun x => Quotient.mk_surjective x))

end D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient

namespace D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient
variable {M : Type*} [Fintype M]

def Space (D : Matrix M M ℂ) (_hD : D.PosSemidef) := (M → ℂ) ⧸ D.mulVecLin.ker
instance (D : Matrix M M ℂ) (hD : D.PosSemidef) : AddCommGroup (Space D hD) :=
  inferInstanceAs (AddCommGroup ((M → ℂ) ⧸ D.mulVecLin.ker))
instance (D : Matrix M M ℂ) (hD : D.PosSemidef) : Module ℂ (Space D hD) :=
  inferInstanceAs (Module ℂ ((M → ℂ) ⧸ D.mulVecLin.ker))
instance (D : Matrix M M ℂ) (hD : D.PosSemidef) : NormedAddCommGroup (Space D hD) :=
  NormedAddCommGroup.induced _ _ (quotientEquiv D hD) (quotientEquiv D hD).injective
instance (D : Matrix M M ℂ) (hD : D.PosSemidef) : InnerProductSpace ℂ (Space D hD) :=
  InnerProductSpace.induced (quotientEquiv D hD).toLinearMap
instance (D : Matrix M M ℂ) (hD : D.PosSemidef) : FiniteDimensional ℂ (Space D hD) :=
  inferInstanceAs (FiniteDimensional ℂ ((M → ℂ) ⧸ D.mulVecLin.ker))
instance (D : Matrix M M ℂ) (hD : D.PosSemidef) : CompleteSpace (Space D hD) :=
  FiniteDimensional.complete ℂ _

def mk (D : Matrix M M ℂ) (hD : D.PosSemidef) : (M → ℂ) →ₗ[ℂ] Space D hD :=
  D.mulVecLin.ker.mkQ

private theorem quotientEquiv_mk (D : Matrix M M ℂ) (hD : D.PosSemidef) (c : M → ℂ) :
    quotientEquiv D hD (mk D hD c) = SeparationQuotient.mk (c : Coefficients D hD) := by
  simp [quotientEquiv, mk, projection, Submodule.quotEquivOfEq_mk]

theorem inner_mk (D : Matrix M M ℂ) (hD : D.PosSemidef) (c d : M → ℂ) :
    ⟪mk D hD c, mk D hD d⟫_ℂ = star c ⬝ᵥ D *ᵥ d := by
  change ⟪quotientEquiv D hD (mk D hD c), quotientEquiv D hD (mk D hD d)⟫_ℂ = _
  rw [quotientEquiv_mk, quotientEquiv_mk, SeparationQuotient.inner_mk_mk, inner_coeff]

def label (D : Matrix M M ℂ) (hD : D.PosSemidef) [DecidableEq M] (i : M) : Space D hD :=
  mk D hD (Pi.single i 1)

private theorem labels_span (D : Matrix M M ℂ) (hD : D.PosSemidef) [DecidableEq M] :
    Submodule.span ℂ (Set.range (label D hD)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨c, rfl⟩ := (Submodule.Quotient.mk_surjective D.mulVecLin.ker) x
  have hc : c = ∑ i, c i • (Pi.single i 1 : M → ℂ) := by
    ext j
    simp
  rw [show (Submodule.Quotient.mk c : Space D hD) = mk D hD c from rfl, hc, map_sum]
  exact Submodule.sum_mem _ fun i _ =>
    (map_smul (mk D hD) (c i) _).symm ▸
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

private theorem spanning_analysis_injective {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : M → E)
    (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    Function.Injective (fun x : E => fun i => ⟪v i, x⟫_ℂ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hz : ∀ z ∈ Submodule.span ℂ (Set.range v), ⟪z, x - y⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      simpa only [inner_sub_right, sub_eq_zero] using congrFun hxy i
    | zero => simp
    | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
    | smul c a _ ha => simp [inner_smul_left, ha]
  exact hz (x - y) (hv ▸ Submodule.mem_top)

private def familyRKHS {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : M → E) (hv : Submodule.span ℂ (Set.range v) = ⊤) : RKHS ℂ E M ℂ where
  coeCLM := ContinuousLinearMap.pi fun i => innerSL ℂ (v i)
  coeCLM_injective := spanning_analysis_injective v hv

private theorem family_kerFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (v : M → E) (hv : Submodule.span ℂ (Set.range v) = ⊤) (i : M) (z : ℂ) :
    letI := familyRKHS v hv
    RKHS.kerFun E i z = z • v i := by
  letI := familyRKHS v hv
  apply ext_inner_right ℂ
  intro x
  rw [RKHS.kerFun_inner, inner_smul_left]
  simp [familyRKHS, RCLike.inner_apply]

private def familyEquiv {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (v : M → E) (w : M → F)
    (hv : Submodule.span ℂ (Set.range v) = ⊤)
    (hw : Submodule.span ℂ (Set.range w) = ⊤)
    (hg : ∀ i j, ⟪v i, v j⟫_ℂ = ⟪w i, w j⟫_ℂ) : E ≃ₗᵢ[ℂ] F := by
  letI := familyRKHS v hv
  letI := familyRKHS w hw
  apply RKHS.equiv
  ext i j z
  apply ext_inner_right ℂ
  intro t
  rw [RKHS.kernel_inner, RKHS.kernel_inner]
  simp [family_kerFun, inner_smul_left, inner_smul_right, hg]

private theorem familyEquiv_label {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (v : M → E) (w : M → F)
    (hv : Submodule.span ℂ (Set.range v) = ⊤)
    (hw : Submodule.span ℂ (Set.range w) = ⊤)
    (hg : ∀ i j, ⟪v i, v j⟫_ℂ = ⟪w i, w j⟫_ℂ) (i : M) :
    familyEquiv v w hv hw hg (v i) = w i := by
  letI := familyRKHS v hv
  letI := familyRKHS w hw
  have hh := RKHS.equiv_kerFun (H := E) (H' := F)
    (show RKHS.kernel E = RKHS.kernel F from by
      ext i j z
      apply ext_inner_right ℂ
      intro t
      rw [RKHS.kernel_inner, RKHS.kernel_inner]
      simp [family_kerFun, inner_smul_left, inner_smul_right, hg]) i (1 : ℂ)
  simpa [family_kerFun, familyEquiv] using hh

/-- The matrix-kernel quotient realizes all finite positive Gram data, including rank zero. -/
theorem finite_positive_kernel_quotient (D : Matrix M M ℂ) (hD : D.PosSemidef) [DecidableEq M] :
    (∀ c d : M → ℂ, ⟪mk D hD c, mk D hD d⟫_ℂ = star c ⬝ᵥ D *ᵥ d) ∧
    Module.finrank ℂ (Space D hD) = D.rank ∧
    (∀ i j, ⟪label D hD i, label D hD j⟫_ℂ = D i j) ∧
    Submodule.span ℂ (Set.range (label D hD)) = ⊤ ∧
    (∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (v : M → E), (∀ i j, ⟪v i, v j⟫_ℂ = D i j) →
      Submodule.span ℂ (Set.range v) = ⊤ →
      ∃! U : Space D hD ≃ₗᵢ[ℂ] E, ∀ i, U (label D hD i) = v i) := by
  have hl : ∀ i j, ⟪label D hD i, label D hD j⟫_ℂ = D i j := by
    intro i j
    simp [label, inner_mk, dotProduct, Matrix.mulVec, Pi.single_apply]
  refine ⟨inner_mk D hD, ?_, hl, labels_span D hD, ?_⟩
  · exact D.mulVecLin.quotKerEquivRange.finrank_eq
  · intro E _ _ _ v hv hspan
    let U := familyEquiv (label D hD) v (labels_span D hD) hspan
      (fun i j => (hl i j).trans (hv i j).symm)
    refine ⟨U, familyEquiv_label _ _ _ _ _ , ?_⟩
    intro V hV
    apply LinearIsometryEquiv.toLinearEquiv_injective
    apply LinearEquiv.toLinearMap_injective
    exact LinearMap.ext_on_range (labels_span D hD) fun i =>
      (hV i).trans (familyEquiv_label _ _ _ _ _ i).symm
end D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient
