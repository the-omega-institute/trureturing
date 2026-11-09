/- GID: D5/S3/Quantum/Algebra/ActualCommonBidualRoot
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ActualCommonBidualRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.ContinuousMap.Weierstrass, mathlib/module/Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal]
   utility: none
   digest: A single positive square root in the first-Arens real bidual realizes every actual GNS square root and lies in the closed one-generator subspace. -/

import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Normed.Module.HahnBanach
import D5.S3.Quantum.Algebra.CentralPositiveFunctionalExtension
import D5.S3.QuantumStates.GNSCompatibleStateExtension
import D5.S3.Topology.JBAlgebra

noncomputable section
open scoped ComplexOrder ComplexConjugate
open Complex InnerProductSpace

namespace ActualGNSCoefficientViaExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private def realLift (F : StrongDual ℝ (StrongDual ℝ V)) :
    StrongDual ℝ (V →L[ℝ] ℂ) :=
  F.comp (Complex.reCLM.postcomp V)
private lemma realLift_norm (F : StrongDual ℝ (StrongDual ℝ V)) :
    ‖realLift F‖ ≤ ‖F‖ := by
  have hr : ‖Complex.reCLM.postcomp V‖ ≤ 1 :=
    (ContinuousLinearMap.norm_postcomp_le (σ₁₂ := RingHom.id ℝ) (E := V) Complex.reCLM).trans_eq Complex.reCLM_norm
  calc
    ‖realLift F‖ ≤ ‖F‖ * ‖Complex.reCLM.postcomp V‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hr (norm_nonneg F)
    _ = ‖F‖ := mul_one _

private def lift (F : StrongDual ℝ (StrongDual ℝ V)) :
    StrongDual ℂ (V →L[ℝ] ℂ) :=
  (realLift F).extendRCLike
private lemma lift_apply (F : StrongDual ℝ (StrongDual ℝ V))
    (c : V →L[ℝ] ℂ) :
    lift F c = (F (reCLM.comp c) : ℂ) + I * (F (imCLM.comp c) : ℂ) := by
  have hi : reCLM.comp (I • c) = -(imCLM.comp c) := by
    ext x
    simp [smul_eq_mul, Complex.mul_re]
  rw [lift, StrongDual.extendRCLike_apply]
  change (F (reCLM.comp c) : ℂ) - I * (F (reCLM.comp (I • c)) : ℂ) = _
  rw [hi, map_neg, Complex.ofReal_neg]
  ring
private lemma lift_bound (F : StrongDual ℝ (StrongDual ℝ V))
    (c : V →L[ℝ] ℂ) : ‖lift F c‖ ≤ ‖F‖ * ‖c‖ := by
  calc
    ‖lift F c‖ ≤ ‖realLift F‖ * ‖c‖ :=
      StrongDual.norm_extendRCLike_bound (𝕜 := ℂ) (realLift F) c
    _ ≤ ‖F‖ * ‖c‖ := mul_le_mul_of_nonneg_right (realLift_norm F) (norm_nonneg c)
private lemma lift_conj (F : StrongDual ℝ (StrongDual ℝ V))
    (c : V →L[ℝ] ℂ) :
    lift F (Complex.conjCLE.toContinuousLinearMap.comp c) = conj (lift F c) := by
  have hr : reCLM.comp (Complex.conjCLE.toContinuousLinearMap.comp c) =
      reCLM.comp c := by ext x; simp
  have hi : imCLM.comp (Complex.conjCLE.toContinuousLinearMap.comp c) =
      -(imCLM.comp c) := by ext x; simp
  rw [lift_apply, lift_apply, hr, hi, map_neg]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def representationCLM (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    A →L[ℂ] (H →L[ℂ] H) :=
  π.toAlgHom.toLinearMap.mkContinuous 1 (fun a => by
    simpa only [one_mul] using! NonUnitalStarAlgHom.norm_apply_le π a)

/-- Original-label coefficient, using the given isometric inclusion without completion. -/
def coefficient (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (i : V →ₗᵢ[ℝ] A) (ξ η : H) : V →L[ℝ] ℂ :=
  (((innerSL ℂ ξ).comp
    ((ContinuousLinearMap.apply ℂ H η).comp (representationCLM π))).restrictScalars ℝ).comp
      i.toContinuousLinearMap
private lemma coefficient_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (i : V →ₗᵢ[ℝ] A) (ξ η : H) (x : V) :
    coefficient π i ξ η x = inner ℂ ξ (π (i x) η) := rfl

private lemma coefficient_norm (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (i : V →ₗᵢ[ℝ] A) (ξ η : H) : ‖coefficient π i ξ η‖ ≤ ‖ξ‖ * ‖η‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg ξ) (norm_nonneg η))
  intro x
  rw [coefficient_apply]
  calc
    ‖inner ℂ ξ (π (i x) η)‖ ≤ ‖ξ‖ * ‖π (i x) η‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖π (i x)‖ * ‖η‖) :=
      mul_le_mul_of_nonneg_left ((π (i x)).le_opNorm η) (norm_nonneg ξ)
    _ ≤ ‖ξ‖ * (‖i x‖ * ‖η‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le π (i x))
          (norm_nonneg η)) (norm_nonneg ξ)
    _ = (‖ξ‖ * ‖η‖) * ‖x‖ := by rw [i.norm_map]; ring
private def form (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (i : V →ₗᵢ[ℝ] A)
    (F : StrongDual ℝ (StrongDual ℝ V)) : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun ξ := {
    toFun η := lift F (coefficient π i ξ η)
    map_add' η ζ := by
      have hc : coefficient π i ξ (η + ζ) =
          coefficient π i ξ η + coefficient π i ξ ζ := by
        ext x
        simp only [coefficient_apply, ContinuousLinearMap.add_apply, map_add, inner_add_right]
      change lift F (coefficient π i ξ (η + ζ)) = _
      rw [hc, map_add]
    map_smul' z η := by
      have hc : coefficient π i ξ (z • η) = z • coefficient π i ξ η := by
        ext x
        simp only [coefficient_apply, ContinuousLinearMap.smul_apply, map_smul,
          inner_smul_right, smul_eq_mul]
      change lift F (coefficient π i ξ (z • η)) = z • lift F (coefficient π i ξ η)
      rw [hc, map_smul] }
  map_add' ξ ζ := by
    ext η
    have hc : coefficient π i (ξ + ζ) η =
        coefficient π i ξ η + coefficient π i ζ η := by
      ext x
      simp only [coefficient_apply, ContinuousLinearMap.add_apply, inner_add_left]
    change lift F (coefficient π i (ξ + ζ) η) =
      lift F (coefficient π i ξ η) + lift F (coefficient π i ζ η)
    rw [hc, map_add]
  map_smul' z ξ := by
    ext η
    have hc : coefficient π i (z • ξ) η = conj z • coefficient π i ξ η := by
      ext x
      simp only [coefficient_apply, ContinuousLinearMap.smul_apply, inner_smul_left, smul_eq_mul]
    change lift F (coefficient π i (z • ξ) η) =
      conj z • lift F (coefficient π i ξ η)
    rw [hc, map_smul]
private lemma form_bound (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (i : V →ₗᵢ[ℝ] A)
    (F : StrongDual ℝ (StrongDual ℝ V)) (ξ η : H) :
    ‖form π i F ξ η‖ ≤ ‖F‖ * ‖ξ‖ * ‖η‖ := by
  calc
    ‖form π i F ξ η‖ ≤ ‖F‖ * ‖coefficient π i ξ η‖ := lift_bound F _
    _ ≤ ‖F‖ * (‖ξ‖ * ‖η‖) :=
      mul_le_mul_of_nonneg_left (coefficient_norm π i ξ η) (norm_nonneg F)
    _ = ‖F‖ * ‖ξ‖ * ‖η‖ := (mul_assoc _ _ _).symm
private lemma form_hermitian (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (i : V →ₗᵢ[ℝ] A)
    (hi : ∀ x, IsSelfAdjoint (i x)) (F : StrongDual ℝ (StrongDual ℝ V)) (ξ η : H) :
    form π i F η ξ = conj (form π i F ξ η) := by
  have hc : coefficient π i η ξ =
      Complex.conjCLE.toContinuousLinearMap.comp (coefficient π i ξ η) := by
    ext x
    change inner ℂ η (π (i x) ξ) = conj (inner ℂ ξ (π (i x) η))
    calc
      inner ℂ η (π (i x) ξ) = inner ℂ (π (i x) η) ξ :=
        (((hi x).map π).isSymmetric η ξ).symm
      _ = conj (inner ℂ ξ (π (i x) η)) := (inner_conj_symm _ _).symm
  change lift F (coefficient π i η ξ) = conj (lift F (coefficient π i ξ η))
  rw [hc, lift_conj]
variable [PartialOrder A] [StarOrderedRing A]

/-- Coefficient representation in each actual unnormalized GNS. -/
private theorem original_gns_exists_unique (i : V →ₗᵢ[ℝ] A)
    (hi : ∀ x, IsSelfAdjoint (i x)) (ψ : A →ₚ[ℂ] ℂ)
    (F : StrongDual ℝ (StrongDual ℝ V)) :
    ∃! T : ψ.GNS →L[ℂ] ψ.GNS,
      IsSelfAdjoint T ∧ ‖T‖ ≤ ‖F‖ ∧
      (∀ ξ η, inner ℂ ξ (T η) =
        (F (reCLM.comp (coefficient ψ.gnsStarAlgHom i ξ η)) : ℂ) +
          I * (F (imCLM.comp (coefficient ψ.gnsStarAlgHom i ξ η)) : ℂ)) ∧
      (∀ x : V, F = NormedSpace.inclusionInDoubleDual ℝ V x →
        T = ψ.gnsStarAlgHom (i x)) := by
  let π := ψ.gnsStarAlgHom
  let B := (form π i F).mkContinuous₂ ‖F‖ (form_bound π i F)
  let T := InnerProductSpace.continuousLinearMapOfBilin B
  have hleft (ξ η : ψ.GNS) : inner ℂ (T ξ) η = form π i F ξ η :=
    InnerProductSpace.continuousLinearMapOfBilin_apply B ξ η
  have hright (ξ η : ψ.GNS) : inner ℂ ξ (T η) = form π i F ξ η := by
    calc
      inner ℂ ξ (T η) = conj (inner ℂ (T η) ξ) := (inner_conj_symm _ _).symm
      _ = conj (form π i F η ξ) := congrArg conj (hleft η ξ)
      _ = form π i F ξ η := by rw [form_hermitian π i hi F ξ η]; simp
  have hsa : IsSelfAdjoint T := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro ξ η
    exact (hleft ξ η).trans (hright ξ η).symm
  have hn : ‖T‖ ≤ ‖F‖ := by
    have hB : ‖B‖ ≤ ‖F‖ :=
      (form π i F).mkContinuous₂_norm_le (norm_nonneg F) (form_bound π i F)
    apply T.opNorm_le_bound (norm_nonneg F)
    intro ξ
    change ‖(InnerProductSpace.toDual ℂ ψ.GNS).symm (B ξ)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact B.le_of_opNorm_le hB ξ
  have heval (ξ η : ψ.GNS) : inner ℂ ξ (T η) =
      (F (reCLM.comp (coefficient π i ξ η)) : ℂ) +
        I * (F (imCLM.comp (coefficient π i ξ η)) : ℂ) :=
    (hright ξ η).trans (lift_apply F _)
  have hcanon (x : V) (hx : F = NormedSpace.inclusionInDoubleDual ℝ V x) :
      T = π (i x) := by
    ext η
    apply ext_inner_left ℂ
    intro ξ
    rw [heval, hx]
    change ((inner ℂ ξ (π (i x) η)).re : ℂ) +
      I * ((inner ℂ ξ (π (i x) η)).im : ℂ) = _
    apply Complex.ext <;> simp
  refine ⟨T, ⟨hsa, hn, heval, hcanon⟩, ?_⟩
  intro S hS
  ext η
  apply ext_inner_left ℂ
  intro ξ
  exact (hS.2.2.1 ξ η).trans (heval ξ η).symm

end ActualGNSCoefficientViaExtension

noncomputable section
open scoped ComplexOrder ComplexConjugate
open Complex InnerProductSpace
namespace ActualGNSFamilyNorming

open ActualGNSCoefficientViaExtension
open D5.S3.QuantumStates.GNSCompatibleStateExtension
open D5.S3.Quantum.Algebra.CentralPositiveFunctionalExtension

variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
private def selected (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →ₚ[ℂ] ℂ) (F : StrongDual ℝ (StrongDual ℝ V)) :
    ψ.GNS →L[ℂ] ψ.GNS :=
  Classical.choose (original_gns_exists_unique i hi ψ F)

private lemma selected_inner (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →ₚ[ℂ] ℂ) (F : StrongDual ℝ (StrongDual ℝ V)) (ξ η : ψ.GNS) :
    inner ℂ ξ (selected i hi ψ F η) =
      (F (reCLM.comp (coefficient ψ.gnsStarAlgHom i ξ η)) : ℂ) +
        I * (F (imCLM.comp (coefficient ψ.gnsStarAlgHom i ξ η)) : ℂ) :=
  (Classical.choose_spec (original_gns_exists_unique i hi ψ F)).1.2.2.1 ξ η
/-- Real linearity in the original bidual, for each fixed actual positive GNS.
The positive functional is an index, not a linear variable. -/
def gnsLinear (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →ₚ[ℂ] ℂ) :
    StrongDual ℝ (StrongDual ℝ V) →ₗ[ℝ] (ψ.GNS →L[ℂ] ψ.GNS) where
  toFun := selected i hi ψ
  map_add' F G := by
    ext η
    apply ext_inner_left ℂ
    intro ξ
    change inner ℂ ξ (selected i hi ψ (F + G) η) =
      inner ℂ ξ (selected i hi ψ F η + selected i hi ψ G η)
    rw [inner_add_right, selected_inner, selected_inner, selected_inner]
    simp only [ContinuousLinearMap.add_apply, Complex.ofReal_add]
    ring
  map_smul' r F := by
    ext η
    apply ext_inner_left ℂ
    intro ξ
    change inner ℂ ξ (selected i hi ψ (r • F) η) =
      inner ℂ ξ (r • selected i hi ψ F η)
    rw [← Complex.coe_smul, inner_smul_right, selected_inner, selected_inner]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
/-- The real-linear map retains the self-adjoint coefficient specification. -/
private theorem gnsLinear_spec (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →ₚ[ℂ] ℂ) (F : StrongDual ℝ (StrongDual ℝ V)) :
    IsSelfAdjoint (gnsLinear i hi ψ F) ∧ ‖gnsLinear i hi ψ F‖ ≤ ‖F‖ ∧
      (∀ ξ η, inner ℂ ξ (gnsLinear i hi ψ F η) =
        (F (reCLM.comp (coefficient ψ.gnsStarAlgHom i ξ η)) : ℂ) +
          I * (F (imCLM.comp (coefficient ψ.gnsStarAlgHom i ξ η)) : ℂ)) ∧
      (∀ x : V, F = NormedSpace.inclusionInDoubleDual ℝ V x →
        gnsLinear i hi ψ F = ψ.gnsStarAlgHom (i x)) :=
  (Classical.choose_spec (original_gns_exists_unique i hi ψ F)).1
private lemma vacuum_inner (ψ : A →ₚ[ℂ] ℂ) (a : A) :
    inner ℂ (cyclicVector ψ) (ψ.gnsStarAlgHom a (cyclicVector ψ)) = ψ a := by
  change inner ℂ ((ψ.toPreGNS 1) : ψ.GNS)
    (ψ.gnsNonUnitalStarAlgHom a ((ψ.toPreGNS 1) : ψ.GNS)) = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
    UniformSpace.Completion.inner_coe]
  simp [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.leftMulMapPreGNS]

private lemma vacuum_norm_sq (ψ : A →ₚ[ℂ] ℂ) :
    ‖cyclicVector ψ‖ ^ 2 = (ψ 1).re := by
  change ‖((ψ.toPreGNS 1) : ψ.GNS)‖ ^ 2 = (ψ 1).re
  rw [UniformSpace.Completion.norm_coe]
  have h := congrArg Complex.re (ψ.preGNS_norm_sq (ψ.toPreGNS 1))
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul] using h

/-- Actual restriction of a positive continuous ambient functional to original labels. -/
def restriction (i : V →ₗᵢ[ℝ] A) (ψ : A →P[ℂ] ℂ) : StrongDual ℝ V :=
  reCLM.comp ((ψ.toContinuousLinearMap.restrictScalars ℝ).comp i.toContinuousLinearMap)
private lemma vacuum_read (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →P[ℂ] ℂ) (F : StrongDual ℝ (StrongDual ℝ V)) :
    (inner ℂ (cyclicVector ψ.toPositiveLinearMap)
      (gnsLinear i hi ψ.toPositiveLinearMap F
        (cyclicVector ψ.toPositiveLinearMap))).re = F (restriction i ψ) := by
  have hc : reCLM.comp (coefficient ψ.toPositiveLinearMap.gnsStarAlgHom i
      (cyclicVector ψ.toPositiveLinearMap) (cyclicVector ψ.toPositiveLinearMap)) =
      restriction i ψ := by
    ext x
    change (inner ℂ (cyclicVector ψ.toPositiveLinearMap)
      (ψ.toPositiveLinearMap.gnsStarAlgHom (i x)
        (cyclicVector ψ.toPositiveLinearMap))).re = (ψ (i x)).re
    exact congrArg Complex.re (vacuum_inner ψ.toPositiveLinearMap (i x))
  have h := congrArg Complex.re ((gnsLinear_spec i hi ψ.toPositiveLinearMap F).2.2.1
    (cyclicVector ψ.toPositiveLinearMap) (cyclicVector ψ.toPositiveLinearMap))
  simpa [hc] using h
private lemma vacuum_bound (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →P[ℂ] ℂ) (F : StrongDual ℝ (StrongDual ℝ V))
    (r : ℝ) (hT : ‖gnsLinear i hi ψ.toPositiveLinearMap F‖ ≤ r) :
    ‖F (restriction i ψ)‖ ≤ r * (ψ 1).re := by
  let Ω := cyclicVector ψ.toPositiveLinearMap
  let T := gnsLinear i hi ψ.toPositiveLinearMap F
  have hm : ‖Ω‖ ^ 2 = (ψ 1).re := vacuum_norm_sq ψ.toPositiveLinearMap
  have hread : (inner ℂ Ω (T Ω)).re = F (restriction i ψ) := vacuum_read i hi ψ F
  calc
    ‖F (restriction i ψ)‖ = |(inner ℂ Ω (T Ω)).re| := by
      rw [hread]
      exact Real.norm_eq_abs _
    _ ≤ ‖inner ℂ Ω (T Ω)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖Ω‖ * ‖T Ω‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖T‖ * ‖Ω‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm Ω) (norm_nonneg Ω)
    _ = ‖T‖ * ‖Ω‖ ^ 2 := by ring
    _ ≤ r * ‖Ω‖ ^ 2 := mul_le_mul_of_nonneg_right hT (sq_nonneg ‖Ω‖)
    _ = r * (ψ 1).re := by rw [hm]
/-- The bounded inverse uses the same actual inverse function and inherited norms. -/

private lemma positive_pair (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (φ : StrongDual ℝ V) :
    ∃ ψplus ψminus : A →P[ℂ] ℂ,
      φ = restriction i ψplus - restriction i ψminus ∧
      (ψplus 1).re + (ψminus 1).re = ‖φ‖ := by
  let e := i.equivRange
  let φ' : StrongDual ℝ i.toLinearMap.range :=
    φ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hn : ‖φ'‖ = ‖φ‖ := by
    apply le_antisymm
    · apply φ'.opNorm_le_bound (norm_nonneg φ)
      intro z
      change ‖φ (e.symm z)‖ ≤ ‖φ‖ * ‖z‖
      simpa only [e.symm.norm_map] using φ.le_opNorm (e.symm z)
    · apply φ.opNorm_le_bound (norm_nonneg φ')
      intro x
      have he : φ' (e x) = φ x := by simp [φ']
      calc
        ‖φ x‖ = ‖φ' (e x)‖ := congrArg norm he.symm
        _ ≤ ‖φ'‖ * ‖e x‖ := φ'.le_opNorm (e x)
        _ = ‖φ'‖ * ‖x‖ := by rw [e.norm_map]
  have hX : ∀ z : i.toLinearMap.range, IsSelfAdjoint (z : A) := by
    intro z
    obtain ⟨x, hx⟩ := z.property
    exact hx ▸ hi x
  obtain ⟨ψplus, ψminus, hagree, hmass⟩ :=
    exists_positive_extensions_norm_additive i.toLinearMap.range hX φ'
  refine ⟨ψplus, ψminus, ?_, hmass.trans hn⟩
  ext x
  have h := hagree (e x)
  change φ (e.symm (e x)) = (ψplus (i x)).re - (ψminus (i x)).re at h
  simpa [restriction] using h
/-- All radii, all unnormalized positive continuous functionals, original bidual.
No positive mass is divided out, including when either or both masses are zero. -/
private theorem all_positive_continuous_norming
    (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (F : StrongDual ℝ (StrongDual ℝ V)) (r : ℝ) (hr : 0 ≤ r) :
    (∀ ψ : A →P[ℂ] ℂ, ‖gnsLinear i hi ψ.toPositiveLinearMap F‖ ≤ r) ↔
      ‖F‖ ≤ r := by
  constructor
  · intro hall
    apply F.opNorm_le_bound hr
    intro φ
    obtain ⟨ψplus, ψminus, hφ, hmass⟩ := positive_pair i hi φ
    calc
      ‖F φ‖ = ‖F (restriction i ψplus) - F (restriction i ψminus)‖ := by
        rw [hφ, map_sub]
      _ ≤
          ‖F (restriction i ψplus)‖ + ‖F (restriction i ψminus)‖ := norm_sub_le _ _
      _ ≤ r * (ψplus 1).re + r * (ψminus 1).re :=
        add_le_add (vacuum_bound i hi ψplus F r (hall ψplus))
          (vacuum_bound i hi ψminus F r (hall ψminus))
      _ = r * ‖φ‖ := by rw [← mul_add, hmass]
  · intro hF ψ
    exact (gnsLinear_spec i hi ψ.toPositiveLinearMap F).2.1.trans hF

/-- Positive linear functionals, including all continuous ones, give the same radii. -/
private theorem all_positive_norming (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (F : StrongDual ℝ (StrongDual ℝ V)) (r : ℝ) (hr : 0 ≤ r) :
    (∀ ψ : A →ₚ[ℂ] ℂ, ‖gnsLinear i hi ψ F‖ ≤ r) ↔ ‖F‖ ≤ r := by
  constructor
  · intro hall
    exact (all_positive_continuous_norming i hi F r hr).mp
      (fun ψ => hall ψ.toPositiveLinearMap)
  · intro hF ψ
    exact (gnsLinear_spec i hi ψ F).2.1.trans hF

end ActualGNSFamilyNorming

noncomputable section
open scoped ComplexOrder ComplexConjugate
open Complex InnerProductSpace
open ActualGNSCoefficientViaExtension

namespace ActualGNSJordanProduct
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
/-- Bounded scalar rows: row S φ x y = φ (S x y). -/
def rows (S : V →L[ℝ] V →L[ℝ] V) :
    StrongDual ℝ V →L[ℝ] V →L[ℝ] StrongDual ℝ V :=
  ContinuousLinearMap.precompL V (ContinuousLinearMap.compL ℝ V V ℝ).flip S

/-- The complex-valued original rows have the same original V twice. -/
def complexRows (S : V →L[ℝ] V →L[ℝ] V) :
    (V →L[ℝ] ℂ) →L[ℝ] V →L[ℝ] V →L[ℝ] ℂ :=
  ContinuousLinearMap.precompL V (ContinuousLinearMap.compL ℝ V V ℂ).flip S

/-- Genuine bounded first Arens extension; no exchange of its two evaluations. -/
def arens (S : V →L[ℝ] V →L[ℝ] V)
    (F G : StrongDual ℝ (StrongDual ℝ V)) : StrongDual ℝ (StrongDual ℝ V) :=
  F.comp ((ContinuousLinearMap.compL ℝ V (StrongDual ℝ V) ℝ G).comp (rows S))
private lemma arens_apply (S : V →L[ℝ] V →L[ℝ] V)
    (F G : StrongDual ℝ (StrongDual ℝ V)) (φ : StrongDual ℝ V) :
    arens S F G φ = F (G.comp (rows S φ)) := rfl

/-- Real-linear, complex-valued evaluation of actual real and imaginary functionals. -/
def evalC (F : StrongDual ℝ (StrongDual ℝ V)) : (V →L[ℝ] ℂ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (F.comp (Complex.reCLM.postcomp V)) +
    I • Complex.ofRealCLM.comp (F.comp (Complex.imCLM.postcomp V))
private lemma evalC_apply (F : StrongDual ℝ (StrongDual ℝ V)) (c : V →L[ℝ] ℂ) :
    evalC F c = (F (reCLM.comp c) : ℂ) + I * (F (imCLM.comp c) : ℂ) := rfl

/-- Both real components retain exactly the same F-outside-G evaluation order. -/
private lemma evalC_arens (S : V →L[ℝ] V →L[ℝ] V)
    (F G : StrongDual ℝ (StrongDual ℝ V)) (c : V →L[ℝ] ℂ) :
    evalC (arens S F G) c = evalC F ((evalC G).comp (complexRows S c)) := by
  have hr : reCLM.comp ((evalC G).comp (complexRows S c)) =
      G.comp (rows S (reCLM.comp c)) := by
    ext x
    change (evalC G (complexRows S c x)).re = G (rows S (reCLM.comp c) x)
    rw [evalC_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero]
    apply congrArg G
    ext y
    rfl
  have hi : imCLM.comp ((evalC G).comp (complexRows S c)) =
      G.comp (rows S (imCLM.comp c)) := by
    ext x
    change (evalC G (complexRows S c x)).im = G (rows S (imCLM.comp c) x)
    rw [evalC_apply]
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      zero_add]
    apply congrArg G
    ext y
    rfl
  rw [evalC_apply, evalC_apply, hr, hi, arens_apply, arens_apply]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Select the operator determined by the original coefficient functional. -/
def operator (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →ₚ[ℂ] ℂ) (F : StrongDual ℝ (StrongDual ℝ V)) : ψ.GNS →L[ℂ] ψ.GNS :=
  Classical.choose (original_gns_exists_unique i hi ψ F)

private lemma operator_sa (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →ₚ[ℂ] ℂ) (F : StrongDual ℝ (StrongDual ℝ V)) :
    IsSelfAdjoint (operator i hi ψ F) :=
  (Classical.choose_spec (original_gns_exists_unique i hi ψ F)).1.1

private lemma operator_coeff (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →ₚ[ℂ] ℂ) (F : StrongDual ℝ (StrongDual ℝ V)) (ξ η : ψ.GNS) :
    inner ℂ ξ (operator i hi ψ F η) =
      evalC F (coefficient ψ.gnsStarAlgHom i ξ η) :=
  (Classical.choose_spec (original_gns_exists_unique i hi ψ F)).1.2.2.1 ξ η
/-- Fix x first. Each of its two ordered factors becomes an original coefficient. -/
private lemma coefficient_rows (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (ψ : A →ₚ[ℂ] ℂ) (ξ η : ψ.GNS) (x : V) :
    complexRows S (coefficient ψ.gnsStarAlgHom i ξ η) x =
      (1 / 2 : ℝ) •
        (coefficient ψ.gnsStarAlgHom i (ψ.gnsStarAlgHom (i x) ξ) η +
         coefficient ψ.gnsStarAlgHom i ξ (ψ.gnsStarAlgHom (i x) η)) := by
  ext y
  change inner ℂ ξ (ψ.gnsStarAlgHom (i (S x y)) η) =
    (1 / 2 : ℝ) •
      (inner ℂ (ψ.gnsStarAlgHom (i x) ξ) (ψ.gnsStarAlgHom (i y) η) +
       inner ℂ ξ (ψ.gnsStarAlgHom (i y) (ψ.gnsStarAlgHom (i x) η)))
  have hr (r : ℝ) (a : A) : ψ.gnsStarAlgHom (r • a) =
      r • ψ.gnsStarAlgHom a :=
    (ψ.gnsStarAlgHom.toAlgHom.restrictScalars ℝ).toLinearMap.map_smul r a
  rw [hS, hr]
  simp only [map_add, map_mul, smul_apply, add_apply, mul_apply_eq_comp,
    inner_smul_right_eq_smul, inner_add_right]
  exact congrArg
    (fun z : ℂ => (1 / 2 : ℝ) •
      (z + inner ℂ ξ (ψ.gnsStarAlgHom (i y) (ψ.gnsStarAlgHom (i x) η))))
    (((hi x).map ψ.gnsStarAlgHom).isSymmetric ξ (ψ.gnsStarAlgHom (i y) η)).symm
/-- Apply G only after the original row identity; use actual selfadjoint GNS operators. -/
private lemma evaluated_rows (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (ψ : A →ₚ[ℂ] ℂ) (G : StrongDual ℝ (StrongDual ℝ V)) (ξ η : ψ.GNS) :
    (evalC G).comp (complexRows S (coefficient ψ.gnsStarAlgHom i ξ η)) =
      (1 / 2 : ℝ) •
        (coefficient ψ.gnsStarAlgHom i ξ (operator i hi ψ G η) +
         coefficient ψ.gnsStarAlgHom i (operator i hi ψ G ξ) η) := by
  ext x
  change evalC G (complexRows S (coefficient ψ.gnsStarAlgHom i ξ η) x) = _
  rw [coefficient_rows i hi S hS ψ ξ η x, map_smul, map_add,
    ← operator_coeff i hi ψ G, ← operator_coeff i hi ψ G]
  change (1 / 2 : ℝ) •
      (inner ℂ (ψ.gnsStarAlgHom (i x) ξ) (operator i hi ψ G η) +
       inner ℂ ξ (operator i hi ψ G (ψ.gnsStarAlgHom (i x) η))) =
    (1 / 2 : ℝ) •
      (inner ℂ ξ (ψ.gnsStarAlgHom (i x) (operator i hi ψ G η)) +
       inner ℂ (operator i hi ψ G ξ) (ψ.gnsStarAlgHom (i x) η))
  exact congrArg (fun z : ℂ => (1 / 2 : ℝ) • z)
    (congrArg₂ (fun z w : ℂ => z + w)
      (((hi x).map ψ.gnsStarAlgHom).isSymmetric ξ (operator i hi ψ G η))
      ((operator_sa i hi ψ G).isSymmetric ξ (ψ.gnsStarAlgHom (i x) η)).symm)
/-- All complex coefficients of the actual first Arens product, on arbitrary V. -/
private theorem arens_coefficients (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (ψ : A →ₚ[ℂ] ℂ) (F G : StrongDual ℝ (StrongDual ℝ V)) (ξ η : ψ.GNS) :
    inner ℂ ξ (operator i hi ψ (arens S F G) η) =
      inner ℂ ξ (((1 / 2 : ℝ) •
        (operator i hi ψ F * operator i hi ψ G +
         operator i hi ψ G * operator i hi ψ F)) η) := by
  rw [operator_coeff, evalC_arens, evaluated_rows i hi S hS ψ G ξ η,
    map_smul, map_add, ← operator_coeff i hi ψ F, ← operator_coeff i hi ψ F]
  simp only [smul_apply, add_apply, mul_apply_eq_comp,
    inner_smul_right_eq_smul, inner_add_right]
  exact congrArg
    (fun z : ℂ => (1 / 2 : ℝ) •
      (inner ℂ ξ (operator i hi ψ F (operator i hi ψ G η)) + z))
    ((operator_sa i hi ψ G).isSymmetric ξ (operator i hi ψ F η))

/-- Equality of the selected actual operators, established by all coefficients. -/
private theorem arens_operator (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (ψ : A →ₚ[ℂ] ℂ) (F G : StrongDual ℝ (StrongDual ℝ V)) :
    operator i hi ψ (arens S F G) = (1 / 2 : ℝ) •
      (operator i hi ψ F * operator i hi ψ G +
       operator i hi ψ G * operator i hi ψ F) := by
  ext η
  apply ext_inner_left ℂ
  intro ξ
  exact arens_coefficients i hi S hS ψ F G ξ η

end ActualGNSJordanProduct


noncomputable section
set_option autoImplicit false
open scoped ComplexOrder ComplexConjugate
open Complex InnerProductSpace

set_option maxSynthPendingDepth 8

namespace ActualBidualJordanLaws

open ActualGNSCoefficientViaExtension
open ActualGNSFamilyNorming
open ActualGNSJordanProduct

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Both suppliers represent exactly the same coefficient functional. -/
private theorem same_family (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →ₚ[ℂ] ℂ) (F : StrongDual ℝ (StrongDual ℝ V)) :
    gnsLinear i hi ψ F = operator i hi ψ F := by
  ext η
  apply ext_inner_left ℂ
  intro ξ
  exact ((gnsLinear_spec i hi ψ F).2.2.1 ξ η).trans
    (operator_coeff i hi ψ F ξ η).symm

/-- All positive continuous readings separate the original real bidual. -/
private theorem family_ext (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    {F G : StrongDual ℝ (StrongDual ℝ V)}
    (h : ∀ ψ : A →P[ℂ] ℂ,
      gnsLinear i hi ψ.toPositiveLinearMap F =
        gnsLinear i hi ψ.toPositiveLinearMap G) : F = G := by
  have hz : ‖F - G‖ ≤ 0 :=
    (all_positive_continuous_norming i hi (F - G) 0 le_rfl).mp (by
      intro ψ
      rw [map_sub, h ψ, sub_self, norm_zero])
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg (F - G))))

/-- Product representation in the very family used by norm detection. -/
private theorem family_product (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (ψ : A →ₚ[ℂ] ℂ) (F G : StrongDual ℝ (StrongDual ℝ V)) :
    gnsLinear i hi ψ (arens S F G) = (1 / 2 : ℝ) •
      (gnsLinear i hi ψ F * gnsLinear i hi ψ G +
       gnsLinear i hi ψ G * gnsLinear i hi ψ F) := by
  simpa only [same_family] using arens_operator i hi S hS ψ F G

/-- Squaring uses the associative operator square in the same representation. -/
private theorem family_square (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (ψ : A →ₚ[ℂ] ℂ) (F : StrongDual ℝ (StrongDual ℝ V)) :
    gnsLinear i hi ψ (arens S F F) =
      gnsLinear i hi ψ F * gnsLinear i hi ψ F := by
  rw [family_product i hi S hS]
  module

/-- The order of evaluation is retained; symmetry is derived by separation. -/

private theorem arens_add_left (S : V →L[ℝ] V →L[ℝ] V)
    (F G H : StrongDual ℝ (StrongDual ℝ V)) :
    arens S (F + G) H = arens S F H + arens S G H := by
  ext φ
  rfl

private theorem arens_smul_left (S : V →L[ℝ] V →L[ℝ] V)
    (r : ℝ) (F G : StrongDual ℝ (StrongDual ℝ V)) :
    arens S (r • F) G = r • arens S F G := by
  ext φ
  rfl

private theorem arens_add_right (S : V →L[ℝ] V →L[ℝ] V)
    (F G H : StrongDual ℝ (StrongDual ℝ V)) :
    arens S F (G + H) = arens S F G + arens S F H := by
  ext φ
  have hr : (G + H).comp (rows S φ) = G.comp (rows S φ) + H.comp (rows S φ) := by
    ext x
    rfl
  simp only [arens_apply, hr, map_add, ContinuousLinearMap.add_apply]

private theorem arens_smul_right (S : V →L[ℝ] V →L[ℝ] V)
    (r : ℝ) (F G : StrongDual ℝ (StrongDual ℝ V)) :
    arens S F (r • G) = r • arens S F G := by
  ext φ
  have hr : (r • G).comp (rows S φ) = r • G.comp (rows S φ) := by
    ext x
    rfl
  simp only [arens_apply, hr, map_smul, ContinuousLinearMap.smul_apply,
    RingHom.id_apply]

/-- The exact first Arens function, bundled only as a real bilinear map. -/
def arensBilinear (S : V →L[ℝ] V →L[ℝ] V) :
    StrongDual ℝ (StrongDual ℝ V) →ₗ[ℝ]
      StrongDual ℝ (StrongDual ℝ V) →ₗ[ℝ] StrongDual ℝ (StrongDual ℝ V) where
  toFun F := {
    toFun := arens S F
    map_add' G H := arens_add_right S F G H
    map_smul' r G := arens_smul_right S r F G }
  map_add' F G := by
    apply LinearMap.ext
    intro H
    exact arens_add_left S F G H
  map_smul' r F := by
    apply LinearMap.ext
    intro G
    exact arens_smul_left S r F G

/-- Contractivity is read in every actual positive GNS, then transferred back. -/
private theorem arens_norm_le (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (F G : StrongDual ℝ (StrongDual ℝ V)) :
    ‖arens S F G‖ ≤ ‖F‖ * ‖G‖ := by
  apply (all_positive_continuous_norming i hi (arens S F G)
    (‖F‖ * ‖G‖) (mul_nonneg (norm_nonneg F) (norm_nonneg G))).mp
  intro ψ
  rw [family_product i hi S hS]
  let T := gnsLinear i hi ψ.toPositiveLinearMap F
  let U := gnsLinear i hi ψ.toPositiveLinearMap G
  change ‖(1 / 2 : ℝ) • (T * U + U * T)‖ ≤ ‖F‖ * ‖G‖
  calc
    ‖(1 / 2 : ℝ) • (T * U + U * T)‖ = (1 / 2 : ℝ) * ‖T * U + U * T‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖T‖ * ‖U‖ + ‖U‖ * ‖T‖) :=
      mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)))
        (by norm_num)
    _ = ‖T‖ * ‖U‖ := by ring
    _ ≤ ‖F‖ * ‖G‖ := mul_le_mul
      (gnsLinear_spec i hi ψ.toPositiveLinearMap F).2.1
      (gnsLinear_spec i hi ψ.toPositiveLinearMap G).2.1
      (norm_nonneg U) (norm_nonneg F)

/-- No new bidual product: this bounded map has the same underlying function. -/

private theorem norm_sq_le_of_family_sq_le (i : V →ₗᵢ[ℝ] A)
    (hi : ∀ x, IsSelfAdjoint (i x)) (F : StrongDual ℝ (StrongDual ℝ V))
    (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ ψ : A →P[ℂ] ℂ, ‖gnsLinear i hi ψ.toPositiveLinearMap F‖ ^ 2 ≤ r) :
    ‖F‖ ^ 2 ≤ r := by
  have hF : ‖F‖ ≤ Real.sqrt r :=
    (all_positive_continuous_norming i hi F (Real.sqrt r) (Real.sqrt_nonneg r)).mp (by
      intro ψ
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg r)).mp
      simpa only [Real.sq_sqrt hr] using h ψ)
  have hF2 := (sq_le_sq₀ (norm_nonneg F) (Real.sqrt_nonneg r)).mpr hF
  simpa only [Real.sq_sqrt hr] using hF2

/-- The original canonical bidual norm is a JB square norm. -/
private theorem arens_square_norm (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (F : StrongDual ℝ (StrongDual ℝ V)) : ‖arens S F F‖ = ‖F‖ ^ 2 := by
  apply le_antisymm
  · simpa only [pow_two] using arens_norm_le i hi S hS F F
  · apply norm_sq_le_of_family_sq_le i hi F ‖arens S F F‖ (norm_nonneg (arens S F F))
    intro ψ
    calc
      ‖gnsLinear i hi ψ.toPositiveLinearMap F‖ ^ 2 =
          ‖gnsLinear i hi ψ.toPositiveLinearMap F *
            gnsLinear i hi ψ.toPositiveLinearMap F‖ :=
        (gnsLinear_spec i hi ψ.toPositiveLinearMap F).1.norm_mul_self.symm
      _ = ‖gnsLinear i hi ψ.toPositiveLinearMap (arens S F F)‖ :=
        congrArg norm (family_square i hi S hS ψ.toPositiveLinearMap F).symm
      _ ≤ ‖arens S F F‖ := (gnsLinear_spec i hi ψ.toPositiveLinearMap _).2.1

end ActualBidualJordanLaws


noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 64
set_option maxRecDepth 4096

namespace D5.S3.Quantum.Algebra.ActualCommonBidualRoot

open ActualGNSFamilyNorming ActualGNSJordanProduct ActualBidualJordanLaws
open D5.S3.Topology.JBAlgebra
open Filter _root_.Topology
open scoped Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local notation "M" => StrongDual ℝ (StrongDual ℝ V)

/-- Positivity is exactly positivity of the actual canonical operator readings. -/
def Positive (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x)) (F : M) : Prop :=
  ∀ ψ : A →ₚ[ℂ] ℂ, 0 ≤ gnsLinear i hi ψ F

/-- No independent positivity interface: these are the same quadratic forms. -/
private theorem positive_iff_quadratic (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (F : M) : Positive i hi F ↔
      ∀ (ψ : A →ₚ[ℂ] ℂ) (v : ψ.GNS),
        0 ≤ (inner ℂ v (gnsLinear i hi ψ F v)).re := by
  constructor
  · intro h ψ v
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (h ψ)).re_inner_nonneg_right v
  · intro h ψ
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    refine ⟨(gnsLinear_spec i hi ψ F).1.isSymmetric, ?_⟩
    intro v
    change 0 ≤ RCLike.re (inner ℂ (gnsLinear i hi ψ F v) v)
    rw [inner_re_symm]
    exact h ψ v

/-- Boundedness gives continuity on the canonical bidual norm. -/
def familyContinuous (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (ψ : A →ₚ[ℂ] ℂ) : M →L[ℝ] (ψ.GNS →L[ℂ] ψ.GNS) :=
  (gnsLinear i hi ψ).mkContinuous 1 (fun F => by
    simpa only [one_mul] using (gnsLinear_spec i hi ψ F).2.1)

/-- The zeroth power uses the literal original unit. -/
private theorem family_unit (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (u : V) (hu : i u = 1) (ψ : A →ₚ[ℂ] ℂ) :
    gnsLinear i hi ψ (NormedSpace.inclusionInDoubleDual ℝ V u) = 1 := by
  rw [(gnsLinear_spec i hi ψ _).2.2.2 u rfl, hu, map_one]

/-- Existing JB powers are sent to associative powers in every same-ψ reading. -/
private theorem family_power (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (u : V) (hu : i u = 1) (F : M) (ψ : A →ₚ[ℂ] ℂ) (n : ℕ) :
    gnsLinear i hi ψ
      (npow (arensBilinear S) (NormedSpace.inclusionInDoubleDual ℝ V u) F n) =
        (gnsLinear i hi ψ F) ^ n := by
  induction n with
  | zero => simpa only [npow, pow_zero] using family_unit i hi u hu ψ
  | succ n ih =>
    change gnsLinear i hi ψ (arens S F
      (npow (arensBilinear S) (NormedSpace.inclusionInDoubleDual ℝ V u) F n)) = _
    rw [family_product i hi S hS, ih, ← pow_succ', ← pow_succ]
    module

/-- Finite real polynomial evaluation, without a nonassociative algebra instance. -/
def polynomial (S : V →L[ℝ] V →L[ℝ] V) (u : V) (F : M) (q : ℝ[X]) : M :=
  ∑ n ∈ Finset.range (q.natDegree + 1), q.coeff n •
    npow (arensBilinear S) (NormedSpace.inclusionInDoubleDual ℝ V u) F n

/-- One bidual polynomial, simultaneously in every actual GNS representation. -/
private theorem family_polynomial (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (u : V) (hu : i u = 1) (F : M) (q : ℝ[X]) (ψ : A →ₚ[ℂ] ℂ) :
    gnsLinear i hi ψ (polynomial S u F q) = Polynomial.aeval (gnsLinear i hi ψ F) q := by
  simp only [polynomial, map_sum, map_smul, RingHom.id_apply,
    family_power i hi S hS u hu F ψ]
  exact (Polynomial.aeval_eq_sum_range (gnsLinear i hi ψ F)).symm

/-- These approximants stay in the existing closed one-generator subspace. -/
private theorem polynomial_mem_generated (S : V →L[ℝ] V →L[ℝ] V) (u : V) (F : M)
    (q : ℝ[X]) : polynomial S u F q ∈
      generated (arensBilinear S) (NormedSpace.inclusionInDoubleDual ℝ V u) F := by
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)

/-- The real spectra all lie in a single scalar interval; no NormOneClass or
nontriviality premise is needed for zero GNS spaces. -/
private theorem spectrum_interval (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (F : M) (hF : Positive i hi F) (ψ : A →ₚ[ℂ] ℂ) {t : ℝ}
    (ht : t ∈ spectrum ℝ (gnsLinear i hi ψ F)) : t ∈ Set.Icc 0 ‖F‖ := by
  refine ⟨spectrum_nonneg_of_nonneg (hF ψ) ht, ?_⟩
  exact (Real.le_norm_self t).trans
    ((IsometricContinuousFunctionalCalculus.norm_spectrum_le (gnsLinear i hi ψ F)
      ht (gnsLinear_spec i hi ψ F).1).trans (gnsLinear_spec i hi ψ F).2.1)

/-- A scalar uniform error controls the very same operator polynomial error. -/
private theorem operator_error (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (F : M) (hF : Positive i hi F) (q : ℝ[X]) (ε : ℝ) (hε : 0 ≤ ε)
    (hq : ∀ t ∈ Set.Icc 0 ‖F‖, |q.eval t - Real.sqrt t| ≤ ε)
    (ψ : A →ₚ[ℂ] ℂ) :
    ‖Polynomial.aeval (gnsLinear i hi ψ F) q - cfc Real.sqrt (gnsLinear i hi ψ F)‖ ≤ ε := by
  rw [← cfc_polynomial q (gnsLinear i hi ψ F) (gnsLinear_spec i hi ψ F).1,
    ← cfc_sub q.eval Real.sqrt (gnsLinear i hi ψ F)
      q.continuousOn Real.continuous_sqrt.continuousOn]
  apply norm_cfc_le hε
  intro t ht
  simpa only [Real.norm_eq_abs] using hq t (spectrum_interval i hi F hF ψ ht)

/-- The error schedule is fixed independently of every positive reading. -/
def error (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- A single scalar polynomial sequence on the original norm interval. -/
def sqrtPolynomials (R : ℝ) (n : ℕ) : ℝ[X] :=
  Classical.choose (exists_polynomial_near_of_continuousOn 0 R Real.sqrt
    Real.continuous_sqrt.continuousOn (error n) (by unfold error; positivity))

private theorem sqrtPolynomials_error (R : ℝ) (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 R) :
    |(sqrtPolynomials R n).eval t - Real.sqrt t| ≤ error n :=
  le_of_lt (Classical.choose_spec (exists_polynomial_near_of_continuousOn 0 R Real.sqrt
    Real.continuous_sqrt.continuousOn (error n) (by unfold error; positivity)) t ht)

/-- The same error estimate holds in every representation, with no ψ-dependent
choice of a preimage or polynomial. -/
private theorem approximant_error (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (u : V) (hu : i u = 1) (F : M) (hF : Positive i hi F)
    (n : ℕ) (ψ : A →ₚ[ℂ] ℂ) :
    ‖gnsLinear i hi ψ (polynomial S u F (sqrtPolynomials ‖F‖ n)) -
      cfc Real.sqrt (gnsLinear i hi ψ F)‖ ≤ error n := by
  rw [family_polynomial i hi S hS u hu]
  exact operator_error i hi F hF _ _ (by unfold error; positivity)
    (sqrtPolynomials_error ‖F‖ n) ψ

/-- Joint norm detection turns uniform same-family operator estimates into a
Cauchy sequence in the actual original bidual, rather than in a family product. -/
private theorem approximants_cauchy (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (u : V) (hu : i u = 1) (F : M) (hF : Positive i hi F) :
    CauchySeq (fun n => polynomial S u F (sqrtPolynomials ‖F‖ n)) := by
  have he : Tendsto error atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp he (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmε : error m < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ error m by
      unfold error; positivity)] using hN m hm
  have hnε : error n < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ error n by
      unfold error; positivity)] using hN n hn
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (b := error m + error n) ?_ (by linarith)
  apply (all_positive_norming i hi _ _ (by unfold error; positivity)).mp
  intro ψ
  rw [map_sub]
  calc
    ‖gnsLinear i hi ψ (polynomial S u F (sqrtPolynomials ‖F‖ m)) -
        gnsLinear i hi ψ (polynomial S u F (sqrtPolynomials ‖F‖ n))‖ ≤
      ‖gnsLinear i hi ψ (polynomial S u F (sqrtPolynomials ‖F‖ m)) -
        cfc Real.sqrt (gnsLinear i hi ψ F)‖ +
      ‖cfc Real.sqrt (gnsLinear i hi ψ F) -
        gnsLinear i hi ψ (polynomial S u F (sqrtPolynomials ‖F‖ n))‖ :=
      by simpa only [dist_eq_norm] using
        (dist_triangle
          (gnsLinear i hi ψ (polynomial S u F (sqrtPolynomials ‖F‖ m)))
          (cfc Real.sqrt (gnsLinear i hi ψ F))
          (gnsLinear i hi ψ (polynomial S u F (sqrtPolynomials ‖F‖ n))))
    _ ≤ error m + error n := by
      rw [norm_sub_rev (cfc Real.sqrt (gnsLinear i hi ψ F))]
      exact add_le_add (approximant_error i hi S hS u hu F hF m ψ)
        (approximant_error i hi S hS u hu F hF n ψ)

/-- Convergence to the designated operator root is uniform in the same error
schedule. This statement makes no operator-surjectivity assertion. -/
private theorem approximant_readings_tendsto (i : V →ₗᵢ[ℝ] A)
    (hi : ∀ x, IsSelfAdjoint (i x)) (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (u : V) (hu : i u = 1) (F : M) (hF : Positive i hi F) (ψ : A →ₚ[ℂ] ℂ) :
    Tendsto (fun n => gnsLinear i hi ψ (polynomial S u F (sqrtPolynomials ‖F‖ n)))
      atTop (𝓝 (cfc Real.sqrt (gnsLinear i hi ψ F))) := by
  have he : Tendsto error atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp he ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (approximant_error i hi S hS u hu F hF n ψ)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ error n by
    unfold error; positivity)] using hN n hn

/-- The actual common root. Completeness belongs to StrongDual ℝ (StrongDual ℝ V),
not V. One G works for all unnormalized positive ψ on the original domains. -/
theorem exists_common_root (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (u : V) (hu : i u = 1) (F : M) (hF : Positive i hi F) :
    ∃ G : M, arens S G G = F ∧ ‖G‖ ^ 2 = ‖F‖ ∧ Positive i hi G ∧
      G ∈ generated (arensBilinear S) (NormedSpace.inclusionInDoubleDual ℝ V u) F ∧
      ∀ ψ : A →ₚ[ℂ] ℂ, gnsLinear i hi ψ G = cfc Real.sqrt (gnsLinear i hi ψ F) := by
  by_cases hzero : ‖F‖ = 0
  · have hFzero : F = 0 := norm_eq_zero.mp hzero
    subst F
    refine ⟨0, ?_, by simp, ?_, (generated _ _ _).zero_mem, ?_⟩
    · change (arensBilinear S 0) 0 = 0
      simp
    · intro ψ
      simp only [map_zero, le_refl]
    · intro ψ
      simp only [map_zero, cfc_apply_zero, Real.sqrt_zero, map_zero]
  · have hR : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg F) (Ne.symm hzero)
    obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete
      (approximants_cauchy i hi S hS u hu F hF)
    have hfamily (ψ : A →ₚ[ℂ] ℂ) :
        gnsLinear i hi ψ G = cfc Real.sqrt (gnsLinear i hi ψ F) := by
      have hlim := ((familyContinuous i hi ψ).continuous.tendsto G).comp hG
      exact tendsto_nhds_unique hlim
        (approximant_readings_tendsto i hi S hS u hu F hF ψ)
    have hsq : arens S G G = F := by
      apply family_ext i hi
      intro ψ
      rw [family_square i hi S hS, hfamily ψ.toPositiveLinearMap]
      rw [← cfc_mul Real.sqrt Real.sqrt (gnsLinear i hi ψ.toPositiveLinearMap F)
        Real.continuous_sqrt.continuousOn Real.continuous_sqrt.continuousOn]
      calc
        cfc (fun t : ℝ => Real.sqrt t * Real.sqrt t)
            (gnsLinear i hi ψ.toPositiveLinearMap F) =
            cfc (id : ℝ → ℝ) (gnsLinear i hi ψ.toPositiveLinearMap F) := by
          apply cfc_congr
          intro t ht
          exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg
            (hF ψ.toPositiveLinearMap) ht)
        _ = _ := cfc_id ℝ _ (gnsLinear_spec i hi ψ.toPositiveLinearMap F).1
    refine ⟨G, hsq, ?_, ?_, ?_, hfamily⟩
    · rw [← arens_square_norm i hi S hS G, hsq]
    · intro ψ
      rw [hfamily]
      exact cfc_nonneg (fun t ht => Real.sqrt_nonneg t)
    · exact (Submodule.isClosed_topologicalClosure
        (Submodule.span ℝ (Set.range
          (npow (arensBilinear S) (NormedSpace.inclusionInDoubleDual ℝ V u) F)))).mem_of_tendsto
        hG (Filter.Eventually.of_forall (fun n => polynomial_mem_generated S u F _))

/-- The reverse implication is the consumed canonical operator-square identity. -/
theorem quadratic_iff_square (i : V →ₗᵢ[ℝ] A) (hi : ∀ x, IsSelfAdjoint (i x))
    (S : V →L[ℝ] V →L[ℝ] V)
    (hS : ∀ x y, i (S x y) = (1 / 2 : ℝ) • (i x * i y + i y * i x))
    (u : V) (hu : i u = 1) (F : M) :
    (∀ (ψ : A →ₚ[ℂ] ℂ) (v : ψ.GNS),
      0 ≤ (inner ℂ v (gnsLinear i hi ψ F v)).re) ↔ ∃ G : M, arens S G G = F := by
  rw [← positive_iff_quadratic i hi F]
  constructor
  · intro h
    obtain ⟨G, hG, _⟩ := exists_common_root i hi S hS u hu F h
    exact ⟨G, hG⟩
  · rintro ⟨G, rfl⟩ ψ
    rw [family_square i hi S hS]
    exact (gnsLinear_spec i hi ψ G).1.mul_self_nonneg

end D5.S3.Quantum.Algebra.ActualCommonBidualRoot
