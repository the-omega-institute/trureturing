/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform coercivity and the finite trace of the relative covariance roots. -/

import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondPositivity4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondMultipliers4D
import D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
import D5.S3.Quantum.Analysis.TraceClass.GeneralIdeal

/-! The relative covariance and finite trace on complete complex subspaces of the null diamond. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open ContinuousLinearMap HilbertSchmidt
open D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
open scoped ComplexOrder InnerProductSpace NNReal

namespace NullConeGravity

/-- The massive symmetric covariance on the ambient massless reference space. -/
def nullN (M : ℝ) (hM : 0 < M) : H4D →L[ℂ] H4D := 1 + nullT M hM

private theorem nullN_add_J (M : ℝ) (hM : 0 < M) :
    nullN M hM + nullJ = nullA + nullT M hM := by
  unfold nullN nullJ
  abel

/-- The signed positive bounds and compact correction give a uniform positive lower bound. -/
theorem nullN_coercive (M : ℝ) (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : H4D →L[ℂ] H4D) ≤ nullN M hM := by
  have hJ := (nonneg_iff_isPositive.mp nullA_nonneg).isSelfAdjoint.sub (IsSelfAdjoint.one _)
  have hp : 0 ≤ nullN M hM + nullJ := nullN_add_J M hM ▸ nullB_nonneg hM
  exact (hilbertSchmidt_add_one_coercive (nullT_hs M hM) (nullT_selfAdjoint M hM)
    hJ nullJ_ker hp (nullN_sub_J_nonneg hM)).2

-- Elaborate the functional calculus on an abstract Hilbert space before specialization.
private abbrev operatorSqrt {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (A : K →L[ℂ] K) := CFC.sqrt A

private theorem operatorSqrt_nonneg {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (A : K →L[ℂ] K) :
    0 ≤ operatorSqrt A := CFC.sqrt_nonneg A

private theorem operatorSqrt_mul_self {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (A : K →L[ℂ] K) (hA : 0 ≤ A) :
    operatorSqrt A * operatorSqrt A = A := CFC.sqrt_mul_sqrt_self A hA

private theorem operatorSqrt_isUnit_iff {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (A : K →L[ℂ] K) (hA : 0 ≤ A) :
    IsUnit (operatorSqrt A) ↔ IsUnit A := CFC.isUnit_sqrt_iff A hA

variable (V : Submodule ℂ H4D) [CompleteSpace V]

/-- Compression of the symmetric covariance to the chosen complete subspace. -/
def compressedN (M : ℝ) (hM : 0 < M) : V →L[ℂ] V :=
  adjointCongr V.subtypeL (nullN M hM)

/-- The squared massless symmetric norm. -/
def mu0Sq (f : V) : ℝ := ‖f‖ ^ 2

/-- The squared massive symmetric norm. -/
def mumSq (M : ℝ) (hM : 0 < M) (f : V) : ℝ :=
  (⟪f, compressedN V M hM f⟫_ℂ).re

private theorem congr_inner {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (C : K →L[ℂ] H) (A : H →L[ℂ] H) (x y : K) :
    ⟪x, adjointCongr C A y⟫_ℂ = ⟪C x, A (C y)⟫_ℂ := by
  simp only [adjointCongr, comp_apply, adjoint_inner_right]

private theorem lower_form {M c : ℝ} (hM : 0 < M)
    (hc : c • (1 : H4D →L[ℂ] H4D) ≤ nullN M hM) (f : V) :
    c * mu0Sq V f ≤ mumSq V M hM f := by
  have h := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hc)).re_inner_nonneg_right
    (V.subtypeL f)
  change 0 ≤ (⟪V.subtypeL f, (nullN M hM - c • (1 : H4D →L[ℂ] H4D))
    (V.subtypeL f)⟫_ℂ).re at h
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right,
    Complex.sub_re, inner_smul_right_eq_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  have hs : (⟪V.subtypeL f, V.subtypeL f⟫_ℂ).re = ‖f‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (V.subtypeL f)
  rw [hs] at h
  unfold mumSq mu0Sq compressedN
  rw [congr_inner]
  exact sub_nonneg.mp h

/-- The symmetric upper comparison holds with the ambient operator norm. -/
theorem mumSq_le (M : ℝ) (hM : 0 < M) (f : V) :
    mumSq V M hM f ≤ ‖nullN M hM‖ * mu0Sq V f := by
  unfold mumSq mu0Sq compressedN
  rw [congr_inner]
  calc
    _ ≤ ‖V.subtypeL f‖ * ‖nullN M hM (V.subtypeL f)‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    _ ≤ ‖V.subtypeL f‖ * (‖nullN M hM‖ * ‖V.subtypeL f‖) :=
      mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
    _ = _ := by change ‖f‖ * (‖nullN M hM‖ * ‖f‖) = _; ring

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
private theorem compressedN_nonneg (M : ℝ) (hM : 0 < M) :
    0 ≤ compressedN V M hM := by
  obtain ⟨c, hc, hle⟩ := nullN_coercive M hM
  have hzero : 0 ≤ c • (1 : H4D →L[ℂ] H4D) := by
    change 0 ≤ (c : ℂ) • (1 : H4D →L[ℂ] H4D)
    exact nonneg_iff_isPositive.mpr (isPositive_one.smul_of_nonneg (Complex.zero_le_real.mpr hc.le))
  have hn : 0 ≤ nullN M hM := hzero.trans hle
  exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hn).adjoint_conj V.subtypeL)

private theorem compressedN_unit (M : ℝ) (hM : 0 < M) :
    IsUnit (compressedN V M hM) := by
  obtain ⟨c, hc, hle⟩ := nullN_coercive M hM
  let d : ℝ≥0 := ⟨c, hc.le⟩
  apply isUnit_of_forall_le_norm_inner_map _ (c := d) (show 0 < d from hc)
  intro f
  have hf := lower_form V hM hle f
  change c * ‖f‖ ^ 2 ≤ (⟪f, compressedN V M hM f⟫_ℂ).re at hf
  rw [mul_comm]
  refine hf.trans ?_
  change RCLike.re ⟪f, compressedN V M hM f⟫_ℂ ≤ _
  rw [inner_re_symm (𝕜 := ℂ)]
  exact Complex.re_le_norm _

private theorem sqrt_unit (M : ℝ) (hM : 0 < M) :
    IsUnit (operatorSqrt (compressedN V M hM)) :=
  (operatorSqrt_isUnit_iff _ (compressedN_nonneg V M hM)).mpr (compressedN_unit V M hM)

/-- The inverse of the positive square root of the compressed covariance. -/
def invRootN (M : ℝ) (hM : 0 < M) : V →L[ℂ] V :=
  Ring.inverse (operatorSqrt (compressedN V M hM))

/-- Inclusion after changing to the massive reference norm. -/
def referenceMap (M : ℝ) (hM : 0 < M) : V →L[ℂ] H4D :=
  V.subtypeL ∘L invRootN V M hM

/-- The transported massless symmetric covariance. -/
def relativeQ (M : ℝ) (hM : 0 < M) : V →L[ℂ] V :=
  adjointCongr (referenceMap V M hM) (1 : H4D →L[ℂ] H4D)

/-- The transported skew form. -/
def relativeR (M : ℝ) (hM : 0 < M) : V →L[ℂ] V :=
  Complex.I • adjointCongr (referenceMap V M hM) nullJ

/-- The difference of the two positive covariance square roots. -/
def eq71Delta (M : ℝ) (hM : 0 < M) : V →L[ℂ] V :=
  operatorSqrt (relativeQ V M hM - Complex.I • relativeR V M hM) -
    operatorSqrt (1 - Complex.I • relativeR V M hM)

private theorem invRootN_mul_sqrt (M : ℝ) (hM : 0 < M) :
    invRootN V M hM * operatorSqrt (compressedN V M hM) = 1 :=
  Ring.inverse_mul_cancel _ (sqrt_unit V M hM)

private theorem sqrt_mul_invRootN (M : ℝ) (hM : 0 < M) :
    operatorSqrt (compressedN V M hM) * invRootN V M hM = 1 :=
  Ring.mul_inverse_cancel _ (sqrt_unit V M hM)

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
private theorem invRootN_selfAdjoint (M : ℝ) (hM : 0 < M) :
    IsSelfAdjoint (invRootN V M hM) := by
  have hs := (nonneg_iff_isPositive.mp
    (operatorSqrt_nonneg (compressedN V M hM))).isSelfAdjoint
  change star (invRootN V M hM) = _
  have h : star (invRootN V M hM) * operatorSqrt (compressedN V M hM) = 1 := by
    have hh := congrArg star (sqrt_mul_invRootN V M hM)
    simpa only [star_mul, hs.star_eq, star_one] using hh
  exact left_inv_eq_right_inv h (sqrt_mul_invRootN V M hM)

private theorem reference_congr (M : ℝ) (hM : 0 < M) (A : H4D →L[ℂ] H4D) :
    adjointCongr (referenceMap V M hM) A =
      invRootN V M hM * adjointCongr V.subtypeL A * invRootN V M hM := by
  have hd : (invRootN V M hM).adjoint = invRootN V M hM :=
    invRootN_selfAdjoint V M hM
  apply ContinuousLinearMap.ext
  intro f
  simp only [referenceMap, adjointCongr, adjoint_comp, hd, comp_apply, mul_apply_eq_comp]

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
private theorem reference_normalized (M : ℝ) (hM : 0 < M) :
    adjointCongr (referenceMap V M hM) (nullN M hM) = 1 := by
  rw [reference_congr]
  change invRootN V M hM * compressedN V M hM * invRootN V M hM = 1
  rw [← operatorSqrt_mul_self _ (compressedN_nonneg V M hM), ← mul_assoc,
    invRootN_mul_sqrt, one_mul, sqrt_mul_invRootN]

private theorem relativeQ_eq (M : ℝ) (hM : 0 < M) :
    relativeQ V M hM = invRootN V M hM * invRootN V M hM := by
  rw [relativeQ, reference_congr]
  have hi : adjointCongr V.subtypeL (1 : H4D →L[ℂ] H4D) = 1 := by
    ext f
    simp [adjointCongr, Submodule.adjoint_subtypeL,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [hi, mul_one]

private theorem relativeQ_unit (M : ℝ) (hM : 0 < M) : IsUnit (relativeQ V M hM) := by
  have hu : IsUnit (invRootN V M hM) :=
    ⟨⟨_, _, invRootN_mul_sqrt V M hM, sqrt_mul_invRootN V M hM⟩, rfl⟩
  rw [relativeQ_eq]
  exact hu.mul hu

private theorem congr_add (C : V →L[ℂ] H4D) (A B : H4D →L[ℂ] H4D) :
    adjointCongr C (A + B) = adjointCongr C A + adjointCongr C B := by
  ext f
  simp [adjointCongr]

private theorem congr_massless (M : ℝ) (hM : 0 < M) :
    relativeQ V M hM - Complex.I • relativeR V M hM =
      adjointCongr (referenceMap V M hM) nullA := by
  have ha : nullA = (1 : H4D →L[ℂ] H4D) + nullJ := by unfold nullJ; abel
  rw [ha, congr_add, relativeQ, relativeR, smul_smul, Complex.I_mul_I, neg_smul, one_smul,
    sub_neg_eq_add]

private theorem congr_massive (M : ℝ) (hM : 0 < M) :
    (1 : V →L[ℂ] V) - Complex.I • relativeR V M hM =
      adjointCongr (referenceMap V M hM) (nullA + nullT M hM) := by
  rw [← nullN_add_J M hM, congr_add, reference_normalized, relativeR, smul_smul,
    Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
private theorem reference_norm_sq_le {M c : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hle : c • (1 : H4D →L[ℂ] H4D) ≤ nullN M hM) :
    ‖referenceMap V M hM‖ ^ 2 ≤ c⁻¹ := by
  have hpoint (f : V) : c * ‖referenceMap V M hM f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    have hh := lower_form V hM hle (invRootN V M hM f)
    change c * ‖referenceMap V M hM f‖ ^ 2 ≤
      (⟪invRootN V M hM f, compressedN V M hM (invRootN V M hM f)⟫_ℂ).re at hh
    have he := congr_inner (referenceMap V M hM) (nullN M hM) f f
    rw [reference_normalized, one_apply_eq_self] at he
    unfold compressedN at hh
    rw [congr_inner] at hh
    change c * ‖referenceMap V M hM f‖ ^ 2 ≤
      (⟪referenceMap V M hM f, nullN M hM (referenceMap V M hM f)⟫_ℂ).re at hh
    rw [← he] at hh
    exact hh.trans_eq (inner_self_eq_norm_sq (𝕜 := ℂ) f)
  have hn : ‖referenceMap V M hM‖ ≤ Real.sqrt c⁻¹ := by
    apply opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro f
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hc.le), inv_mul_eq_div]
    exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hpoint f)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq
    (Real.sq_sqrt (inv_nonneg.mpr hc.le))

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
private theorem delta_bound {M c : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hle : c • (1 : H4D →L[ℂ] H4D) ≤ nullN M hM) :
    ∃ hd : IsHilbertSchmidt (eq71Delta V M hM),
      hsSq _ hd ≤ c⁻¹ * hsSq (nullW M hM) (nullW_hs M hM) := by
  have hf : nullA + nullT M hM - nullA =
      quarterRoot nullA * nullW M hM * quarterRoot nullA := by
    rw [add_sub_cancel_left, nullT_factor]
  obtain ⟨hd, hb⟩ := quarterPower_congruence_sqrt_hsSq_le
    nullA_nonneg (nullB_nonneg hM) (nullW_hs M hM) hf (referenceMap V M hM)
  have he : eq71Delta V M hM =
      -(operatorSqrt (adjointCongr (referenceMap V M hM) (nullA + nullT M hM)) -
        operatorSqrt (adjointCongr (referenceMap V M hM) nullA)) := by
    rw [eq71Delta, congr_massless, congr_massive]
    abel
  have hΔ : IsHilbertSchmidt (eq71Delta V M hM) := by
    rw [he]
    simpa using isHilbertSchmidt_smul (-1 : ℂ) hd
  refine ⟨hΔ, ?_⟩
  have hsq : hsSq (eq71Delta V M hM) hΔ = hsSq _ hd := by
    unfold hsSq
    apply tsum_congr
    intro i
    rw [he, neg_apply, norm_neg]
  rw [hsq]
  exact hb.trans (mul_le_mul_of_nonneg_right (reference_norm_sq_le V hM hc hle)
    (tsum_nonneg fun _ => sq_nonneg _))

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
/-- Uniform comparison and the sharp Hilbert–Schmidt bound on every complete complex subspace. -/
theorem nullDiamond_eq71_4D (m L : ℝ) (hm : 0 < m) (hL : 0 < L) :
    let M := m * L
    let hM := mul_pos hm hL
    ∃ c : ℝ, 0 < c ∧
      c • (1 : H4D →L[ℂ] H4D) ≤ nullN M hM ∧
      ∀ (V : Submodule ℂ H4D) [CompleteSpace V],
        (∀ f : V, c * mu0Sq V f ≤ mumSq V M hM f) ∧
        IsUnit (relativeQ V M hM) ∧
        (relativeQ V M hM).ker = ⊥ ∧
        (0 ≤ relativeQ V M hM - Complex.I • relativeR V M hM) ∧
        (0 ≤ (1 : V →L[ℂ] V) - Complex.I • relativeR V M hM) ∧
        ∃ hd : IsHilbertSchmidt (eq71Delta V M hM),
          hsSq (eq71Delta V M hM) hd ≤ c⁻¹ * hsSq (nullW M hM) (nullW_hs M hM) := by
  dsimp only
  let hM := mul_pos hm hL
  obtain ⟨c, hc, hle⟩ := nullN_coercive (m * L) hM
  refine ⟨c, hc, hle, fun V _ => ?_⟩
  have hu := relativeQ_unit V (m * L) hM
  refine ⟨lower_form V hM hle, hu, LinearMap.ker_eq_bot.mpr
    (isUnit_iff_bijective.mp hu).1, ?_, ?_, delta_bound V hM hc hle⟩
  · rw [congr_massless]
    exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp nullA_nonneg).adjoint_conj _)
  · rw [congr_massive]
    exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp (nullB_nonneg hM)).adjoint_conj _)

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
/-- The literal trace of the squared difference equals its finite Hilbert–Schmidt square. -/
theorem eq71_trace_eq_hsSq (M : ℝ) (hM : 0 < M) :
    ∃ hd : IsHilbertSchmidt (eq71Delta V M hM),
      ∃ ht : IsTraceClass (eq71Delta V M hM * eq71Delta V M hM),
        trace _ ht = (hsSq (eq71Delta V M hM) hd : ℂ) := by
  obtain ⟨c, hc, hle⟩ := nullN_coercive M hM
  obtain ⟨hd, _⟩ := delta_bound V hM hc hle
  let D := eq71Delta V M hM
  have hsa : IsSelfAdjoint D := (nonneg_iff_isPositive.mp (operatorSqrt_nonneg _)).isSelfAdjoint.sub
    (nonneg_iff_isPositive.mp (operatorSqrt_nonneg _)).isSelfAdjoint
  have ht : IsTraceClass (D * D) := isTraceClass_mul_of_isHilbertSchmidt hd hd
  refine ⟨hd, ht, ?_⟩
  let b := (exists_hilbertBasis ℂ V).choose_spec.choose
  rw [trace_eq_of_hilbertBasis_unconditional ht b]
  change (∑' i, ⟪b i, (D * D) (b i)⟫_ℂ) = (∑' i, ‖D (b i)‖ ^ 2 : ℝ)
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro i
  calc
    ⟪b i, (D * D) (b i)⟫_ℂ = ⟪b i, D.adjoint (D (b i))⟫_ℂ := by
      rw [show D.adjoint = D from hsa, mul_apply_eq_comp]
    _ = ⟪D (b i), D (b i)⟫_ℂ := adjoint_inner_right D _ _
    _ = _ := by rw [inner_self_eq_norm_sq_to_K]; norm_cast

end NullConeGravity
