/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondExcitability5D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondExcitability5D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp finite covariance-root trace and mutual Gaussian excitability in five dimensions. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondWeakBoundary5D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondExcitability4D
import D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianFolium
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
import D5.S3.Quantum.Analysis.TraceClass.GeneralIdeal

/-! The relative covariance and finite trace on complete complex subspaces of the null diamond. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open ContinuousLinearMap HilbertSchmidt MeasureTheory
open D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState
open D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianFolium
open D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
open scoped ComplexOrder InnerProductSpace NNReal Ring CStarAlgebra

namespace NullConeGravity

private local instance : SecondCountableTopology H5D := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact Lp.SecondCountableTopology

private abbrev reflectReal (x : H5D) : H5D := nullConj5D.toLinearIsometryEquiv x

/-- The massive symmetric covariance on the ambient massless reference space. -/
def nullN5D (M : ℝ) (hM : 0 < M) : H5D →L[ℂ] H5D := 1 + nullT5D M hM

private theorem nullN5D_add_J (M : ℝ) (hM : 0 < M) :
    nullN5D M hM + nullJ5D = nullA5D + nullT5D M hM := by
  unfold nullN5D nullJ5D
  abel

/-- The signed positive bounds and compact correction give a uniform positive lower bound. -/
theorem nullN5D_coercive (M : ℝ) (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : H5D →L[ℂ] H5D) ≤ nullN5D M hM := by
  have hJ := (nonneg_iff_isPositive.mp nullA5D_nonneg).isSelfAdjoint.sub (IsSelfAdjoint.one _)
  have hp : 0 ≤ nullN5D M hM + nullJ5D := nullN5D_add_J M hM ▸ nullB5D_nonneg hM
  exact (hilbertSchmidt_add_one_coercive (nullT5D_hs M hM) (nullT5D_selfAdjoint M hM)
    hJ nullJ5D_ker hp (nullN5D_sub_J_nonneg hM)).2

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

section Trace

variable (V : Submodule ℂ H5D) [CompleteSpace V]

/-- Compression of the symmetric covariance to the chosen complete subspace. -/
def compressedN5D (M : ℝ) (hM : 0 < M) : V →L[ℂ] V :=
  adjointCongr V.subtypeL (nullN5D M hM)

/-- The squared massless symmetric norm. -/
def mu0Sq5D (f : V) : ℝ := ‖f‖ ^ 2

/-- The squared massive symmetric norm. -/
def mumSq5D (M : ℝ) (hM : 0 < M) (f : V) : ℝ :=
  (⟪f, compressedN5D V M hM f⟫_ℂ).re

private theorem congr_inner {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (C : K →L[ℂ] H) (A : H →L[ℂ] H) (x y : K) :
    ⟪x, adjointCongr C A y⟫_ℂ = ⟪C x, A (C y)⟫_ℂ := by
  simp only [adjointCongr, comp_apply, adjoint_inner_right]

private theorem lower_form {M c : ℝ} (hM : 0 < M)
    (hc : c • (1 : H5D →L[ℂ] H5D) ≤ nullN5D M hM) (f : V) :
    c * mu0Sq5D V f ≤ mumSq5D V M hM f := by
  have h := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hc)).re_inner_nonneg_right
    (V.subtypeL f)
  change 0 ≤ (⟪V.subtypeL f, (nullN5D M hM - c • (1 : H5D →L[ℂ] H5D))
    (V.subtypeL f)⟫_ℂ).re at h
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right,
    Complex.sub_re, inner_smul_right_eq_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  have hs : (⟪V.subtypeL f, V.subtypeL f⟫_ℂ).re = ‖f‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (V.subtypeL f)
  rw [hs] at h
  unfold mumSq5D mu0Sq5D compressedN5D
  rw [congr_inner]
  exact sub_nonneg.mp h

/-- The symmetric upper comparison holds with the ambient operator norm. -/
theorem mumSq5D_le (M : ℝ) (hM : 0 < M) (f : V) :
    mumSq5D V M hM f ≤ ‖nullN5D M hM‖ * mu0Sq5D V f := by
  unfold mumSq5D mu0Sq5D compressedN5D
  rw [congr_inner]
  calc
    _ ≤ ‖V.subtypeL f‖ * ‖nullN5D M hM (V.subtypeL f)‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    _ ≤ ‖V.subtypeL f‖ * (‖nullN5D M hM‖ * ‖V.subtypeL f‖) :=
      mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
    _ = _ := by change ‖f‖ * (‖nullN5D M hM‖ * ‖f‖) = _; ring

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
private theorem compressedN_nonneg (M : ℝ) (hM : 0 < M) :
    0 ≤ compressedN5D V M hM := by
  obtain ⟨c, hc, hle⟩ := nullN5D_coercive M hM
  have hzero : 0 ≤ c • (1 : H5D →L[ℂ] H5D) := by
    change 0 ≤ (c : ℂ) • (1 : H5D →L[ℂ] H5D)
    exact nonneg_iff_isPositive.mpr (isPositive_one.smul_of_nonneg (Complex.zero_le_real.mpr hc.le))
  have hn : 0 ≤ nullN5D M hM := hzero.trans hle
  exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hn).adjoint_conj V.subtypeL)

private theorem compressedN_unit (M : ℝ) (hM : 0 < M) :
    IsUnit (compressedN5D V M hM) := by
  obtain ⟨c, hc, hle⟩ := nullN5D_coercive M hM
  let d : ℝ≥0 := ⟨c, hc.le⟩
  apply isUnit_of_forall_le_norm_inner_map _ (c := d) (show 0 < d from hc)
  intro f
  have hf := lower_form V hM hle f
  change c * ‖f‖ ^ 2 ≤ (⟪f, compressedN5D V M hM f⟫_ℂ).re at hf
  rw [mul_comm]
  refine hf.trans ?_
  change RCLike.re ⟪f, compressedN5D V M hM f⟫_ℂ ≤ _
  rw [inner_re_symm (𝕜 := ℂ)]
  exact Complex.re_le_norm _

private theorem sqrt_unit (M : ℝ) (hM : 0 < M) :
    IsUnit (operatorSqrt (compressedN5D V M hM)) :=
  (operatorSqrt_isUnit_iff _ (compressedN_nonneg V M hM)).mpr (compressedN_unit V M hM)

/-- The inverse of the positive square root of the compressed covariance. -/
def invRootN5D (M : ℝ) (hM : 0 < M) : V →L[ℂ] V :=
  Ring.inverse (operatorSqrt (compressedN5D V M hM))

/-- Inclusion after changing to the massive reference norm. -/
def referenceMap5D (M : ℝ) (hM : 0 < M) : V →L[ℂ] H5D :=
  V.subtypeL ∘L invRootN5D V M hM

/-- The transported massless symmetric covariance. -/
def relativeQ5D (M : ℝ) (hM : 0 < M) : V →L[ℂ] V :=
  adjointCongr (referenceMap5D V M hM) (1 : H5D →L[ℂ] H5D)

/-- The transported skew form. -/
def relativeR5D (M : ℝ) (hM : 0 < M) : V →L[ℂ] V :=
  Complex.I • adjointCongr (referenceMap5D V M hM) nullJ5D

/-- The difference of the two positive covariance square roots. -/
def eq71Delta5D (M : ℝ) (hM : 0 < M) : V →L[ℂ] V :=
  operatorSqrt (relativeQ5D V M hM - Complex.I • relativeR5D V M hM) -
    operatorSqrt (1 - Complex.I • relativeR5D V M hM)

private theorem invRootN_mul_sqrt (M : ℝ) (hM : 0 < M) :
    invRootN5D V M hM * operatorSqrt (compressedN5D V M hM) = 1 :=
  Ring.inverse_mul_cancel _ (sqrt_unit V M hM)

private theorem sqrt_mul_invRootN (M : ℝ) (hM : 0 < M) :
    operatorSqrt (compressedN5D V M hM) * invRootN5D V M hM = 1 :=
  Ring.mul_inverse_cancel _ (sqrt_unit V M hM)

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
private theorem invRootN_selfAdjoint (M : ℝ) (hM : 0 < M) :
    IsSelfAdjoint (invRootN5D V M hM) := by
  have hs := (nonneg_iff_isPositive.mp
    (operatorSqrt_nonneg (compressedN5D V M hM))).isSelfAdjoint
  change star (invRootN5D V M hM) = _
  have h : star (invRootN5D V M hM) * operatorSqrt (compressedN5D V M hM) = 1 := by
    have hh := congrArg star (sqrt_mul_invRootN V M hM)
    simpa only [star_mul, hs.star_eq, star_one] using hh
  exact left_inv_eq_right_inv h (sqrt_mul_invRootN V M hM)

private theorem reference_congr (M : ℝ) (hM : 0 < M) (A : H5D →L[ℂ] H5D) :
    adjointCongr (referenceMap5D V M hM) A =
      invRootN5D V M hM * adjointCongr V.subtypeL A * invRootN5D V M hM := by
  have hd : (invRootN5D V M hM).adjoint = invRootN5D V M hM :=
    invRootN_selfAdjoint V M hM
  apply ContinuousLinearMap.ext
  intro f
  simp only [referenceMap5D, adjointCongr, adjoint_comp, hd, comp_apply, mul_apply_eq_comp]

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
private theorem reference_normalized (M : ℝ) (hM : 0 < M) :
    adjointCongr (referenceMap5D V M hM) (nullN5D M hM) = 1 := by
  rw [reference_congr]
  change invRootN5D V M hM * compressedN5D V M hM * invRootN5D V M hM = 1
  rw [← operatorSqrt_mul_self _ (compressedN_nonneg V M hM), ← mul_assoc,
    invRootN_mul_sqrt, one_mul, sqrt_mul_invRootN]

private theorem relativeQ_eq (M : ℝ) (hM : 0 < M) :
    relativeQ5D V M hM = invRootN5D V M hM * invRootN5D V M hM := by
  rw [relativeQ5D, reference_congr]
  have hi : adjointCongr V.subtypeL (1 : H5D →L[ℂ] H5D) = 1 := by
    ext f
    simp [adjointCongr, Submodule.adjoint_subtypeL,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [hi, mul_one]

private theorem relativeQ_unit (M : ℝ) (hM : 0 < M) : IsUnit (relativeQ5D V M hM) := by
  have hu : IsUnit (invRootN5D V M hM) :=
    ⟨⟨_, _, invRootN_mul_sqrt V M hM, sqrt_mul_invRootN V M hM⟩, rfl⟩
  rw [relativeQ_eq]
  exact hu.mul hu

private theorem congr_add (C : V →L[ℂ] H5D) (A B : H5D →L[ℂ] H5D) :
    adjointCongr C (A + B) = adjointCongr C A + adjointCongr C B := by
  ext f
  simp [adjointCongr]

private theorem congr_massless (M : ℝ) (hM : 0 < M) :
    relativeQ5D V M hM - Complex.I • relativeR5D V M hM =
      adjointCongr (referenceMap5D V M hM) nullA5D := by
  have ha : nullA5D = (1 : H5D →L[ℂ] H5D) + nullJ5D := by unfold nullJ5D; abel
  rw [ha, congr_add, relativeQ5D, relativeR5D, smul_smul, Complex.I_mul_I, neg_smul, one_smul,
    sub_neg_eq_add]

private theorem congr_massive (M : ℝ) (hM : 0 < M) :
    (1 : V →L[ℂ] V) - Complex.I • relativeR5D V M hM =
      adjointCongr (referenceMap5D V M hM) (nullA5D + nullT5D M hM) := by
  rw [← nullN5D_add_J M hM, congr_add, reference_normalized, relativeR5D, smul_smul,
    Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
private theorem reference_norm_sq_le {M c : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hle : c • (1 : H5D →L[ℂ] H5D) ≤ nullN5D M hM) :
    ‖referenceMap5D V M hM‖ ^ 2 ≤ c⁻¹ := by
  have hpoint (f : V) : c * ‖referenceMap5D V M hM f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    have hh := lower_form V hM hle (invRootN5D V M hM f)
    change c * ‖referenceMap5D V M hM f‖ ^ 2 ≤
      (⟪invRootN5D V M hM f, compressedN5D V M hM (invRootN5D V M hM f)⟫_ℂ).re at hh
    have he := congr_inner (referenceMap5D V M hM) (nullN5D M hM) f f
    rw [reference_normalized, one_apply_eq_self] at he
    unfold compressedN5D at hh
    rw [congr_inner] at hh
    change c * ‖referenceMap5D V M hM f‖ ^ 2 ≤
      (⟪referenceMap5D V M hM f, nullN5D M hM (referenceMap5D V M hM f)⟫_ℂ).re at hh
    rw [← he] at hh
    exact hh.trans_eq (inner_self_eq_norm_sq (𝕜 := ℂ) f)
  have hn : ‖referenceMap5D V M hM‖ ≤ Real.sqrt c⁻¹ := by
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
    (hle : c • (1 : H5D →L[ℂ] H5D) ≤ nullN5D M hM) :
    ∃ hd : IsHilbertSchmidt (eq71Delta5D V M hM),
      hsSq _ hd ≤ c⁻¹ * hsSq (nullW5D M hM) (nullW5D_hs M hM) := by
  have hf : nullA5D + nullT5D M hM - nullA5D =
      quarterRoot nullA5D * nullW5D M hM * quarterRoot nullA5D := by
    rw [add_sub_cancel_left, nullT5D_factor]
  obtain ⟨hd, hb⟩ := quarterPower_congruence_sqrt_hsSq_le
    nullA5D_nonneg (nullB5D_nonneg hM) (nullW5D_hs M hM) hf (referenceMap5D V M hM)
  have he : eq71Delta5D V M hM =
      -(operatorSqrt (adjointCongr (referenceMap5D V M hM) (nullA5D + nullT5D M hM)) -
        operatorSqrt (adjointCongr (referenceMap5D V M hM) nullA5D)) := by
    rw [eq71Delta5D, congr_massless, congr_massive]
    abel
  have hΔ : IsHilbertSchmidt (eq71Delta5D V M hM) := by
    rw [he]
    simpa using isHilbertSchmidt_smul (-1 : ℂ) hd
  refine ⟨hΔ, ?_⟩
  have hsq : hsSq (eq71Delta5D V M hM) hΔ = hsSq _ hd := by
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
theorem nullDiamond_eq71_5D (m L : ℝ) (hm : 0 < m) (hL : 0 < L) :
    let M := m * L
    let hM := mul_pos hm hL
    ∃ c : ℝ, 0 < c ∧
      c • (1 : H5D →L[ℂ] H5D) ≤ nullN5D M hM ∧
      ∀ (V : Submodule ℂ H5D) [CompleteSpace V],
        (∀ f : V, c * mu0Sq5D V f ≤ mumSq5D V M hM f) ∧
        IsUnit (relativeQ5D V M hM) ∧
        (relativeQ5D V M hM).ker = ⊥ ∧
        (0 ≤ relativeQ5D V M hM - Complex.I • relativeR5D V M hM) ∧
        (0 ≤ (1 : V →L[ℂ] V) - Complex.I • relativeR5D V M hM) ∧
        ∃ hd : IsHilbertSchmidt (eq71Delta5D V M hM),
          hsSq (eq71Delta5D V M hM) hd ≤ c⁻¹ * hsSq (nullW5D M hM) (nullW5D_hs M hM) := by
  dsimp only
  let hM := mul_pos hm hL
  obtain ⟨c, hc, hle⟩ := nullN5D_coercive (m * L) hM
  refine ⟨c, hc, hle, fun V _ => ?_⟩
  have hu := relativeQ_unit V (m * L) hM
  refine ⟨lower_form V hM hle, hu, LinearMap.ker_eq_bot.mpr
    (isUnit_iff_bijective.mp hu).1, ?_, ?_, delta_bound V hM hc hle⟩
  · rw [congr_massless]
    exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp nullA5D_nonneg).adjoint_conj _)
  · rw [congr_massive]
    exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp (nullB5D_nonneg hM)).adjoint_conj _)

set_option maxHeartbeats 1600000 in
-- Elaborate the concrete L² subspace and its operator instances.
/-- The literal trace of the squared difference equals its finite Hilbert–Schmidt square. -/
theorem eq71_trace_eq_hsSq_5D (M : ℝ) (hM : 0 < M) :
    ∃ hd : IsHilbertSchmidt (eq71Delta5D V M hM),
      ∃ ht : IsTraceClass (eq71Delta5D V M hM * eq71Delta5D V M hM),
        trace _ ht = (hsSq (eq71Delta5D V M hM) hd : ℂ) := by
  obtain ⟨c, hc, hle⟩ := nullN5D_coercive M hM
  obtain ⟨hd, _⟩ := delta_bound V hM hc hle
  let D := eq71Delta5D V M hM
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

end Trace

/-- Restriction of frequency-reflecting conjugation to an invariant complex subspace. -/
def subspaceConjugation5D (V : Submodule ℂ H5D) (hV : ∀ x ∈ V, reflectReal x ∈ V) : RealConjugation V where
  toLinearIsometryEquiv :=
    { toLinearEquiv := LinearEquiv.ofInvolutive
        { toFun := fun x => ⟨reflectReal x, hV x x.property⟩
          map_add' := fun x y => Subtype.ext (map_add nullConj5D.toLinearIsometryEquiv (x : H5D) y)
          map_smul' := fun c x => Subtype.ext (map_smul nullConj5D.toLinearIsometryEquiv c (x : H5D)) }
        (fun x => Subtype.ext (nullConj5D.involutive x))
      norm_map' := fun x => nullConj5D.toLinearIsometryEquiv.norm_map (x : H5D) }
  involutive := fun x => Subtype.ext (nullConj5D.involutive x)
  map_complex_smul := fun c x => Subtype.ext (nullConj5D.map_complex_smul c x)

open private adjoint_conjugation congr_conjugation squareRoot_real inverse_real
  gaussianPairRealization from D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondExcitability4D

private abbrev RealOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Γ : RealConjugation H) (T : H →L[ℂ] H) : Prop :=
  ∀ x, Γ.toLinearIsometryEquiv (T x) = T (Γ.toLinearIsometryEquiv x)

section RelativeOperators
variable (V : Submodule ℂ H5D) [CompleteSpace V]
variable (hV : ∀ x ∈ V, reflectReal x ∈ V) (M : ℝ) (hM : 0 < M)
private theorem compressed_real : RealOperator (subspaceConjugation5D V hV) (compressedN5D V M hM) := by
  apply congr_conjugation nullConj5D (subspaceConjugation5D V hV) V.subtypeL (fun _ => rfl)
  intro x
  change reflectReal (nullN5D M hM x) = nullN5D M hM (reflectReal x)
  change nullConj5D.toLinearIsometryEquiv (nullN5D M hM x) =
    nullN5D M hM (nullConj5D.toLinearIsometryEquiv x)
  simp [nullN5D, nullConj5D_comm_T]
set_option maxHeartbeats 1600000 in
private theorem compressed_positive : 0 ≤ compressedN5D V M hM := by
  obtain ⟨c, hc, hle⟩ := nullN5D_coercive M hM
  have hn : 0 ≤ nullN5D M hM := (show 0 ≤ c • (1 : H5D →L[ℂ] H5D) from
    nonneg_iff_isPositive.mpr (isPositive_one.smul_of_nonneg (Complex.zero_le_real.mpr hc.le))).trans hle
  exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hn).adjoint_conj V.subtypeL)
set_option maxHeartbeats 1600000 in
private theorem inverseRoot_real : RealOperator (subspaceConjugation5D V hV) (invRootN5D V M hM) :=
  inverse_real _ (squareRoot_real _ (compressed_positive V M hM) (compressed_real V hV M hM))
private theorem reference_real (x : V) :
    nullConj5D.toLinearIsometryEquiv (referenceMap5D V M hM x) =
      referenceMap5D V M hM ((subspaceConjugation5D V hV).toLinearIsometryEquiv x) :=
  congrArg Subtype.val (inverseRoot_real V hV M hM x)
set_option maxHeartbeats 1600000 in
private theorem relativeQ_real : RealOperator (subspaceConjugation5D V hV) (relativeQ5D V M hM) :=
  congr_conjugation nullConj5D (subspaceConjugation5D V hV)
    (referenceMap5D V M hM) (reference_real V hV M hM) (fun _ => rfl)
set_option maxHeartbeats 1600000 in
private theorem relativeR_real : RealOperator (subspaceConjugation5D V hV) (relativeR5D V M hM) := by
  let Γ := subspaceConjugation5D V hV
  let C := referenceMap5D V M hM
  intro x
  change Γ.toLinearIsometryEquiv (Complex.I • C.adjoint (nullJ5D (C x))) =
    Complex.I • C.adjoint (nullJ5D (C (Γ.toLinearIsometryEquiv x)))
  rw [Γ.map_complex_smul, adjoint_conjugation nullConj5D Γ C (reference_real V hV M hM)]
  change star Complex.I • C.adjoint (nullConj5D.toLinearIsometryEquiv (nullJ5D (C x))) = _
  rw [nullConj5D_anti_J, map_neg, reference_real V hV M hM]
  simp only [Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]
  rfl
set_option maxHeartbeats 1600000 in
private theorem relativeR_adjoint : (relativeR5D V M hM).adjoint = -relativeR5D V M hM := by
  let C := referenceMap5D V M hM
  have hj : nullJ5D.adjoint = nullJ5D := (IsSelfAdjoint.of_nonneg nullA5D_nonneg).sub (IsSelfAdjoint.one _)
  have hsa : IsSelfAdjoint (adjointCongr C nullJ5D) := by
    change (adjointCongr C nullJ5D).adjoint = _
    simp [adjointCongr, adjoint_comp, hj, comp_assoc]
  rw [← star_eq_adjoint]
  change star (Complex.I • adjointCongr C nullJ5D) = -(Complex.I • adjointCongr C nullJ5D)
  rw [star_smul, hsa.star_eq]
  simp

set_option maxHeartbeats 2000000 in
/-- Real and positive relative covariance data, with finite square-root difference. -/
theorem nullDiamondRelativeProperties5D :
    0 ≤ relativeQ5D V M hM ∧ (relativeQ5D V M hM).ker = ⊥ ∧
    (∀ x, (subspaceConjugation5D V hV).toLinearIsometryEquiv (relativeQ5D V M hM x) =
      relativeQ5D V M hM ((subspaceConjugation5D V hV).toLinearIsometryEquiv x)) ∧
    (relativeR5D V M hM).adjoint = -relativeR5D V M hM ∧
    (∀ x, (subspaceConjugation5D V hV).toLinearIsometryEquiv (relativeR5D V M hM x) =
      relativeR5D V M hM ((subspaceConjugation5D V hV).toLinearIsometryEquiv x)) ∧
    0 ≤ (1 : V →L[ℂ] V) - Complex.I • relativeR5D V M hM ∧
    0 ≤ relativeQ5D V M hM - Complex.I • relativeR5D V M hM ∧
    IsHilbertSchmidt (eq71Delta5D V M hM) := by
  obtain ⟨_, _, _, hv⟩ := nullDiamond_eq71_5D M 1 hM zero_lt_one
  simp only [mul_one] at hv
  obtain ⟨_, _, hk, hp₂, hp₁, hd, _⟩ := hv V
  refine ⟨?_, hk, relativeQ_real V hV M hM, relativeR_adjoint V M hM,
    relativeR_real V hV M hM, hp₁, hp₂, hd⟩
  exact nonneg_iff_isPositive.mpr (isPositive_one.adjoint_conj (referenceMap5D V M hM))
end RelativeOperators

section Excitability

open D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianFolium
variable {S A : Type*} [AddCommGroup S] [Module ℝ S]
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {σ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ}

set_option maxHeartbeats 2000000 in
/-- The relative massless and massive Gaussian states are in one another's countable GNS folia. -/
theorem nullDiamond_excitable_5D (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (V : Submodule ℂ H5D) [CompleteSpace V] (hV : ∀ x ∈ V, reflectReal x ∈ V)
    (W : WeylSystem (A := A) σ) (ω₀ ω_m : A →ₚ[ℂ] ℂ) (e : S →ₗ[ℝ] V)
    (he : ∀ f, (subspaceConjugation5D V hV).toLinearIsometryEquiv (e f) = e f)
    (hd : Dense (Submodule.span ℂ (Set.range e) : Set V))
    (hσ : ∀ f g, σ f g = -2 * (⟪e f, relativeR5D V (m * L) (mul_pos hm hL) (e g)⟫_ℂ).re)
    (h₀ : ω₀ 1 = 1) (hmState : ω_m 1 = 1)
    (hRef : ∀ f, ω_m (W.weyl f) = Complex.exp (-(‖e f‖^2 : ℂ)/2))
    (hTarget : ∀ f, ω₀ (W.weyl f) = Complex.exp
      (-((⟪e f, relativeQ5D V (m * L) (mul_pos hm hL) (e f)⟫_ℂ).re : ℂ)/2)) :
    Excitability ω₀ ω_m ∧ Excitability ω_m ω₀ := by
  let hM := mul_pos hm hL
  obtain ⟨hQ, hker, hq, hR, hr, h₁, h₂, hHS⟩ := nullDiamondRelativeProperties5D V hV (m * L) hM
  exact gaussian_mutual_excitable_of_sqrt_hs W ω_m ω₀ (subspaceConjugation5D V hV) e he hd
    (relativeQ5D V (m * L) hM) (relativeR5D V (m * L) hM) hQ hker hq hR hr h₁ h₂
    hmState h₀ hσ hRef hTarget hHS
end Excitability

/-- The concrete massless and massive covariances on the fixed real form of a null subspace. -/
def NullDiamondConcreteRealization5D (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (V : Submodule ℂ H5D) [CompleteSpace V] (hV : ∀ x ∈ V, reflectReal x ∈ V) : Prop :=
  GaussianPairRealization (subspaceConjugation5D V hV)
    (relativeQ5D V (m * L) (mul_pos hm hL)) (relativeR5D V (m * L) (mul_pos hm hL))
set_option maxHeartbeats 2000000 in
/-- The paired Fock Weyl algebra realizes both Gaussian states with mutual excitability. -/
theorem nullDiamond_concrete_gaussian_excitable_5D (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (V : Submodule ℂ H5D) [CompleteSpace V] (hV : ∀ x ∈ V, reflectReal x ∈ V) :
    NullDiamondConcreteRealization5D m L hm hL V hV := by
  let hM := mul_pos hm hL
  obtain ⟨hQ, hk, hq, hR, hr, h₁, h₂, hHS⟩ := nullDiamondRelativeProperties5D V hV (m * L) hM
  exact gaussianPairRealization (subspaceConjugation5D V hV) _ _ hQ hk hq hR hr h₁ h₂ hHS

private local instance : CompleteSpace (⊤ : Submodule ℂ H5D) :=
  (show IsClosed ((⊤ : Submodule ℂ H5D) : Set H5D) from isClosed_univ).completeSpace_coe

/-- The unconditional realization on the full null-diamond Hilbert space. -/
theorem nullDiamond_full_space_excitable_5D (m L : ℝ) (hm : 0 < m) (hL : 0 < L) :
    NullDiamondConcreteRealization5D m L hm hL (⊤ : Submodule ℂ H5D)
      (fun _ _ => Submodule.mem_top) :=
  nullDiamond_concrete_gaussian_excitable_5D m L hm hL ⊤ (fun _ _ => Submodule.mem_top)

end NullConeGravity
