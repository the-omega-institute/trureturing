/- GID: D5/S3/Observer/Linear/SharpTrajectoryNoiseRecovery
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/SharpTrajectoryNoiseRecovery
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: []
   utility: none
   digest: Exact deterministic Hilbert recovery risk uses the true trajectory floor. -/

import D5.S3.Observer.Linear.PositiveWindowObservationBound
import D5.S3.Observer.MeasureSeparation.RobustMinimaxKernelBound
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery

open MeasureTheory Set
open scoped InnerProductSpace ENNReal NNReal
open D5.S3.Observer.MeasureSeparation.RobustMinimaxKernelBound
open D5.S3.Observer.Linear.PositiveWindowObservationBound

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The exact squared lower modulus, with no assumption of attainment. -/
def squaredLowerModulus (A : E →L[𝕜] F) : ℝ :=
  sInf ((fun x : E => ‖A x‖ ^ 2) '' {x : E | ‖x‖ = 1})

/-- Worst-case norm error over all states and all noise in the closed norm ball.
The reconstruction is an arbitrary total function. -/
def reconstructionRisk (A : E →L[𝕜] F) (δ : ℝ) (R : F → E) : ℝ≥0∞ :=
  worstCaseCost {m : E × F | ‖m.2‖ ≤ δ}
    (fun m R => ENNReal.ofReal ‖R (A m.1 + m.2) - m.1‖) R

omit [CompleteSpace E] in
include 𝕜 in
private lemma sphere_nonempty : ({x : E | ‖x‖ = 1} : Set E).Nonempty := by
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty_rclike 𝕜 (E := E)
    (r := 1) (by norm_num)
  exact ⟨x, by simpa using hx⟩

omit [CompleteSpace E] [Nontrivial E] [CompleteSpace F] in
private lemma modulus_le (A : E →L[𝕜] F) (x : E) (hx : ‖x‖ = 1) :
    squaredLowerModulus A ≤ ‖A x‖ ^ 2 := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨y, _, rfl⟩; exact sq_nonneg _⟩
  · exact ⟨x, hx, rfl⟩

omit [CompleteSpace E] [CompleteSpace F] in
private lemma risk_lower (A : E →L[𝕜] F) (ha : 0 < squaredLowerModulus A)
    (δ : ℝ) (hδ : 0 ≤ δ) (R : F → E) :
    ENNReal.ofReal (δ / Real.sqrt (squaredLowerModulus A)) ≤
      reconstructionRisk A δ R := by
  by_cases htop : reconstructionRisk A δ R = ⊤
  · simp [htop]
  by_cases hz : δ = 0
  · simp [hz]
  have hd : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
  let w := (reconstructionRisk A δ R).toReal
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  have error_le (x : E) (η : F) (hη : ‖η‖ ≤ δ) :
      ‖R (A x + η) - x‖ ≤ w := by
    apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
    exact le_iSup_of_le (⟨(x, η), hη⟩ : {m : E × F | ‖m.2‖ ≤ δ}) le_rfl
  have indistinguishable (z : E) (hz : ‖A z‖ ≤ δ) : ‖z‖ ≤ w := by
    have hp := error_le z (-A z) (by simpa using hz)
    have hm := error_le (-z) (A z) hz
    simp only [add_neg_cancel, map_neg, neg_add_cancel] at hp hm
    have htriangle := norm_add_le (z - R 0) (R 0 - -z)
    have heq : z - R 0 + (R 0 - -z) = (2 : 𝕜) • z := by
      rw [two_smul]; abel
    rw [heq, norm_smul, norm_sub_rev z] at htriangle
    have htwo : ‖(2 : 𝕜)‖ = (2 : ℝ) := by norm_num
    rw [htwo] at htriangle
    linarith
  have directional (v : E) (hv : ‖v‖ = 1) : δ / ‖A v‖ ≤ w := by
    have hav : 0 < ‖A v‖ := by
      have := ha.trans_le (modulus_le A v hv)
      nlinarith [norm_nonneg (A v)]
    have hs := indistinguishable (((δ / ‖A v‖ : ℝ) : 𝕜) • v)
    have hn : ‖A (((δ / ‖A v‖ : ℝ) : 𝕜) • v)‖ = δ := by
      rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (div_nonneg hδ hav.le)]
      exact div_mul_cancel₀ δ hav.ne'
    have hs' := hs hn.le
    simpa only [norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (div_nonneg hδ hav.le), hv, mul_one] using hs'
  obtain ⟨v, hv⟩ := sphere_nonempty (𝕜 := 𝕜) (E := E)
  have hw : 0 < w := by
    have hav : 0 < ‖A v‖ := by
      have := ha.trans_le (modulus_le A v hv)
      nlinarith [norm_nonneg (A v)]
    exact (div_pos hd hav).trans_le (directional v hv)
  have hinf : (δ / w) ^ 2 ≤ squaredLowerModulus A := by
    apply le_csInf ((sphere_nonempty (𝕜 := 𝕜) (E := E)).image _)
    rintro _ ⟨u, hu, rfl⟩
    have hau : 0 < ‖A u‖ := by
      have := ha.trans_le (modulus_le A u hu)
      nlinarith [norm_nonneg (A u)]
    have hdu := (div_le_iff₀ hau).mp (directional u hu)
    have hratio : δ / w ≤ ‖A u‖ := (div_le_iff₀ hw).mpr (by nlinarith)
    exact pow_le_pow_left₀ (div_nonneg hδ hw.le) hratio 2
  have hsqrt : δ / w ≤ Real.sqrt (squaredLowerModulus A) :=
    (Real.le_sqrt (div_nonneg hδ hw.le) ha.le).mpr hinf
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
  apply (div_le_iff₀ (Real.sqrt_pos.mpr ha)).mpr
  have := (div_le_iff₀ hw).mp hsqrt
  nlinarith

/-- In a Hilbert space the inverse on the closed range, composed with orthogonal
projection onto that range, attains the exact deterministic minimax risk among
all total reconstruction functions, simultaneously for every finite budget. -/
theorem sharp_hilbert_noise_recovery (A : E →L[𝕜] F)
    (ha : 0 < squaredLowerModulus A) :
    ∃ R : F →L[𝕜] E,
      (∀ x, R (A x) = x) ∧
      (∀ y x, inner 𝕜 (A x) (y - A (R y)) = 0) ∧
      (∀ y, ‖R y‖ ≤ ‖y‖ / Real.sqrt (squaredLowerModulus A)) ∧
      ∀ δ : ℝ, 0 ≤ δ →
        reconstructionRisk A δ R = ENNReal.ofReal (δ / Real.sqrt (squaredLowerModulus A)) ∧
        (⨅ Q : F → E, reconstructionRisk A δ Q) =
          ENNReal.ofReal (δ / Real.sqrt (squaredLowerModulus A)) := by
  let K : ℝ≥0 := ⟨(Real.sqrt (squaredLowerModulus A))⁻¹, by positivity⟩
  have hs : 0 < Real.sqrt (squaredLowerModulus A) := Real.sqrt_pos.mpr ha
  have hanti : AntilipschitzWith K A := by
    apply antilipschitz_of_bound_of_norm_one (𝕜 := 𝕜)
    intro x hx
    have hbound : Real.sqrt (squaredLowerModulus A) ≤ ‖A x‖ :=
      (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, modulus_le A x hx⟩
    change 1 ≤ (Real.sqrt (squaredLowerModulus A))⁻¹ * ‖A x‖
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hs).mpr (by simpa using hbound)
  have hcl : IsClosed (Set.range A) := hanti.isClosed_range A.uniformContinuous
  let : CompleteSpace A.range := hcl.completeSpace_coe
  let e := A.equivRange hanti.injective hcl
  let R : F →L[𝕜] E := e.symm.toContinuousLinearMap.comp A.range.orthogonalProjectionOnto
  have hAR (y : F) : A (R y) = A.range.starProjection y := by
    have he := e.apply_symm_apply (A.range.orthogonalProjectionOnto y)
    exact congrArg Subtype.val he
  have hRA (x : E) : R (A x) = x := by
    apply hanti.injective
    rw [hAR]
    exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
  have hnorm (y : F) : ‖R y‖ ≤ ‖y‖ / Real.sqrt (squaredLowerModulus A) := by
    have hh := hanti.le_mul_dist (R y) 0
    simp only [dist_zero_right, map_zero] at hh
    change ‖R y‖ ≤ (Real.sqrt (squaredLowerModulus A))⁻¹ * ‖A (R y)‖ at hh
    rw [hAR] at hh
    calc
      _ ≤ _ := hh
      _ ≤ (Real.sqrt (squaredLowerModulus A))⁻¹ * ‖y‖ :=
        mul_le_mul_of_nonneg_left (A.range.norm_starProjection_apply_le y) (by positivity)
      _ = _ := by rw [div_eq_inv_mul]
  refine ⟨R, hRA, ?_, hnorm, ?_⟩
  · intro y x
    rw [hAR]
    exact (A.range.mem_orthogonal _).mp (A.range.sub_starProjection_mem_orthogonal y)
      (A x) ⟨x, rfl⟩
  · intro δ hδ
    have upper : reconstructionRisk A δ R ≤
        ENNReal.ofReal (δ / Real.sqrt (squaredLowerModulus A)) := by
      apply iSup_le
      rintro ⟨⟨x, η⟩, hη⟩
      apply ENNReal.ofReal_le_ofReal
      have heq : R (A x + η) - x = R η := by rw [map_add, hRA]; abel
      rw [heq]
      exact (hnorm η).trans (div_le_div_of_nonneg_right hη hs.le)
    have lower := risk_lower A ha δ hδ
    exact ⟨le_antisymm upper (lower R),
      le_antisymm ((iInf_le _ (R : F → E)).trans upper) (le_iInf lower)⟩

omit [Nontrivial E] [CompleteSpace F] in
private lemma trajectory_l2_operator (B : E →L[𝕜] E) (C : E →L[𝕜] F)
    (T : ℝ) (hT : 0 < T) :
    ∃ A : E →L[𝕜] Lp F 2 (volume.restrict (Ioc 0 T)),
      (∀ x, (fun t => A x t) =ᵐ[volume.restrict (Ioc 0 T)]
        fun t => C ((NormedSpace.exp ((t : 𝕜) • B)) x)) ∧
      ∀ x, ‖A x‖ ^ 2 = trajectoryEnergy B C T x := by
  let μ := volume.restrict (Ioc (0 : ℝ) T)
  let f : ℝ → E →L[𝕜] F := fun t => C.comp (NormedSpace.exp ((t : 𝕜) • B))
  have hexp : Continuous (NormedSpace.exp : (E →L[𝕜] E) → E →L[𝕜] E) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (NormedSpace.exp_analytic (𝕂 := 𝕜) z).continuousAt)
  have hf : Continuous f := continuous_const.clm_comp
    (hexp.comp ((RCLike.continuous_ofReal : Continuous (fun t : ℝ => (t : 𝕜))).smul
      continuous_const))
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hf.continuousOn
  have hbound (x : E) : ∀ᵐ t ∂μ, ‖f t x‖ ≤ max M 0 * ‖x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ((f t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ((hM t (Ioc_subset_Icc_self ht)).trans
        (le_max_left _ _)) (norm_nonneg x))
  have hmem (x : E) : MemLp (fun t => f t x) 2 μ :=
    MemLp.of_bound (((ContinuousLinearMap.apply 𝕜 F x).continuous.comp hf).aestronglyMeasurable)
      (max M 0 * ‖x‖) (hbound x)
  let L : E →ₗ[𝕜] Lp F 2 μ := {
    toFun := fun x => (hmem x).toLp (fun t => f t x)
    map_add' := by
      intro x y
      calc
        (hmem (x + y)).toLp _ = ((hmem x).add (hmem y)).toLp _ := by
          apply MemLp.toLp_congr
          filter_upwards with t
          exact map_add (f t) x y
        _ = _ := MemLp.toLp_add _ _
    map_smul' := by
      intro a x
      calc
        (hmem (a • x)).toLp _ = ((hmem x).const_smul a).toLp _ := by
          apply MemLp.toLp_congr
          filter_upwards with t
          exact map_smul (f t) a x
        _ = _ := MemLp.toLp_const_smul a _ }
  have hrep (x : E) : (fun t => L x t) =ᵐ[μ] fun t => f t x :=
    MemLp.coeFn_toLp (hmem x)
  have hL (x : E) : ‖L x‖ ≤
      (measureUnivNNReal μ : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * max M 0 * ‖x‖ := by
    calc
      _ ≤ (measureUnivNNReal μ : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * (max M 0 * ‖x‖) := by
        apply Lp.norm_le_of_ae_bound (mul_nonneg (le_max_right _ _) (norm_nonneg x))
        filter_upwards [hrep x, hbound x] with t ht hb
        rw [ht]
        exact hb
      _ = _ := by ring
  let A := L.mkContinuous _ hL
  refine ⟨A, hrep, ?_⟩
  intro x
  calc
    ‖A x‖ ^ 2 = RCLike.re (inner 𝕜 (A x) (A x)) := norm_sq_eq_re_inner _
    _ = ∫ t, ‖A x t‖ ^ 2 ∂μ := by
      rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := 𝕜) (A x) (A x))]
      simp only [← norm_sq_eq_re_inner]
    _ = ∫ t, ‖f t x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrep x] with t ht
      change ‖L x t‖ ^ 2 = ‖f t x‖ ^ 2
      rw [ht]
    _ = trajectoryEnergy B C T x := by
      rw [trajectoryEnergy, intervalIntegral.integral_of_le hT.le]
      rfl

/-- The exact deterministic noise clause for the actual, unnormalized Lebesgue
L² exponential trajectory. The same total Moore--Penrose least-squares inverse
is optimal for every nonnegative real noise budget, including zero. -/
theorem sharp_trajectory_noise_recovery (B : E →L[𝕜] E) (C : E →L[𝕜] F)
    (T : ℝ) (hT : 0 < T) (ha : 0 < observationFloor B C T) :
    ∃ A : E →L[𝕜] Lp F 2 (volume.restrict (Ioc 0 T)),
    ∃ R : Lp F 2 (volume.restrict (Ioc 0 T)) →L[𝕜] E,
      (∀ x, (fun t => A x t) =ᵐ[volume.restrict (Ioc 0 T)]
        fun t => C ((NormedSpace.exp ((t : 𝕜) • B)) x)) ∧
      (∀ x, ‖A x‖ ^ 2 = trajectoryEnergy B C T x) ∧
      squaredLowerModulus A = observationFloor B C T ∧
      (∀ x, R (A x) = x) ∧
      (∀ y x, inner 𝕜 (A x) (y - A (R y)) = 0) ∧
      (∀ y, ‖R y‖ ≤ ‖y‖ / Real.sqrt (observationFloor B C T)) ∧
      ∀ δ : ℝ, 0 ≤ δ →
        reconstructionRisk A δ R = ENNReal.ofReal (δ / Real.sqrt (observationFloor B C T)) ∧
        (⨅ Q : Lp F 2 (volume.restrict (Ioc 0 T)) → E, reconstructionRisk A δ Q) =
          ENNReal.ofReal (δ / Real.sqrt (observationFloor B C T)) := by
  obtain ⟨A, hrep, henergy⟩ := trajectory_l2_operator B C T hT
  have hfloor : squaredLowerModulus A = observationFloor B C T := by
    unfold squaredLowerModulus observationFloor
    congr 1
    ext z
    simp only [mem_image, mem_ofPred_eq, henergy]
  obtain ⟨R, hRA, hnormal, hnorm, hrisk⟩ :=
    sharp_hilbert_noise_recovery A (hfloor.symm ▸ ha)
  refine ⟨A, R, hrep, henergy, hfloor, hRA, hnormal, ?_, ?_⟩
  · simpa only [hfloor] using hnorm
  · simpa only [hfloor] using hrisk

#print axioms sharp_hilbert_noise_recovery
#print axioms sharp_trajectory_noise_recovery

end D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery
