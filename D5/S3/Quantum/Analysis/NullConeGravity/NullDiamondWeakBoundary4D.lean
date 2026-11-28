/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regulated null-cone shell forms and weak boundary pairing. -/

import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondMultipliers4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondMassShell4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondProfileFourier4D
import D5.S3.Analysis.ConeCapLimits
import D5.S3.Analysis.RegulatedSeparation
import D5.S3.Analysis.AngularFourierPairing
import D5.S3.Analysis.CompactKernelPairing
import D5.S3.Analysis.ShellPairing
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import D5.S3.Analysis.ModularLogPairing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A regulated shell square for compact cone profiles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped InnerProductSpace Topology ENNReal NNReal FourierTransform
open D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability

namespace NullConeGravity

open Omega (regulatedSeparation)

/-- The plane-wave amplitude of the affine radial derivative on the cone. -/
def shellAmplitude (M : ℝ) (F : ConeProfile) (k : E3) : ℂ :=
  ∫ u in Ioo (0 : ℝ) 1, ∫ n : Sphere4D, (u : ℂ) * profileDeriv F u n *
    Complex.exp (Complex.I * (((energy M k - ⟪k, (n : E3)⟫_ℝ) * u : ℝ) : ℂ))
      ∂sphereMeasure

/-- The shell square with positive imaginary-time damping. -/
def regulatedShellQuad (M ε : ℝ) (F : ConeProfile) : ℝ :=
  4 * ∫ k : E3, shellWeight M k * Real.exp (-ε * energy M k) * ‖shellAmplitude M F k‖ ^ 2

/-- The regulated spectral form is nonnegative for every real mass and regulator. -/
theorem regulatedShellQuad_nonneg (M ε : ℝ) (F : ConeProfile) :
    0 ≤ regulatedShellQuad M ε F := by
  unfold regulatedShellQuad
  refine mul_nonneg (by norm_num) (integral_nonneg (fun k => ?_))
  unfold shellWeight energy
  positivity

private def coneMeasure : Measure Phase4D :=
  (volume.restrict (Ioo (0 : ℝ) 1)).prod sphereMeasure

private local instance : IsFiniteMeasure coneMeasure := by
  unfold coneMeasure
  infer_instance

private def phase (M : ℝ) (k : E3) (p : Phase4D) : ℝ :=
  (energy M k - ⟪k, (p.2 : E3)⟫_ℝ) * p.1

private def derivativeWeight (F : ConeProfile) (p : Phase4D) : ℂ :=
  (p.1 : ℂ) * profileDeriv F p.1 p.2

private theorem profileDeriv_continuous (F : ConeProfile) :
    Continuous (fun p : Phase4D => profileDeriv F p.1 p.2) := by
  induction F with
  | nil => simpa [profileDeriv] using continuous_const (y := (0 : ℂ))
  | cons f F ih =>
    have hr : Continuous (deriv f.radial) :=
      f.smooth.continuous_deriv (by exact_mod_cast le_top)
    exact ((hr.comp continuous_fst).mul
      (f.lipschitz.choose_spec.continuous.comp continuous_snd)).add ih

private theorem derivativeWeight_continuous (F : ConeProfile) :
    Continuous (derivativeWeight F) :=
  (Complex.continuous_ofReal.comp continuous_fst).mul (profileDeriv_continuous F)

private theorem derivativeWeight_memLp (F : ConeProfile) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ p ∂coneMeasure, ‖derivativeWeight F p‖ ≤ C := by
  have hc : IsCompact (Icc (0 : ℝ) 1 ×ˢ (univ : Set Sphere4D)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := (hc.image (derivativeWeight_continuous F)).isBounded.exists_norm_le
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  have hae : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)), u ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [((volume.restrict (Ioo (0 : ℝ) 1)).quasiMeasurePreserving_fst
    (ν := sphereMeasure)).ae hae] with p hp
  exact (hC _ ⟨p, ⟨Ioo_subset_Icc_self hp, mem_univ _⟩, rfl⟩).trans (le_max_right _ _)

private theorem phase_continuous (M : ℝ) :
    Continuous (fun p : E3 × Phase4D => phase M p.1 p.2) := by
  unfold phase energy
  fun_prop

private def planeWave (M : ℝ) (F : ConeProfile) (k : E3) (p : Phase4D) : ℂ :=
  derivativeWeight F p * Complex.exp (Complex.I * (phase M k p : ℂ))

private theorem derivativeWeight_integrable (F : ConeProfile) :
    Integrable (derivativeWeight F) coneMeasure := by
  obtain ⟨C, -, hC⟩ := derivativeWeight_memLp F
  exact (integrable_const C).mono' (derivativeWeight_continuous F).aestronglyMeasurable hC

private theorem shellAmplitude_eq_integral (M : ℝ) (F : ConeProfile) (k : E3) :
    shellAmplitude M F k = ∫ p, planeWave M F k p ∂coneMeasure :=
  (integral_prod _ (Omega.shellWave_integrable (a := derivativeWeight F) (phase := phase M)
    (derivativeWeight_integrable F) (phase_continuous M).measurable k)).symm

private def shellDamping (M ε : ℝ) (k : E3) : ℝ :=
  shellWeight M k * Real.exp (-ε * energy M k)

private theorem shellDamping_integrable (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (shellDamping M ε) := by
  have hτ : 0 < (ε : ℂ).re := by simpa using hε
  convert (bulkU_integrable M hτ (0 : E3)).norm using 1
  funext k
  simp only [shellDamping, inner_zero_right, Complex.ofReal_zero, mul_zero, add_zero,
    norm_mul, Complex.norm_real, Complex.norm_exp]
  have hnonneg : 0 ≤ shellWeight M k := by unfold shellWeight energy; positivity
  rw [Real.norm_of_nonneg hnonneg]
  congr 2
  simp [Complex.mul_re]

private def conePair (M ε : ℝ) (F : ConeProfile)
    (z : E3 × (Phase4D × Phase4D)) : ℂ :=
  (shellDamping M ε z.1 : ℂ) *
    (star (planeWave M F z.1 z.2.1) * planeWave M F z.1 z.2.2)

private theorem conePair_integrable (M : ℝ) {ε : ℝ} (hε : 0 < ε) (F : ConeProfile) :
    Integrable (conePair M ε F) ((volume : Measure E3).prod (coneMeasure.prod coneMeasure)) :=
  Omega.shellPair_integrable (a := derivativeWeight F) (phase := phase M)
    (shellDamping_integrable M hε) (derivativeWeight_integrable F) (phase_continuous M).measurable

private def coneTime (ε : ℝ) (z : Phase4D × Phase4D) : ℂ :=
  (ε : ℂ) + Complex.I * ((z.1.1 - z.2.1 : ℝ) : ℂ)

private def coneDisplacement (z : Phase4D × Phase4D) : E3 :=
  z.1.1 • (z.1.2 : E3) - z.2.1 • (z.2.2 : E3)

private def bulkIntegrand (M ε : ℝ) (F : ConeProfile) (z : Phase4D × Phase4D) : ℂ :=
  star (derivativeWeight F z.1) * derivativeWeight F z.2 *
    bulkU M (coneTime ε z) (coneDisplacement z)

private theorem bulkIntegrand_eq_inner (M ε : ℝ) (F : ConeProfile)
    (z : Phase4D × Phase4D) :
    (∫ k : E3, conePair M ε F (k, z)) = bulkIntegrand M ε F z := by
  unfold bulkIntegrand coneTime coneDisplacement bulkU
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with k
  simp only [conePair, planeWave, shellDamping, Complex.ofReal_mul, Complex.ofReal_exp,
    star_mul, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  simp only [phase, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_neg]
  rw [show ∀ a b c d e f : ℂ, a * b * (c * d * (e * f)) =
    (d * e) * (a * ((b * c) * f)) by intros; ring]
  simp only [← Complex.exp_add]
  congr 3
  ring

/-- At fixed positive regulator, the square of the plane-wave amplitude equals
the double boundary pairing with the regulated bulk kernel. -/
theorem regulatedShellQuad_eq_bulk (M : ℝ) {ε : ℝ} (hε : 0 < ε) (F : ConeProfile) :
    regulatedShellQuad M ε F =
      (4 * ∫ z : Phase4D × Phase4D,
        star (derivativeWeight F z.1) * derivativeWeight F z.2 *
          bulkU M ((ε : ℂ) + Complex.I * ((z.1.1 - z.2.1 : ℝ) : ℂ))
            (z.1.1 • (z.1.2 : E3) - z.2.1 • (z.2.2 : E3))
        ∂(coneMeasure.prod coneMeasure)).re := by
  have h := Omega.integral_shellWave_norm_sq (a := derivativeWeight F) (phase := phase M)
    (shellDamping_integrable M hε) (derivativeWeight_integrable F) (phase_continuous M).measurable
  change (∫ k : E3, shellDamping M ε k * ‖∫ p, planeWave M F k p ∂coneMeasure‖ ^ 2) =
    (∫ z, ∫ k : E3, conePair M ε F (k,z) ∂volume ∂(coneMeasure.prod coneMeasure)).re at h
  simp_rw [← shellAmplitude_eq_integral, bulkIntegrand_eq_inner] at h
  change (4 * ∫ k, shellDamping M ε k * ‖shellAmplitude M F k‖ ^ 2) =
    (4 * ∫ z, bulkIntegrand M ε F z ∂(coneMeasure.prod coneMeasure)).re
  rw [h]
  simp [Complex.mul_re]

private theorem separation_eq (ε : ℝ) (p q : Phase4D) :
    ((‖p.1 • (p.2 : E3) - q.1 • (q.2 : E3)‖ ^ 2 : ℝ) : ℂ) +
        ((ε : ℂ) + Complex.I * ((p.1 - q.1 : ℝ) : ℂ)) ^ 2 =
      regulatedSeparation ε p.1 q.1 (sphereDot p.2 q.2) := by
  rw [norm_sub_sq_real, norm_smul, norm_smul,
    show ‖(p.2 : E3)‖ = 1 by simp, show ‖(q.2 : E3)‖ = 1 by simp,
    real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs]
  simp only [mul_one, sq_abs, regulatedSeparation, sphereDot]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem profileDeriv_zero_near_origin (F : ConeProfile) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ, 0 < u → u ≤ δ →
      ∀ n : Sphere4D, profileDeriv F u n = 0 := by
  have h : ∀ᶠ u : ℝ in 𝓝 0, ∀ n : Sphere4D, profileDeriv F u n = 0 := by
    induction F with
    | nil => exact .of_forall fun u n => by simp [profileDeriv]
    | cons f F ih =>
      have h₀ : (0 : ℝ) ∉ tsupport f.radial := fun h => by simpa using f.interior h
      have h₁ := (isClosed_tsupport f.radial).isOpen_compl.mem_nhds h₀
      filter_upwards [h₁, ih] with u hu hf n
      have hd : deriv f.radial u = 0 :=
        image_eq_zero_of_notMem_tsupport fun hd => hu (tsupport_deriv_subset hd)
      change deriv f.radial u * f.angular n + profileDeriv F u n = 0
      rw [hd, hf n, zero_mul, zero_add]
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨δ / 2, by positivity, fun u hu hu' n => ?_⟩
  have hm : u ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hu.le] using (show u < δ by linarith)
  exact hb hm n

private theorem abs_sphereDot_le_one (n m : Sphere4D) : |sphereDot n m| ≤ 1 := by
  simpa [sphereDot, show ‖(n : E3)‖ = 1 by simp, show ‖(m : E3)‖ = 1 by simp] using
    abs_real_inner_le_norm (n : E3) (m : E3)

private theorem rearrangeCone :
    MeasurePreserving Omega.pairInterleave (coneMeasure.prod coneMeasure)
      (Omega.ConeCap.pairMeasure sphereMeasure 0) :=
  Omega.measurePreserving_pairInterleave (volume.restrict (Ioo (0 : ℝ) 1)) sphereMeasure

private theorem sphereLog_majorant_integrable :
    Integrable (fun z : Phase4D × Phase4D =>
      1 + |Real.log (1 - sphereDot z.1.2 z.2.2)|) (coneMeasure.prod coneMeasure) := by
  have hi := Omega.integrable_one_add_abs_of_sq _ (by
    apply Measurable.aestronglyMeasurable
    unfold sphereDot
    fun_prop) sphere_log_sq_integrable
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hp := (integrable_const (μ := μ.prod μ) (1 : ℝ)).mul_prod hi
  exact rearrangeCone.integrable_comp_of_integrable (by simpa only [Omega.ConeCap.pairMeasure, Omega.ConeCap.radialMeasure, one_mul] using hp)

private theorem sphereDot_lt_one_ae : ∀ᵐ p ∂sphereMeasure.prod sphereMeasure, sphereDot p.1 p.2 < 1 := by
  have hp : ∀ᵐ p ∂sphereMeasure.prod sphereMeasure, sphereDot p.1 p.2 ≠ 1 := by
    rw [ae_iff]
    simpa only [not_not] using sphere_diag_null
  filter_upwards [hp] with p hp
  exact lt_of_le_of_ne (abs_le.mp (abs_sphereDot_le_one p.1 p.2)).2 hp

private theorem cone_pair_ae (F : ConeProfile) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ z ∂coneMeasure.prod coneMeasure,
      z.1.1 ∈ Ioo (0 : ℝ) 1 ∧ z.2.1 ∈ Ioo (0 : ℝ) 1 ∧
      sphereDot z.1.2 z.2.2 < 1 ∧
      ‖derivativeWeight F z.1‖ ≤ B ∧ ‖derivativeWeight F z.2‖ ≤ B := by
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hr : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  have hr' : ∀ᵐ p ∂coneMeasure, p.1 ∈ Ioo (0 : ℝ) 1 :=
    (μ.quasiMeasurePreserving_fst (ν := sphereMeasure)).ae hr
  have hcone := rearrangeCone.quasiMeasurePreserving.ae
    ((sphereMeasure.prod sphereMeasure).quasiMeasurePreserving_snd (μ := μ.prod μ) |>.ae sphereDot_lt_one_ae)
  obtain ⟨B, hB, hb⟩ := derivativeWeight_memLp F
  refine ⟨B, hB, ?_⟩
  have hf := coneMeasure.quasiMeasurePreserving_fst (ν := coneMeasure)
  have hs := coneMeasure.quasiMeasurePreserving_snd (μ := coneMeasure)
  filter_upwards [hf.ae hr', hs.ae hr', hcone, hf.ae hb, hs.ae hb] with z hu hv hx hb₁ hb₂
  exact ⟨hu, hv, hx, hb₁, hb₂⟩

private def differenceIntegrand (M ε : ℝ) (F : ConeProfile) (z : Phase4D × Phase4D) : ℂ :=
  star (derivativeWeight F z.1) * derivativeWeight F z.2 *
    bulkDifference M (regulatedSeparation ε z.1.1 z.2.1 (sphereDot z.1.2 z.2.2))

private theorem differenceIntegrand_boundary {M : ℝ} (hM : 0 < M) (F : ConeProfile) :
    Tendsto (fun ε : ℝ => ∫ z, differenceIntegrand M ε F z ∂(coneMeasure.prod coneMeasure))
      (𝓝[>] 0) (𝓝 (∫ z, differenceIntegrand M 0 F z ∂(coneMeasure.prod coneMeasure))) ∧
      Integrable (differenceIntegrand M 0 F) (coneMeasure.prod coneMeasure) := by
  obtain ⟨δ, hδ, hzero⟩ := profileDeriv_zero_near_origin F
  obtain ⟨B, hB, hb⟩ := cone_pair_ae F
  let a : Phase4D × Phase4D → ℂ := fun z => star (derivativeWeight F z.1) * derivativeWeight F z.2
  have ha : Measurable a :=
    (((derivativeWeight_continuous F).comp continuous_fst).star.mul
      ((derivativeWeight_continuous F).comp continuous_snd)).measurable
  have hx : Measurable (fun z : Phase4D × Phase4D => sphereDot z.1.2 z.2.2) := by
    unfold sphereDot
    fun_prop
  refine Omega.tendsto_integral_separationPowerLog (a := a)
    (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd) hx ha hM hδ
    (sq_nonneg B) besselP_entire.continuous besselB_entire.continuous
    ((M : ℂ)^2 / (16 * (Real.pi : ℂ)^2)) ?_ ?_ sphereLog_majorant_integrable
  · filter_upwards [hb] with z ⟨hu, hv, hx, huB, hvB⟩
    refine ⟨hu, hv, abs_sphereDot_le_one _ _, hx, ?_⟩
    dsimp only [a]
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul huB hvB (norm_nonneg _) hB
  · filter_upwards [hb] with z hz h
    rcases h with h | h
    · simp [a, derivativeWeight, hzero _ hz.1.1 h.le]
    · simp [a, derivativeWeight, hzero _ hz.2.1.1 h.le]

/-- The difference of regulated shell forms converges to the smeared position-space
boundary correction. -/
theorem regulatedShellQuad_difference_limit {M : ℝ} (hM : 0 < M) (F : ConeProfile) :
    Tendsto (fun ε : ℝ => regulatedShellQuad M ε F - regulatedShellQuad 0 ε F)
      (𝓝[>] (0 : ℝ))
      (𝓝 (4 * ∫ z, differenceIntegrand M 0 F z ∂(coneMeasure.prod coneMeasure)).re) := by
  have hlim := (Complex.continuous_re.continuousAt.tendsto.comp
    ((differenceIntegrand_boundary hM F).1.const_mul (4 : ℂ)))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hi (m : ℝ) : Integrable (bulkIntegrand m ε F) (coneMeasure.prod coneMeasure) := by
    have h := (conePair_integrable m hε F).integral_prod_right
    exact h.congr (Eventually.of_forall (bulkIntegrand_eq_inner m ε F))
  have he (z : Phase4D × Phase4D) :
      differenceIntegrand M ε F z = bulkIntegrand M ε F z - bulkIntegrand 0 ε F z := by
    unfold differenceIntegrand bulkIntegrand
    rw [← mul_sub, bulkU_difference hM (by simpa [coneTime, Complex.mul_re] using hε)]
    exact congrArg (fun q => star (derivativeWeight F z.1) * derivativeWeight F z.2 *
      bulkDifference M q) (separation_eq ε z.1 z.2).symm
  change (4 * ∫ z, differenceIntegrand M ε F z ∂(coneMeasure.prod coneMeasure)).re = _
  simp_rw [he]
  rw [integral_sub (hi M) (hi 0), mul_sub, Complex.sub_re,
    regulatedShellQuad_eq_bulk M hε F, regulatedShellQuad_eq_bulk 0 hε F]
  rfl

/-- The regulated massless bulk kernel in its angular cap normalization. -/
theorem bulkU_zero_cap {ε : ℝ} (hε : 0 < ε) (p q : Phase4D)
    (hu : 0 < p.1) (hv : 0 < q.1) :
    (4 * (p.1 : ℂ) * (q.1 : ℂ)) * bulkU 0 (coneTime ε (p,q)) (coneDisplacement (p,q)) =
      (1 / (2 * (Real.pi : ℂ) ^ 2)) *
        ((1 - (sphereDot p.2 q.2 : ℂ)) + Omega.capShift ε p.1 q.1)⁻¹ := by
  have hτ : 0 < (coneTime ε (p, q)).re := by
    simpa [coneTime, Complex.mul_re] using hε
  rw [bulkU_zero hτ]
  change _ * (1 / (4 * (Real.pi : ℂ) ^ 2 *
    (((‖p.1 • (p.2 : E3) - q.1 • (q.2 : E3)‖ ^ 2 : ℝ) : ℂ) +
      ((ε : ℂ) + Complex.I * ((p.1 - q.1 : ℝ) : ℂ)) ^ 2))) = _
  rw [separation_eq]
  exact Omega.regulatedSeparation_inv_cap hu hv

private theorem sphere_dist_eq (n m : Sphere4D) :
    dist n m = Real.sqrt (2 * (1 - sphereDot n m)) := by
  change dist (n : E3) (m : E3) = _
  rw [dist_eq_norm, ← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
    Real.sq_sqrt (by linarith [(abs_le.mp (abs_sphereDot_le_one n m)).2]),
    norm_sub_sq_real]
  simp [sphereDot]
  ring

private theorem profileDeriv_cap_bounds (F : ConeProfile) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ∀ n, ‖profileDeriv F r n‖ ≤ B) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ∀ n m, ‖profileDeriv F r m - profileDeriv F r n‖ ≤
        C * Real.sqrt (1 - sphereDot n m)) := by
  have compact := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod (isCompact_univ (X := Sphere4D))
  obtain ⟨B, hB⟩ := (compact.image (profileDeriv_continuous F)).isBounded.exists_norm_le
  obtain ⟨C, hC, hc⟩ := Omega.ConeCap.separated_sum_angular_bound F isCompact_Icc
    (fun f => deriv f.radial) ConeProfileTerm.angular
    (fun f => f.smooth.continuous_deriv (by exact_mod_cast le_top)) ConeProfileTerm.lipschitz
  refine ⟨max 0 B, C * Real.sqrt 2, le_max_left _ _, by positivity, ?_, ?_⟩
  · exact fun r hr n => (hB _ ⟨(r,n), ⟨hr, mem_univ _⟩, rfl⟩).trans (le_max_right _ _)
  · intro r hr n m
    have h := hc r hr n m
    rw [sphere_dist_eq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc] at h
    exact h

private theorem modularProfile_deriv_chain (F : ConeProfile) (n : Sphere4D) (s : ℝ) :
    deriv (modularProfile F n) s =
      ((2 * Real.pi * (affineRadius s * (1 - affineRadius s)) : ℝ) : ℂ) *
        profileDeriv F (affineRadius s) n := by
  have hd := (profileValue_hasDerivAt F (affineRadius s) n).scomp s
    (Omega.hasDerivAt_logistic (2 * Real.pi) s)
  have hfun : (modularProfile F n : ℝ → ℂ) = (fun u => profileValue F u n) ∘ affineRadius :=
    funext (modularProfile_apply F n)
  rw [hfun]
  simpa only [affineRadius, Complex.real_smul] using hd.deriv

private theorem massless_shell_eq_cap {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    (F : ConeProfile) (hzero : ∀ u : ℝ, 0 < u → u ≤ δ →
      ∀ n, profileDeriv F u n = 0) :
    regulatedShellQuad 0 ε F =
      ((1 / (2 * (Real.pi : ℂ) ^ 2)) * ∫ z,
        Omega.ConeCap.capIntegrand (fun p : Phase4D => profileDeriv F p.1 p.2) sphereDot ε z
        ∂Omega.ConeCap.pairMeasure sphereMeasure δ).re := by
  let g := Omega.ConeCap.capIntegrand (fun p : Phase4D => profileDeriv F p.1 p.2) sphereDot ε
  rw [regulatedShellQuad_eq_bulk 0 hε F]
  have hcut : (∫ z, g z ∂Omega.ConeCap.pairMeasure sphereMeasure 0) =
      ∫ z, g z ∂Omega.ConeCap.pairMeasure sphereMeasure δ := by
    refine Omega.ConeCap.integral_cap_pair_cut hδ g (fun z hz h => ?_)
    rcases h with h | h
    · simp [g, Omega.ConeCap.capIntegrand, Omega.ConeCap.first, hzero _ hz.1.1 h]
    · simp [g, Omega.ConeCap.capIntegrand, Omega.ConeCap.second, hzero _ hz.2.1 h]
  rw [← hcut]
  have hp : (∫ z, g (Omega.pairInterleave z) ∂coneMeasure.prod coneMeasure) =
      ∫ z, g z ∂Omega.ConeCap.pairMeasure sphereMeasure 0 :=
    rearrangeCone.integral_comp Omega.pairInterleave.measurableEmbedding g
  rw [← hp]
  apply congrArg Complex.re
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  obtain ⟨B, -, hpair⟩ := cone_pair_ae F
  filter_upwards [hpair] with z hz
  have hb := bulkU_zero_cap hε z.1 z.2 hz.1.1 hz.2.1.1
  change _ * (_ * _ * bulkU 0 (coneTime ε z) (coneDisplacement z)) = _
  simp only [derivativeWeight, star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = (star (profileDeriv F z.1.1 z.1.2) * profileDeriv F z.2.1 z.2.2) *
          ((4 * (z.1.1 : ℂ) * (z.2.1 : ℂ)) * bulkU 0 (coneTime ε z) (coneDisplacement z)) := by
      rw [Complex.star_def]
      ring
    _ = _ := by
      rw [hb]
      simp only [g, Omega.ConeCap.capIntegrand, Omega.ConeCap.first, Omega.ConeCap.second,
        Omega.pairInterleave_apply, Complex.ofReal_sub, Complex.ofReal_one, div_eq_mul_inv]
      ring

/-- The positive-regulator massless shell square tends to the modular covariance form. -/
theorem massless_boundary_limit (F : ConeProfile) :
    Tendsto (fun ε : ℝ => regulatedShellQuad 0 ε F) (𝓝[>] (0 : ℝ))
      (𝓝 (⟪profileEmbed F, nullA (profileEmbed F)⟫_ℂ).re) := by
  obtain ⟨δ, hδ, hzero⟩ := profileDeriv_zero_near_origin F
  obtain ⟨B, C, hB, hC, hb, hc⟩ := profileDeriv_cap_bounds F
  let f : Phase4D → ℂ := fun p => profileDeriv F p.1 p.2
  have ha : ∀ n, (∫ r, f (r,n) ∂Omega.ConeCap.radialMeasure δ) = 0 := by
    intro n
    rw [← Omega.ConeCap.integral_radial_cut hδ.le _ (fun r hr le => hzero r hr.1 le n)]
    exact Omega.integral_affine_derivative_eq_zero _ (modularProfile_compact F n)
      (modularProfile_deriv_chain F n)
  have hσ : 0 < sphereMeasure.real univ := by
    rw [Measure.real, sphere_measure_univ, ENNReal.toReal_ofReal (by positivity)]
    positivity
  have hdot : Measurable (Function.uncurry sphereDot) := by unfold sphereDot; fun_prop
  have hl := Omega.ConeCap.cap_boundary hdot (by positivity : 0 < 2 * Real.pi)
    sphere_dot_pushforward (fun n m => (abs_le.mp (abs_sphereDot_le_one n m)).2)
    hσ (profileDeriv_continuous F).measurable hδ hB hC
    (fun r hr => hb r ⟨(hδ.trans hr.1).le, hr.2.le⟩)
    (fun r hr => hc r ⟨(hδ.trans hr.1).le, hr.2.le⟩) ha
  have he (n : Sphere4D) : -(Real.pi : ℂ)⁻¹ * Omega.ConeCap.affineLogIntegral δ f n =
      Omega.modularLogPairing (modularProfile F n) (modularProfile F n) := by
    have hcut : Omega.ConeCap.affineLogIntegral 0 f n = Omega.ConeCap.affineLogIntegral δ f n := by
      apply Omega.ConeCap.integral_radial_pair_cut hδ.le
      intro p hp h
      rcases h with h | h
      · simp [f, hzero _ hp.1.1 h]
      · simp [f, hzero _ hp.2.1 h]
    rw [← hcut]
    have hh := (profileDeriv_continuous F).comp (continuous_id.prodMk (continuous_const (y := n)))
    exact Omega.affine_log_pairing_eq_modular _ _
      (F' := fun u => profileDeriv F u n) (G' := fun u => profileDeriv F u n)
      (modularProfile_compact F n)
      (modularProfile_compact F n) hh hh (modularProfile_deriv_chain F n) (modularProfile_deriv_chain F n)
  have hk : (1 / (2 * (Real.pi : ℂ) ^ 2)) *
      (-(↑(2 * Real.pi) : ℂ) * ∫ n, Omega.ConeCap.affineLogIntegral δ f n ∂sphereMeasure) =
      ⟪profileEmbed F, nullA (profileEmbed F)⟫_ℂ := by
    rw [← profile_modular_log_pairing, ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with n
    rw [← he n]
    push_cast
    field_simp [show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (hl.const_mul (1 / (2 * (Real.pi : ℂ) ^ 2)))
  rw [hk] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (massless_shell_eq_cap hε hδ.le F hzero).symm

private theorem affineBulkKernel_smooth {M x : ℝ} (hM : 0 < M) (hx : x < 1) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ((p.1 * p.2 : ℝ) : ℂ) *
      bulkDifference M ((2 * p.1 * p.2 * (1 - x) : ℝ) : ℂ)) (Ioi 0 ×ˢ Ioi 0) := by
  have hA (q : ℝ) (hq : 0 < q) : AnalyticAt ℂ (bulkDifference M) q := by
    let t : ℂ → ℂ := fun z => (M : ℂ)^2 * z / 4
    have ht : AnalyticAt ℂ t q := by unfold t; fun_prop
    have htpos : 0 < (t q).re := by
      change 0 < (((M : ℂ)^2 * (q : ℂ)) / (4 : ℂ)).re
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_ofNat,
        ← Complex.ofReal_div, Complex.ofReal_re]
      positivity
    exact analyticAt_const.mul (((ht.clog (Complex.mem_slitPlane_iff.mpr (Or.inl htpos))).mul
      ((besselP_entire.analyticAt _).comp ht)).sub ((besselB_entire.analyticAt _).comp ht))
  refine (Omega.contDiffOn_mul_of_real_product (a := 2 * (1 - x)) (by positivity) hA).congr ?_
  intro p _
  rw [show 2 * p.1 * p.2 * (1 - x) = 2 * (1 - x) * p.1 * p.2 by ring]

private theorem affineBulkKernel_eq_stripG {M x : ℝ} (hM : 0 < M) (hx : x < 1)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hf₀ : tsupport f ⊆ Ioo 0 1) (hg₀ : tsupport g ⊆ Ioo 0 1) :
    4 * (∫ p : ℝ × ℝ, star (deriv f p.1) *
      (((p.1 * p.2 : ℝ) : ℂ) * bulkDifference M ((2 * p.1 * p.2 * (1 - x) : ℝ) : ℂ)) *
      deriv g p.2 ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) =
      ∫ s : ℝ, ∫ t : ℝ, star (f (Omega.logistic (2 * Real.pi) s)) *
        stripG M s t x * g (Omega.logistic (2 * Real.pi) t) := by
  have hb : 0 < 2 * Real.pi := by positivity
  have hp (s : ℝ) : 0 < Omega.logistic (2 * Real.pi) s := by
    have hs : Omega.logistic (2 * Real.pi) s ∈ range (Omega.logistic (2 * Real.pi)) := ⟨s, rfl⟩
    rw [Omega.range_logistic hb] at hs
    exact hs.1
  rw [Omega.integral_compact_pairing_eq_logistic hb hf hg hf₀ hg₀ (affineBulkKernel_smooth hM hx),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [stripG_real M s t x hM hx, show (modularU (s : ℂ)).re = _ from (Omega.logistic_complex_coordinates s).1,
    show (modularU (t : ℂ)).re = _ from (Omega.logistic_complex_coordinates t).1,
    show modularUprime (s : ℂ) = _ from (Omega.logistic_complex_coordinates s).2,
    show modularUprime (t : ℂ) = _ from (Omega.logistic_complex_coordinates t).2,
    correction_mixed_deriv hM (hp s) (hp t) hx]
  ring

private abbrev scale := 2 * Real.pi

private theorem stripG_slice_integrable {M x : ℝ} (hM : 0 < M) (hx : -1 ≤ x) :
    Integrable (fun p : ℝ × ℝ => stripG M p.1 p.2 x) (volume.prod volume) := by
  by_cases hx' : x < 1
  · obtain ⟨C, hC, h⟩ := stripG_bound M hM
    refine Omega.integrable_of_exponential_pair_bound ?_ hC.le (abs_nonneg (Real.log (1 - x))) Real.pi_pos
      (integrable_exp_neg_mul_abs Real.pi_pos) (fun p => ?_)
    · have hP := besselP2_entire.continuous.measurable
      have hB := besselB2_entire.continuous.measurable
      unfold stripG correctionLog modularU modularUprime liftedLog
      simp only [ite_eq_left hx']
      exact Measurable.aestronglyMeasurable (by fun_prop)
    · have hmem (r : ℝ) : (r : ℂ) ∈ closedStrip := by norm_num [closedStrip, stripB]
      simpa only [Complex.ofReal_re] using h (p.1 : ℂ) (p.2 : ℂ) (hmem _) (hmem _) x hx hx'
  · simp [stripG, hx']

private theorem fourierG_eq_mixed (M x ξ η : ℝ)
    (hi : Integrable (fun p : ℝ × ℝ => stripG M p.1 p.2 x) (volume.prod volume)) :
    fourierG M (scale * ξ) (scale * η) x = (scale : ℂ)⁻¹ *
      Omega.mixedFourier (fun p : ℝ × ℝ => stripG M p.1 p.2 x) (ξ, η) := by
  rw [Omega.mixedFourier_eq_iterated_exp _ hi]
  simp only [fourierG, one_div, show (scale : ℂ) = 2 * (Real.pi : ℂ) by simp [scale]]
  rfl

private theorem profileFourier_bounded_continuous (F : ConeProfile) :
    Continuous (profileFourier F) ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖profileFourier F p‖ ≤ B := by
  change Continuous (fun p : Phase4D => profileFourier F (p.1, p.2)) ∧ _
  unfold profileFourier
  apply Omega.continuous_bounded_listSum
  intro f
  change Continuous (fun p : Phase4D => (Real.sqrt scale : ℂ)⁻¹ *
    (𝓕 (_ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) (scale⁻¹ * p.1) * f.angular p.2) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : Phase4D, ‖(Real.sqrt scale : ℂ)⁻¹ *
      (𝓕 (_ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) (scale⁻¹ * p.1) * f.angular p.2‖ ≤ B
  exact Omega.bounded_continuous_separated_fourier _ _ f.lipschitz.choose_spec.continuous _ _

private theorem massive_frequency_integrable {M : ℝ} (hM : 0 < M) (F : ConeProfile) :
    Integrable (fun p : Phase4D × Phase4D => star (profileFourier F p.1) *
      fourierG M p.1.1 p.2.1 (sphereDot p.1.2 p.2.2) * profileFourier F p.2)
      (phaseMeasure.prod phaseMeasure) := by
  obtain ⟨C, hC, hc⟩ := fourierG_bound M hM
  obtain ⟨hm, B, hB, hb⟩ := profileFourier_bounded_continuous F
  let e (s : ℝ) := Real.exp (-(stripB * |s|))
  let l (n : Sphere4D × Sphere4D) := 1 + |Real.log (1 - sphereDot n.1 n.2)|
  let coords : Phase4D × Phase4D → ℝ × ℝ × ℝ := fun p =>
    (p.1.1, p.2.1, sphereDot p.1.2 p.2.2)
  have hcoords : Measurable coords := by dsimp [coords, sphereDot]; fun_prop
  let L := (fun x : ℝ × ℝ × ℝ => fourierG M x.1 x.2.1 x.2.2) ∘ coords
  have hLm : Measurable L := (fourierG_measurable M).comp hcoords
  have hl : Integrable l (sphereMeasure.prod sphereMeasure) := by
    refine Omega.integrable_one_add_abs_of_sq _ ?_ sphere_log_sq_integrable
    exact (show Measurable (fun n : Sphere4D × Sphere4D =>
      Real.log (1 - sphereDot n.1 n.2)) from by unfold sphereDot; fun_prop).aestronglyMeasurable
  refine Omega.integrable_pairing_of_product_bound sphereMeasure (profileFourier F)
    hm.measurable hB hb L hLm e (integrable_exp_neg_mul_abs (by norm_num [stripB]))
    (fun _ => (Real.exp_pos _).le) l hl (fun _ => by dsimp [l]; positivity) hC.le ?_
  filter_upwards [(Omega.measurePreserving_pairInterleave volume sphereMeasure).quasiMeasurePreserving.ae
    (((sphereMeasure.prod sphereMeasure).quasiMeasurePreserving_snd (μ := volume.prod volume)).ae
      sphereDot_lt_one_ae)] with p hx
  have hk := hc p.1.1 p.2.1 (sphereDot p.1.2 p.2.2) (abs_le.mp (abs_sphereDot_le_one _ _)).1 hx
  rw [show -stripB * (|p.1.1| + |p.2.1|) =
    -(stripB * |p.1.1|) + -(stripB * |p.2.1|) by ring, Real.exp_add] at hk
  exact hk

private theorem massive_modular_pairing {M : ℝ} (hM : 0 < M) (F : ConeProfile) :
    (∫ n : Sphere4D × Sphere4D, ∫ p : ℝ × ℝ,
      star (modularProfile F n.1 p.1) * stripG M p.1 p.2 (sphereDot n.1 n.2) *
        modularProfile F n.2 p.2 ∂((volume : Measure ℝ).prod volume)
        ∂(sphereMeasure.prod sphereMeasure)) =
      ⟪profileEmbed F, nullT M hM (profileEmbed F)⟫_ℂ := by
  rw [profile_nullT_pairing hM F]
  refine (Omega.angular_mixedFourier_pairing sphereMeasure (modularProfile F)
    (fun n p => stripG M p.1 p.2 (sphereDot n.1 n.2))
    (fun n p => fourierG M p.1 p.2 (sphereDot n.1 n.2)) (profileFourier F)
    (b := scale) (by positivity [Real.pi_pos]) (.of_forall fun n =>
      stripG_slice_integrable hM (abs_le.mp (abs_sphereDot_le_one n.1 n.2)).1)
    (fun n ξ η => fourierG_eq_mixed M (sphereDot n.1 n.2) ξ η
      (stripG_slice_integrable hM (abs_le.mp (abs_sphereDot_le_one n.1 n.2)).1))
    (fun n ξ => ?_) (massive_frequency_integrable hM F)).symm
  have h := profileFourier_modular F (scale * ξ) n
  change profileFourier F (scale * ξ, n) = (Real.sqrt scale : ℂ)⁻¹ *
    𝓕 (modularProfile F n) (scale⁻¹ * (scale * ξ)) at h
  simpa only [inv_mul_cancel_left₀ (by positivity [Real.pi_pos] : scale ≠ 0)] using h

private theorem profileValue_smooth_support (F : ConeProfile) (n : Sphere4D) :
    ContDiff ℝ 1 (fun u => profileValue F u n) ∧
    tsupport (fun u => profileValue F u n) ⊆ Ioo 0 1 := by
  induction F with
  | nil =>
    simp [profileValue, contDiff_const]
  | cons f F ih =>
    change ContDiff ℝ 1 (fun u => f.radial u * f.angular n + profileValue F u n) ∧ _
    refine ⟨((f.smooth.of_le (by simp)).mul contDiff_const).add ih.1, ?_⟩
    exact (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_left.trans f.interior) ih.2)

private theorem differenceIntegrand_eq_nullT {M : ℝ} (hM : 0 < M) (F : ConeProfile) :
    (4 * ∫ z, differenceIntegrand M 0 F z ∂(coneMeasure.prod coneMeasure)) =
      ⟪profileEmbed F, nullT M hM (profileEmbed F)⟫_ℂ := by
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  change (4 * ∫ z, differenceIntegrand M 0 F z ∂((μ.prod sphereMeasure).prod
    (μ.prod sphereMeasure))) = _
  rw [Omega.integral_pairInterleave μ sphereMeasure _ (differenceIntegrand_boundary hM F).2,
    ← integral_const_mul, ← massive_modular_pairing hM F]
  apply integral_congr_ae
  filter_upwards [sphereDot_lt_one_ae] with n hn
  have h₁ := profileValue_smooth_support F n.1
  have h₂ := profileValue_smooth_support F n.2
  have he (p : ℝ × ℝ) : differenceIntegrand M 0 F ((p.1,n.1), (p.2,n.2)) =
      star (deriv (fun u => profileValue F u n.1) p.1) *
        (((p.1 * p.2 : ℝ) : ℂ) * bulkDifference M
          ((2 * p.1 * p.2 * (1 - sphereDot n.1 n.2) : ℝ) : ℂ)) *
        deriv (fun u => profileValue F u n.2) p.2 := by
    simp only [differenceIntegrand, derivativeWeight, regulatedSeparation, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, add_zero, Complex.ofReal_zero, star_mul, Complex.star_def,
      Complex.conj_ofReal, Complex.ofReal_mul, (profileValue_hasDerivAt F _ _).deriv]
    ring
  simp_rw [he]
  rw [affineBulkKernel_eq_stripG hM hn h₁.1 h₂.1 h₁.2 h₂.2]
  symm
  have hk := stripG_slice_integrable hM (x := sphereDot n.1 n.2)
    (abs_le.mp (abs_sphereDot_le_one n.1 n.2)).1
  rw [integral_prod _ (Omega.integrable_schwartz_kernel_pairing _ hk
    (modularProfile F n.1) (modularProfile F n.2))]
  simp_rw [modularProfile_apply]
  rfl

/-- At positive mass the right boundary includes the same correction as the Fourier kernel. -/
theorem massive_boundary_limit {M : ℝ} (hM : 0 < M) (F : ConeProfile) :
    Tendsto (fun ε : ℝ => regulatedShellQuad M ε F) (𝓝[>] (0 : ℝ))
      (𝓝 (⟪profileEmbed F, (nullA + nullT M hM) (profileEmbed F)⟫_ℂ).re) := by
  have h := regulatedShellQuad_difference_limit hM F
  rw [differenceIntegrand_eq_nullT hM F] at h
  simpa only [sub_add_cancel, _root_.add_apply, inner_add_right, Complex.add_re,
    add_comm _ (⟪profileEmbed F, nullA (profileEmbed F)⟫_ℂ).re] using
    h.add (massless_boundary_limit F)

end NullConeGravity
