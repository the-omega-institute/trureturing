/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary5D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary5D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regulated null-cone shell forms and weak boundary pairing. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernel5D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondProfileFourier4D
import OmegaMath.Analysis.SemicircleConeCap
import OmegaMath.Analysis.RegulatedHalfPowerDifference
import OmegaMath.Analysis.CompactKernelPairing
import OmegaMath.Analysis.FourSpatialConeShell

/-! Regulated mass shells, the angular boundary limits, and the positive covariance. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter ContinuousLinearMap
open scoped InnerProductSpace Topology ENNReal NNReal FourierTransform ComplexOrder
open D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability
open Omega (regulatedSeparation principalRoot kernelG5D fourierG5D fourierG5D_measurable)
namespace NullConeGravity

open Omega.ConeProfiles (profileDeriv_zero_near_origin profileValue_smooth_support modularProfile_deriv_chain profileFourier_bounded_continuous)

open private weight_sub_eq radial_symbol from
  D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondProfileFourier4D
open private powerOp_ae wgt_measurable from
  D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernel5D

export Omega.FourSpatialMassShell (bulkU5D)

abbrev ConeProfile5D := Omega.ConeProfiles.ConeProfile Sphere5D

/-- The weighted modular Fourier embedding of five-dimensional cone profiles. -/
def profileEmbed5D (F : ConeProfile5D) : H5D :=
  Omega.ConeProfiles.profileEmbed wgt wgt_measurable wgt_bounds sphere5DMeasure F

theorem profileEmbed5D_dense : DenseRange profileEmbed5D :=
  Omega.ConeProfiles.profileEmbed_dense wgt wgt_measurable wgt_bounds sphere5DMeasure

private theorem profileEmbed5D_ae (F : ConeProfile5D) :
    (profileEmbed5D F : Phase5D → ℂ) =ᵐ[phase5DMeasure]
      fun p => (Real.sqrt (wgt p.1) : ℂ) * Omega.ConeProfiles.profileFourier F p :=
  Omega.ConeProfiles.profileEmbed_ae wgt wgt_measurable wgt_bounds sphere5DMeasure F

/-- The massless shell kernel on the regulated half-plane, in principal-power notation. -/
theorem bulkU5D_zero {τ : ℂ} (hτ : 0 < τ.re) (r : E4) :
    bulkU5D 0 τ r = 1 / (8 * (Real.pi : ℂ) ^ 2 *
      (((‖r‖ ^ 2 : ℝ) : ℂ) + τ ^ 2) ^ (3 / 2 : ℂ)) := by
  let q : ℂ := ((‖r‖ ^ 2 : ℝ) : ℂ) + τ ^ 2
  have hn : q ≠ 0 := by
    intro h
    have hr : q.re = 0 := by rw [h]; rfl
    have hi : q.im = 0 := by rw [h]; rfl
    simp only [q, pow_two, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im] at hi
    have him : τ.im = 0 := by
      have hm : τ.re * τ.im = 0 := by nlinarith [hi]
      exact (mul_eq_zero.mp hm).resolve_left hτ.ne'
    simp only [q, pow_two, Complex.add_re, Complex.ofReal_re, Complex.mul_re, him,
      mul_zero, sub_zero] at hr
    nlinarith [sq_nonneg ‖r‖]
  rw [Omega.FourSpatialMassShell.bulkU5D_elementary (M := 0) le_rfl hτ]
  change Omega.FourSpatialMassShell.elementary 0 q = _
  simp only [Omega.FourSpatialMassShell.elementary, Complex.ofReal_zero, neg_zero, zero_mul,
    Complex.exp_zero, add_zero, mul_one]
  rw [show (3 / 2 : ℂ) = 1 + 1 / 2 by norm_num, Complex.cpow_add _ _ hn, Complex.cpow_one]

/-- The spectral difference agrees with the bulk kernel used in the frozen correction. -/
theorem bulkU5D_difference {M : ℝ} (hM : 0 ≤ M) {τ : ℂ} (hτ : 0 < τ.re) (r : E4) :
    bulkU5D M τ r - bulkU5D 0 τ r = bulkDiff5D M (((‖r‖ ^ 2 : ℝ) : ℂ) + τ ^ 2) := by
  rw [Omega.FourSpatialMassShell.bulkU5D_elementary hM hτ,
    Omega.FourSpatialMassShell.bulkU5D_elementary (M := 0) le_rfl hτ]
  simp only [Omega.FourSpatialMassShell.elementary, bulkDiff5D, Complex.ofReal_zero, neg_zero,
    zero_mul, Complex.exp_zero, add_zero, mul_one, div_eq_mul_inv, mul_inv_rev]
  ring

open Omega.FourSpatialConeShell (fluxWeight fluxWeight_rpow coneTime derivativeWeight capPrefactor)
private abbrev coneMeasure := Omega.FourSpatialConeShell.coneMeasure sphere5DMeasure
private abbrev coneDisplacement := Omega.FourSpatialConeShell.coneDisplacement
  ((↑) : Sphere5D → E4)
private abbrev bulkIntegrand := Omega.FourSpatialConeShell.bulkIntegrand
  ((↑) : Sphere5D → E4)
private local instance : IsFiniteMeasure coneMeasure := by
  unfold coneMeasure Omega.FourSpatialConeShell.coneMeasure
  infer_instance

private abbrev profileDeriv_continuous := Omega.ConeProfiles.profileDeriv_continuous
  (A := Sphere5D)
private abbrev derivativeWeight_continuous := Omega.FourSpatialConeShell.derivativeWeight_continuous
  (A := Sphere5D)
private abbrev derivativeWeight_memLp := Omega.FourSpatialConeShell.derivativeWeight_memLp
  sphere5DMeasure
private abbrev conePair := Omega.FourSpatialConeShell.conePair ((↑) : Sphere5D → E4)
private abbrev conePair_integrable := Omega.FourSpatialConeShell.conePair_integrable
  ((↑) : Sphere5D → E4) sphere5DMeasure continuous_subtype_val
private abbrev bulkIntegrand_eq_inner := Omega.FourSpatialConeShell.bulkIntegrand_eq_inner
  ((↑) : Sphere5D → E4)

def shellAmplitude5D := Omega.FourSpatialConeShell.amplitude ((↑) : Sphere5D → E4) sphere5DMeasure

def regulatedShellQuad5D := Omega.FourSpatialConeShell.regulatedQuad
  ((↑) : Sphere5D → E4) sphere5DMeasure

theorem regulatedShellQuad5D_nonneg (M ε : ℝ) (F : ConeProfile5D) :
    0 ≤ regulatedShellQuad5D M ε F :=
  Omega.FourSpatialConeShell.regulatedQuad_nonneg _ _ M ε F

theorem regulatedShellQuad5D_eq_bulk (M : ℝ) {ε : ℝ} (hε : 0 < ε) (F : ConeProfile5D) :
    regulatedShellQuad5D M ε F =
      (4 * ∫ z, bulkIntegrand M ε F z ∂(coneMeasure.prod coneMeasure)).re :=
  Omega.FourSpatialConeShell.regulatedQuad_eq_bulk _ _ continuous_subtype_val M hε F

private theorem separation_eq (ε : ℝ) (p q : Phase5D) :
    ((‖p.1 • (p.2 : E4) - q.1 • (q.2 : E4)‖ ^ 2 : ℝ) : ℂ) +
        ((ε : ℂ) + Complex.I * ((p.1 - q.1 : ℝ) : ℂ)) ^ 2 =
      regulatedSeparation ε p.1 q.1 (sphere5DDot p.2 q.2) := by
  rw [norm_sub_sq_real, norm_smul, norm_smul,
    show ‖(p.2 : E4)‖ = 1 by simp, show ‖(q.2 : E4)‖ = 1 by simp,
    real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs]
  simp only [mul_one, sq_abs, regulatedSeparation, sphere5DDot]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring
private theorem abs_sphereDot_le_one (n m : Sphere5D) : |sphere5DDot n m| ≤ 1 := by
  simpa [sphere5DDot, show ‖(n : E4)‖ = 1 by simp, show ‖(m : E4)‖ = 1 by simp] using
    abs_real_inner_le_norm (n : E4) (m : E4)

private theorem rearrangeCone :
    MeasurePreserving Omega.pairInterleave (coneMeasure.prod coneMeasure)
      (Omega.ConeCap.pairMeasure sphere5DMeasure 0) :=
  Omega.measurePreserving_pairInterleave (volume.restrict (Ioo (0 : ℝ) 1)) sphere5DMeasure
private theorem sphereDot_lt_one_ae : ∀ᵐ p ∂sphere5DMeasure.prod sphere5DMeasure, sphere5DDot p.1 p.2 < 1 := by
  have hp : ∀ᵐ p ∂sphere5DMeasure.prod sphere5DMeasure, sphere5DDot p.1 p.2 ≠ 1 := by
    rw [ae_iff]
    simpa only [not_not] using sphere5D_diag_null
  filter_upwards [hp] with p hp
  exact lt_of_le_of_ne (abs_le.mp (abs_sphereDot_le_one p.1 p.2)).2 hp
private theorem cone_pair_ae (F : ConeProfile5D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ z ∂coneMeasure.prod coneMeasure,
      z.1.1 ∈ Ioo (0 : ℝ) 1 ∧ z.2.1 ∈ Ioo (0 : ℝ) 1 ∧
      sphere5DDot z.1.2 z.2.2 < 1 ∧
      ‖derivativeWeight F z.1‖ ≤ B ∧ ‖derivativeWeight F z.2‖ ≤ B := by
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hr : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  have hr' : ∀ᵐ p ∂coneMeasure, p.1 ∈ Ioo (0 : ℝ) 1 :=
    (μ.quasiMeasurePreserving_fst (ν := sphere5DMeasure)).ae hr
  have hcone := rearrangeCone.quasiMeasurePreserving.ae
    ((sphere5DMeasure.prod sphere5DMeasure).quasiMeasurePreserving_snd (μ := μ.prod μ) |>.ae sphereDot_lt_one_ae)
  obtain ⟨B, hB, hb⟩ := derivativeWeight_memLp F
  refine ⟨B, hB, ?_⟩
  have hf := coneMeasure.quasiMeasurePreserving_fst (ν := coneMeasure)
  have hs := coneMeasure.quasiMeasurePreserving_snd (μ := coneMeasure)
  filter_upwards [hf.ae hr', hs.ae hr', hcone, hf.ae hb, hs.ae hb] with z hu hv hx hb₁ hb₂
  exact ⟨hu, hv, hx, hb₁, hb₂⟩

private theorem bulkDiff_eq (M : ℝ) : bulkDiff5D M = Omega.halfPowerDifference M := by
  funext q
  simp only [bulkDiff5D, Omega.halfPowerDifference, Omega.principalRoot,
    show (1 / 2 : ℂ) = 2⁻¹ by ring]

private def differenceIntegrand (M ε : ℝ) (F : ConeProfile5D) (z : Phase5D × Phase5D) : ℂ :=
  star (derivativeWeight F z.1) * derivativeWeight F z.2 *
    bulkDiff5D M (regulatedSeparation ε z.1.1 z.2.1 (sphere5DDot z.1.2 z.2.2))
private theorem sphere_dist_eq (n m : Sphere5D) :
    dist n m = Real.sqrt (2 * (1 - sphere5DDot n m)) := by
  change dist (n : E4) (m : E4) = _
  rw [dist_eq_norm, ← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
    Real.sq_sqrt (by linarith [(abs_le.mp (abs_sphereDot_le_one n m)).2]),
    norm_sub_sq_real]
  simp [sphere5DDot]
  ring
private theorem profileDeriv_cap_bounds (F : ConeProfile5D) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ∀ n, ‖Omega.ConeProfiles.profileDeriv F r n‖ ≤ B) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ∀ n m, ‖Omega.ConeProfiles.profileDeriv F r m - Omega.ConeProfiles.profileDeriv F r n‖ ≤
        C * Real.sqrt (1 - sphere5DDot n m)) := by
  have compact := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod (isCompact_univ (X := Sphere5D))
  obtain ⟨B, hB⟩ := (compact.image (profileDeriv_continuous F)).isBounded.exists_norm_le
  obtain ⟨C, hC, hc⟩ := Omega.ConeCap.separated_sum_angular_bound F isCompact_Icc
    (fun f => deriv f.radial) Omega.ConeProfiles.ConeProfileTerm.angular
    (fun f => f.smooth.continuous_deriv (by exact_mod_cast le_top)) Omega.ConeProfiles.ConeProfileTerm.lipschitz
  refine ⟨max 0 B, C * Real.sqrt 2, le_max_left _ _, by positivity, ?_, ?_⟩
  · exact fun r hr n => (hB _ ⟨(r,n), ⟨hr, mem_univ _⟩, rfl⟩).trans (le_max_right _ _)
  · intro r hr n m
    have h := hc r hr n m
    rw [sphere_dist_eq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc] at h
    exact h
private theorem profile_massless_pairing_ae (F : ConeProfile5D) :
    (fun p : Phase5D => ⟪profileEmbed5D F p, nullA5D (profileEmbed5D F) p⟫_ℂ) =ᵐ[phase5DMeasure]
      fun p => ((wgt p.1 - p.1 : ℝ) : ℂ) * (‖Omega.ConeProfiles.profileFourier F p‖ ^ 2 : ℝ) := by
  let f := profileEmbed5D F
  have hA : (nullA5D f : Phase5D → ℂ) =ᵐ[phase5DMeasure]
      fun p => ((a p.1 : ℝ) : ℂ) * f p := by
    exact (powerOp_ae zero_le_one f).trans (.of_forall fun p => by
      change (↑(a p.1 ^ (1 : ℝ)) : ℂ) * f p = _
      rw [Real.rpow_one])
  have hF := profileEmbed5D_ae F
  filter_upwards [hA, hF] with p hp hf
  rw [RCLike.inner_apply, hp]
  change (a p.1 : ℂ) * f p * star (f p) = _
  rw [hf, mul_assoc, Complex.star_def, Complex.mul_conj, ← Complex.sq_norm,
    norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by linarith [(wgt_bounds p.1).1]), weight_sub_eq]
  push_cast
  ring

/-- The multiplier of the massless operator pairing in unweighted Fourier coordinates. -/
private theorem profile_nullA5D_pairing (F : ConeProfile5D) :
    ⟪profileEmbed5D F, nullA5D (profileEmbed5D F)⟫_ℂ =
      ∫ p, ((wgt p.1 - p.1 : ℝ) : ℂ) * (‖Omega.ConeProfiles.profileFourier F p‖ ^ 2 : ℝ) ∂phase5DMeasure := by
  rw [L2.inner_def]
  exact integral_congr_ae (profile_massless_pairing_ae F)

/-- The quadratic logarithmic form in the modular radial variable equals the
spectral pairing against the massless multiplier on the given phase space. -/
private theorem profile_modular_log_pairing_5D (F : ConeProfile5D) :
    (∫ n : Sphere5D, Omega.modularLogPairing (Omega.ConeProfiles.modularProfile F n) (Omega.ConeProfiles.modularProfile F n)
      ∂sphere5DMeasure) = ⟪profileEmbed5D F, nullA5D (profileEmbed5D F)⟫_ℂ := by
  let P : Phase5D → ℂ := fun p =>
    ((wgt p.1 - p.1 : ℝ) : ℂ) * (‖Omega.ConeProfiles.profileFourier F p‖ ^ 2 : ℝ)
  have hi : Integrable P phase5DMeasure := (L2.integrable_inner (profileEmbed5D F)
    (nullA5D (profileEmbed5D F))).congr (profile_massless_pairing_ae F)
  rw [profile_nullA5D_pairing F]
  change _ = ∫ p, P p ∂phase5DMeasure
  have hprod := integral_prod_symm P hi
  refine Eq.trans ?_ hprod.symm
  apply integral_congr_ae
  filter_upwards with n
  rw [Omega.modularLogPairing_eq_fourier _ _ (Omega.ConeProfiles.modularProfile_compact F n)
    (Omega.ConeProfiles.modularProfile_compact F n)]
  have hscale := Measure.integral_comp_mul_left (fun ν => P (ν, n)) Omega.ConeProfiles.frequencyScale
  rw [abs_of_nonneg (inv_nonneg.mpr Omega.ConeProfiles.frequencyScale_pos.le)] at hscale
  rw [← inv_smul_smul₀ (inv_ne_zero Omega.ConeProfiles.frequencyScale_pos.ne') (∫ ν, P (ν, n)), ← hscale,
    inv_inv, Complex.real_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [show 2 * Real.pi * ξ = Omega.ConeProfiles.frequencyScale * ξ from rfl]
  have hs : 2 + (Omega.ConeProfiles.frequencyScale * ξ) ^ 2 / Real.pi *
      (𝓕 Omega.logTail ξ).re - Omega.ConeProfiles.frequencyScale * ξ =
      wgt (Omega.ConeProfiles.frequencyScale * ξ) - Omega.ConeProfiles.frequencyScale * ξ :=
    radial_symbol ξ
  rw [hs]
  dsimp only [P]
  rw [Omega.ConeProfiles.profileFourier_modular, ← mul_assoc, Complex.star_def]
  rw [show ∀ c b : ℂ, (starRingEnd ℂ) b * c * b = c * (b * (starRingEnd ℂ) b)
    by intro c b; ring]
  rw [Complex.mul_conj, ← Complex.sq_norm, inv_mul_cancel_left₀ Omega.ConeProfiles.frequencyScale_pos.ne']
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt Omega.ConeProfiles.frequencyScale_pos.le]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Omega.ConeProfiles.frequencyScale_pos.ne']

/-- In the unweighted Fourier representation the two square roots in the
profile embeddings cancel the two weights in the existing correction kernel. -/
private theorem profile_nullT5D_pairing {M : ℝ} (hM : 0 < M) (F : ConeProfile5D) :
    ⟪profileEmbed5D F, nullT5D M hM (profileEmbed5D F)⟫_ℂ =
      ∫ p : Phase5D × Phase5D,
        star (Omega.ConeProfiles.profileFourier F p.1) *
          fourierG5D M p.1.1 p.2.1 (sphere5DDot p.1.2 p.2.2) *
          Omega.ConeProfiles.profileFourier F p.2 ∂(phase5DMeasure.prod phase5DMeasure) := by
  let f := profileEmbed5D F
  unfold nullT5D
  refine (integralKernelOp_inner phase5DMeasure _ _ f f).trans ?_
  apply integral_congr_ae
  have hf := profileEmbed5D_ae F
  filter_upwards [(phase5DMeasure.quasiMeasurePreserving_fst (ν := phase5DMeasure)).ae hf,
    (phase5DMeasure.quasiMeasurePreserving_snd (μ := phase5DMeasure)).ae hf] with p h₁ h₂
  have hn (ν : ℝ) : (Real.sqrt (wgt ν) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by linarith [(wgt_bounds ν).1]))
  rw [h₁, h₂, tKernel5D, Complex.ofReal_mul]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
  field_simp [hn]

private theorem massless_shell_eq_cap {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    (F : ConeProfile5D) (hzero : ∀ u : ℝ, 0 < u → u ≤ δ →
      ∀ n, Omega.ConeProfiles.profileDeriv F u n = 0) :
    regulatedShellQuad5D 0 ε F =
      (capPrefactor * ∫ z,
        Omega.ConeCap.halfCapIntegrand (fun p : Phase5D => Omega.ConeProfiles.profileDeriv F p.1 p.2) sphere5DDot ε z
        ∂Omega.ConeCap.pairMeasure sphere5DMeasure δ).re := by
  let g := Omega.ConeCap.halfCapIntegrand (fun p : Phase5D => Omega.ConeProfiles.profileDeriv F p.1 p.2) sphere5DDot ε
  rw [regulatedShellQuad5D_eq_bulk 0 hε F]
  have hcut : (∫ z, g z ∂Omega.ConeCap.pairMeasure sphere5DMeasure 0) =
      ∫ z, g z ∂Omega.ConeCap.pairMeasure sphere5DMeasure δ := by
    refine Omega.ConeCap.integral_cap_pair_cut hδ g (fun z hz h => ?_)
    rcases h with h | h
    · simp [g, Omega.ConeCap.halfCapIntegrand, Omega.ConeCap.first, hzero _ hz.1.1 h]
    · simp [g, Omega.ConeCap.halfCapIntegrand, Omega.ConeCap.second, hzero _ hz.2.1 h]
  rw [← hcut]
  have hp : (∫ z, g (Omega.pairInterleave z) ∂coneMeasure.prod coneMeasure) =
      ∫ z, g z ∂Omega.ConeCap.pairMeasure sphere5DMeasure 0 :=
    rearrangeCone.integral_comp Omega.pairInterleave.measurableEmbedding g
  rw [← hp]
  apply congrArg Complex.re
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  obtain ⟨B, -, hpair⟩ := cone_pair_ae F
  filter_upwards [hpair] with z hz
  have hb := Omega.FourSpatialConeShell.bulkU5D_zero_cap hε hz.1.1 hz.2.1.1
    (sphere5D_dot_bounds _ _).2 (coneDisplacement z) (separation_eq ε z.1 z.2)
  unfold bulkIntegrand Omega.FourSpatialConeShell.bulkIntegrand
  simp only [derivativeWeight, star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = (star (Omega.ConeProfiles.profileDeriv F z.1.1 z.1.2) * Omega.ConeProfiles.profileDeriv F z.2.1 z.2.2) *
          ((4 * (fluxWeight z.1.1 : ℂ) * (fluxWeight z.2.1 : ℂ)) * bulkU5D 0 (coneTime ε z) (coneDisplacement z)) := by
      rw [Complex.star_def]
      ring
    _ = _ := by
      rw [coneTime, hb]
      simp only [g, Omega.ConeCap.halfCapIntegrand, Omega.ConeCap.first, Omega.ConeCap.second,
        Omega.pairInterleave_apply, Complex.ofReal_sub, Complex.ofReal_one, div_eq_mul_inv]
      ring

/-- The positive-regulator massless shell square tends to the modular covariance form. -/
theorem massless_boundary_limit_5D (F : ConeProfile5D) :
    Tendsto (fun ε : ℝ => regulatedShellQuad5D 0 ε F) (𝓝[>] (0 : ℝ))
      (𝓝 (⟪profileEmbed5D F, nullA5D (profileEmbed5D F)⟫_ℂ).re) := by
  obtain ⟨δ, hδ, hzero⟩ := profileDeriv_zero_near_origin F
  obtain ⟨B, C, hB, hC, hb, hc⟩ := profileDeriv_cap_bounds F
  let f : Phase5D → ℂ := fun p => Omega.ConeProfiles.profileDeriv F p.1 p.2
  have ha : ∀ n, (∫ r, f (r,n) ∂Omega.ConeCap.radialMeasure δ) = 0 := by
    intro n
    rw [← Omega.ConeCap.integral_radial_cut hδ.le _ (fun r hr le => hzero r hr.1 le n)]
    exact Omega.integral_affine_derivative_eq_zero _ (Omega.ConeProfiles.modularProfile_compact F n)
      (modularProfile_deriv_chain F n)
  have hσ : 0 < sphere5DMeasure.real univ := by
    rw [Measure.real, sphere5D_measure_univ, ENNReal.toReal_ofReal (by positivity)]
    positivity
  have hdot : Measurable (Function.uncurry sphere5DDot) := by unfold sphere5DDot; fun_prop
  have hl := Omega.ConeCap.halfCap_boundary hdot (by positivity : 0 < 4 * Real.pi)
    sphere5D_dot_pushforward (fun n m => (abs_le.mp (abs_sphereDot_le_one n m)).2)
    hσ sphereDot_lt_one_ae sphere5D_inv_sqrt_sq_integrable
    (profileDeriv_continuous F).measurable hδ hB
    (fun r hr => hb r ⟨(hδ.trans hr.1).le, hr.2.le⟩)
    (fun r hr => hc r ⟨(hδ.trans hr.1).le, hr.2.le⟩) ha
  have he (n : Sphere5D) : -(Real.pi : ℂ)⁻¹ * Omega.ConeCap.affineLogIntegral δ f n =
      Omega.modularLogPairing (Omega.ConeProfiles.modularProfile F n) (Omega.ConeProfiles.modularProfile F n) := by
    have hcut : Omega.ConeCap.affineLogIntegral 0 f n = Omega.ConeCap.affineLogIntegral δ f n := by
      apply Omega.ConeCap.integral_radial_pair_cut hδ.le
      intro p hp h
      rcases h with h | h
      · simp [f, hzero _ hp.1.1 h]
      · simp [f, hzero _ hp.2.1 h]
    rw [← hcut]
    have hh := (profileDeriv_continuous F).comp (continuous_id.prodMk (continuous_const (y := n)))
    exact Omega.affine_log_pairing_eq_modular _ _
      (F' := fun u => Omega.ConeProfiles.profileDeriv F u n) (G' := fun u => Omega.ConeProfiles.profileDeriv F u n)
      (Omega.ConeProfiles.modularProfile_compact F n)
      (Omega.ConeProfiles.modularProfile_compact F n) hh hh (modularProfile_deriv_chain F n) (modularProfile_deriv_chain F n)
  have hk : capPrefactor *
      (-((4 * Real.pi * Real.sqrt 2 : ℝ) : ℂ) * ∫ n, Omega.ConeCap.affineLogIntegral δ f n ∂sphere5DMeasure) =
      ⟪profileEmbed5D F, nullA5D (profileEmbed5D F)⟫_ℂ := by
    rw [← profile_modular_log_pairing_5D, ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with n
    rw [← he n]
    unfold capPrefactor
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne']
    <;> ring
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (hl.const_mul capPrefactor)
  rw [hk] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (massless_shell_eq_cap hε hδ.le F hzero).symm

set_option maxHeartbeats 1200000 in
-- The product measures and dominated convergence require additional elaboration time.
private theorem differenceIntegrand_boundary (M : ℝ) (F : ConeProfile5D) :
    Tendsto (fun ε : ℝ => ∫ z, differenceIntegrand M ε F z ∂(coneMeasure.prod coneMeasure))
      (𝓝[>] 0) (𝓝 (∫ z, differenceIntegrand M 0 F z ∂(coneMeasure.prod coneMeasure))) ∧
      Integrable (differenceIntegrand M 0 F) (coneMeasure.prod coneMeasure) := by
  obtain ⟨δ, hδ, hzero⟩ := profileDeriv_zero_near_origin F
  obtain ⟨B, hB, hb⟩ := cone_pair_ae F
  let a : Phase5D × Phase5D → ℂ := fun z => star (derivativeWeight F z.1) * derivativeWeight F z.2
  have ha : Measurable a := (((derivativeWeight_continuous F).comp continuous_fst).star.mul
    ((derivativeWeight_continuous F).comp continuous_snd)).measurable
  have hx : Measurable (fun z : Phase5D × Phase5D => sphere5DDot z.1.2 z.2.2) :=
    continuous_sphere5DDot_prod.measurable.comp (measurable_fst.snd.prodMk measurable_snd.snd)
  have hi : Integrable (fun p : Sphere5D × Sphere5D => (Real.sqrt (1 - sphere5DDot p.1 p.2))⁻¹)
      (sphere5DMeasure.prod sphere5DMeasure) := by
    have h := (memLp_one_iff_integrable.mp (sphere5D_inv_sqrt_memLp.mono_exponent (by norm_num))).norm
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_div] using h
  have hi' := rearrangeCone.integrable_comp_of_integrable
    (hi.comp_snd ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))
  have hc := Omega.tendsto_integral_regulated_halfPowerDifference (a := a)
    (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd) hx ha M hδ
    (sq_nonneg B) ?_ ?_ hi'
  swap
  · filter_upwards [hb] with z ⟨hu, hv, hx, huB, hvB⟩
    refine ⟨hu, hv, abs_sphereDot_le_one _ _, hx, ?_⟩
    dsimp only [a]
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul huB hvB (norm_nonneg _) hB
  swap
  · filter_upwards [hb] with z hz h
    rcases h with h | h
    · simp [a, derivativeWeight, hzero _ hz.1.1 h.le]
    · simp [a, derivativeWeight, hzero _ hz.2.1.1 h.le]
  refine ⟨?_, ?_⟩
  · simpa only [differenceIntegrand, bulkDiff_eq, a, Function.comp_apply] using hc.1
  · refine hc.2.congr (.of_forall fun z => ?_)
    simp only [differenceIntegrand, bulkDiff_eq, a, Function.comp_apply]

/-- The difference of regulated shell forms converges to the smeared position-space
boundary correction. -/
private theorem regulatedShellQuad_difference_limit_5D {M : ℝ} (hM : 0 < M) (F : ConeProfile5D) :
    Tendsto (fun ε : ℝ => regulatedShellQuad5D M ε F - regulatedShellQuad5D 0 ε F)
      (𝓝[>] (0 : ℝ))
      (𝓝 (4 * ∫ z, differenceIntegrand M 0 F z ∂(coneMeasure.prod coneMeasure)).re) := by
  have hlim := (Complex.continuous_re.continuousAt.tendsto.comp
    ((differenceIntegrand_boundary M F).1.const_mul (4 : ℂ)))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hi (m : ℝ) : Integrable (bulkIntegrand m ε F) (coneMeasure.prod coneMeasure) := by
    have h := (conePair_integrable m hε F).integral_prod_right
    exact h.congr (Eventually.of_forall (bulkIntegrand_eq_inner m ε F))
  have he (z : Phase5D × Phase5D) :
      differenceIntegrand M ε F z = bulkIntegrand M ε F z - bulkIntegrand 0 ε F z := by
    unfold differenceIntegrand bulkIntegrand Omega.FourSpatialConeShell.bulkIntegrand
    rw [← mul_sub, bulkU5D_difference hM.le (by simpa [coneTime, Complex.mul_re] using hε)]
    exact congrArg (fun q => star (derivativeWeight F z.1) * derivativeWeight F z.2 *
      bulkDiff5D M q) (separation_eq ε z.1 z.2).symm
  change (4 * ∫ z, differenceIntegrand M ε F z ∂(coneMeasure.prod coneMeasure)).re = _
  simp_rw [he]
  rw [integral_sub (hi M) (hi 0), mul_sub, Complex.sub_re,
    regulatedShellQuad5D_eq_bulk M hε F, regulatedShellQuad5D_eq_bulk 0 hε F]

open private strip_cos_pos modularDenom_bound radialDecay_integrable from
  D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondKernel5D
open private kernelG5D_norm_le fourierIntegrand fourierIntegrand_line_integrable contourLine from OmegaMath.Analysis.HalfIntegerBesselFourier

private abbrev realKernel5D (M r s x : ℝ) : ℂ := kernelG5D M (r : ℂ) (s : ℂ) x

private def scaledDifference (M x : ℝ) (p : ℝ × ℝ) : ℂ :=
  (((p.1 * p.2) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
    bulkDiff5D M ((2 * p.1 * p.2 * (1 - x) : ℝ) : ℂ)

private theorem scaledDifference_smooth (M : ℝ) {x : ℝ} (hx : x < 1) :
    ContDiffOn ℝ 2 (scaledDifference M x) (Ioi 0 ×ˢ Ioi 0) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hp₁ : 0 < p.1 := hp.1
  have hp₂ : 0 < p.2 := hp.2
  have hp₃ : 0 < 2 * p.1 * p.2 * (1 - x) := by positivity
  have h₁ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (p.1 * p.2) ^ (3 / 2 : ℝ)) p := by
    exact (contDiffAt_fst.mul contDiffAt_snd).rpow_const_of_ne (mul_pos hp₁ hp₂).ne'
  have h₂ : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((2 * p.1 * p.2 * (1 - x) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (((contDiff_const.mul contDiff_fst).mul contDiff_snd).mul contDiff_const)
  have hA : AnalyticAt ℂ (bulkDiff5D M) ((2 * p.1 * p.2 * (1 - x) : ℝ) : ℂ) :=
    bulkDiff_eq M ▸ Omega.halfPowerDifference_analyticAt M (q := (↑(2 * p.1 * p.2 * (1 - x)) : ℂ))
      (by rwa [Complex.ofReal_re])
  have h₃ : ContDiffAt ℝ 2 (bulkDiff5D M) _ := (hA.restrictScalars (𝕜 := ℝ)).contDiffAt
  have h₄ := h₃.comp p h₂.contDiffAt
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p h₁).mul h₄

set_option maxHeartbeats 1600000 in
-- The iterated radial integrals require additional elaboration time.
private theorem affineBulkKernel_eq_realKernel {M x : ℝ} (hx : x < 1)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hf₀ : tsupport f ⊆ Ioo 0 1) (hg₀ : tsupport g ⊆ Ioo 0 1) :
    4 * (∫ p : ℝ × ℝ, star (deriv f p.1) * scaledDifference M x p * deriv g p.2
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) =
      ∫ s : ℝ, ∫ t : ℝ, star (f (Omega.logistic (2 * Real.pi) s)) *
        realKernel5D M s t x * g (Omega.logistic (2 * Real.pi) t) := by
  have hb : 0 < 2 * Real.pi := by positivity
  have hp (s : ℝ) : 0 < Omega.logistic (2 * Real.pi) s := Real.sigmoid_pos _
  rw [Omega.integral_compact_pairing_eq_logistic hb hf hg hf₀ hg₀ (scaledDifference_smooth M hx),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [realKernel5D, kernelG5D_ofReal M s t x hx]
  have he (v : ℝ) : (fun u => scaledDifference M x (u, v)) =
      fun u => scaledDifference M x (v, u) := by
    funext u
    simp only [scaledDifference, mul_comm u v, show 2 * u * v = 2 * v * u by ring]
  simp_rw [he]
  unfold scaledDifference
  rw [correction5D_mixed_deriv M (hp t) (hp s) hx,
    (Omega.hasDerivAt_logistic _ s).deriv, (Omega.hasDerivAt_logistic _ t).deriv]
  have hsym (u v : ℝ) : correction5D M u v x = correction5D M v u x := by
    simp only [correction5D, mul_comm u v]
  rw [hsym (Omega.logistic (2 * Real.pi) t)]
  push_cast
  ring
private theorem realKernel_slice_integrable (M : ℝ) {x : ℝ} (hx : -1 ≤ x) :
    Integrable (fun p : ℝ × ℝ => realKernel5D M p.1 p.2 x) (volume.prod volume) := by
  by_cases hx' : x < 1
  · obtain ⟨C, hC, h⟩ := kernelG5D_norm_le strip_cos_pos modularDenom_bound M
    simpa [fourierIntegrand, realKernel5D, contourLine] using
      fourierIntegrand_line_integrable radialDecay_integrable (M := M) (ν := 0) (lam := 0)
        (C := C * (1 / Real.sqrt (1 - x))) (x := x)
        (fun z w hz hw => h z w hz hw x hx hx') (y := 0) (t := 0) (by norm_num) (by norm_num)
  · simp [realKernel5D, kernelG5D, hx']

private abbrev scale := 2 * Real.pi

private theorem fourierG_eq_mixed (M x ξ η : ℝ)
    (hi : Integrable (fun p : ℝ × ℝ => realKernel5D M p.1 p.2 x) (volume.prod volume)) :
    fourierG5D M (scale * ξ) (scale * η) x = (scale : ℂ)⁻¹ *
      Omega.mixedFourier (fun p : ℝ × ℝ => realKernel5D M p.1 p.2 x) (ξ, η) := by
  rw [Omega.mixedFourier_eq_iterated_exp _ hi]
  simp only [fourierG5D, fourierIntegrand, realKernel5D, one_div, show (scale : ℂ) = 2 * (Real.pi : ℂ) by simp [scale]]

private theorem massive_frequency_integrable {M : ℝ} (hM : 0 < M) (F : ConeProfile5D) :
    Integrable (fun p : Phase5D × Phase5D => star (Omega.ConeProfiles.profileFourier F p.1) *
      fourierG5D M p.1.1 p.2.1 (sphere5DDot p.1.2 p.2.2) * Omega.ConeProfiles.profileFourier F p.2)
      (phase5DMeasure.prod phase5DMeasure) := by
  obtain ⟨C, hC, hc⟩ := fourierG5D_bound M hM
  obtain ⟨hm, B, hB, hb⟩ := profileFourier_bounded_continuous F
  let e (s : ℝ) := Real.exp (-((3/8) * |s|))
  let l (n : Sphere5D × Sphere5D) := 1 / Real.sqrt (1 - sphere5DDot n.1 n.2)
  let coords : Phase5D × Phase5D → ℝ × ℝ × ℝ := fun p =>
    (p.1.1, p.2.1, sphere5DDot p.1.2 p.2.2)
  have hcoords : Measurable coords := by dsimp [coords, sphere5DDot]; fun_prop
  let L := (fun x : ℝ × ℝ × ℝ => fourierG5D M x.1 x.2.1 x.2.2) ∘ coords
  have hLm : Measurable L := (fourierG5D_measurable M).comp hcoords
  have hl : Integrable l (sphere5DMeasure.prod sphere5DMeasure) := by
    have h := (memLp_one_iff_integrable.mp (sphere5D_inv_sqrt_memLp.mono_exponent (by norm_num))).norm
    simpa [l, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using h
  refine Omega.integrable_pairing_of_product_bound sphere5DMeasure (Omega.ConeProfiles.profileFourier F)
    hm.measurable hB hb L hLm e (integrable_exp_neg_mul_abs (by norm_num))
    (fun _ => (Real.exp_pos _).le) l hl (fun _ => by dsimp [l]; positivity) hC.le ?_
  filter_upwards [(Omega.measurePreserving_pairInterleave volume sphere5DMeasure).quasiMeasurePreserving.ae
    (((sphere5DMeasure.prod sphere5DMeasure).quasiMeasurePreserving_snd (μ := volume.prod volume)).ae
      sphereDot_lt_one_ae)] with p hx
  have hk := hc p.1.1 p.2.1 (sphere5DDot p.1.2 p.2.2) (abs_le.mp (abs_sphereDot_le_one _ _)).1 hx
  rw [show -(3/8) * (|p.1.1| + |p.2.1|) =
    -((3/8) * |p.1.1|) + -((3/8) * |p.2.1|) by ring, Real.exp_add] at hk
  exact hk

private theorem massive_modular_pairing {M : ℝ} (hM : 0 < M) (F : ConeProfile5D) :
    (∫ n : Sphere5D × Sphere5D, ∫ p : ℝ × ℝ,
      star (Omega.ConeProfiles.modularProfile F n.1 p.1) * realKernel5D M p.1 p.2 (sphere5DDot n.1 n.2) *
        Omega.ConeProfiles.modularProfile F n.2 p.2 ∂((volume : Measure ℝ).prod volume)
        ∂(sphere5DMeasure.prod sphere5DMeasure)) =
      ⟪profileEmbed5D F, nullT5D M hM (profileEmbed5D F)⟫_ℂ := by
  rw [profile_nullT5D_pairing hM F]
  refine (Omega.angular_mixedFourier_pairing sphere5DMeasure (Omega.ConeProfiles.modularProfile F)
    (fun n p => realKernel5D M p.1 p.2 (sphere5DDot n.1 n.2))
    (fun n p => fourierG5D M p.1 p.2 (sphere5DDot n.1 n.2)) (Omega.ConeProfiles.profileFourier F)
    (b := scale) (by positivity [Real.pi_pos]) (.of_forall fun n =>
      realKernel_slice_integrable M (abs_le.mp (abs_sphereDot_le_one n.1 n.2)).1)
    (fun n ξ η => fourierG_eq_mixed M (sphere5DDot n.1 n.2) ξ η
      (realKernel_slice_integrable M (abs_le.mp (abs_sphereDot_le_one n.1 n.2)).1))
    (fun n ξ => ?_) (massive_frequency_integrable hM F)).symm
  have h := Omega.ConeProfiles.profileFourier_modular F (scale * ξ) n
  change Omega.ConeProfiles.profileFourier F (scale * ξ, n) = (Real.sqrt scale : ℂ)⁻¹ *
    𝓕 (Omega.ConeProfiles.modularProfile F n) (scale⁻¹ * (scale * ξ)) at h
  simpa only [inv_mul_cancel_left₀ (by positivity [Real.pi_pos] : scale ≠ 0)] using h
private theorem differenceIntegrand_eq_nullT {M : ℝ} (hM : 0 < M) (F : ConeProfile5D) :
    (4 * ∫ z, differenceIntegrand M 0 F z ∂(coneMeasure.prod coneMeasure)) =
      ⟪profileEmbed5D F, nullT5D M hM (profileEmbed5D F)⟫_ℂ := by
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  change (4 * ∫ z, differenceIntegrand M 0 F z ∂((μ.prod sphere5DMeasure).prod
    (μ.prod sphere5DMeasure))) = _
  rw [Omega.integral_pairInterleave μ sphere5DMeasure _ (differenceIntegrand_boundary M F).2,
    ← integral_const_mul, ← massive_modular_pairing hM F]
  apply integral_congr_ae
  filter_upwards [sphereDot_lt_one_ae] with n hn
  have h₁ := profileValue_smooth_support F n.1
  have h₂ := profileValue_smooth_support F n.2
  have he : (fun p : ℝ × ℝ => differenceIntegrand M 0 F ((p.1,n.1), (p.2,n.2))) =ᵐ[μ.prod μ]
      fun p => star (deriv (fun u => Omega.ConeProfiles.profileValue F u n.1) p.1) *
        scaledDifference M (sphere5DDot n.1 n.2) p *
        deriv (fun u => Omega.ConeProfiles.profileValue F u n.2) p.2 := by
    have hr : ∀ᵐ u ∂μ, u ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
    filter_upwards [(μ.quasiMeasurePreserving_fst (ν := μ)).ae hr,
      (μ.quasiMeasurePreserving_snd (μ := μ)).ae hr] with p hu hv
    have hw : fluxWeight p.1 * fluxWeight p.2 = (p.1 * p.2) ^ (3 / 2 : ℝ) := by
      rw [fluxWeight_rpow hu.1, fluxWeight_rpow hv.1, Real.mul_rpow hu.1.le hv.1.le]
    simp only [differenceIntegrand, scaledDifference, derivativeWeight, regulatedSeparation,
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, add_zero, Complex.ofReal_zero,
      star_mul, Complex.star_def, Complex.conj_ofReal, (Omega.ConeProfiles.profileValue_hasDerivAt F _ _).deriv]
    rw [← hw]
    push_cast
    ring
  rw [integral_congr_ae he, affineBulkKernel_eq_realKernel hn h₁.1 h₂.1 h₁.2 h₂.2]
  symm
  have hk := realKernel_slice_integrable M (x := sphere5DDot n.1 n.2)
    (abs_le.mp (abs_sphereDot_le_one n.1 n.2)).1
  rw [integral_prod _ (Omega.integrable_schwartz_kernel_pairing _ hk
    (Omega.ConeProfiles.modularProfile F n.1) (Omega.ConeProfiles.modularProfile F n.2))]
  simp_rw [Omega.ConeProfiles.modularProfile_apply]
  rfl

/-- At positive mass the right boundary includes the same correction as the Fourier kernel. -/
theorem massive_boundary_limit_5D {M : ℝ} (hM : 0 < M) (F : ConeProfile5D) :
    Tendsto (fun ε : ℝ => regulatedShellQuad5D M ε F) (𝓝[>] (0 : ℝ))
      (𝓝 (⟪profileEmbed5D F, (nullA5D + nullT5D M hM) (profileEmbed5D F)⟫_ℂ).re) := by
  have h := regulatedShellQuad_difference_limit_5D hM F
  rw [differenceIntegrand_eq_nullT hM F] at h
  simpa only [sub_add_cancel, _root_.add_apply, inner_add_right, Complex.add_re,
    add_comm _ (⟪profileEmbed5D F, nullA5D (profileEmbed5D F)⟫_ℂ).re] using
    h.add (massless_boundary_limit_5D F)

/-- The weak limit of nonnegative shell squares gives positivity on the ambient space. -/
theorem nullB5D_nonneg {M : ℝ} (hM : 0 < M) : 0 ≤ nullA5D + nullT5D M hM := by
  apply nonneg_iff_isPositive.mpr
  refine isPositive_def'.mpr ⟨(nonneg_iff_isPositive.mp nullA5D_nonneg).isSelfAdjoint.add
    (nullT5D_selfAdjoint M hM), ?_⟩
  intro f
  change 0 ≤ RCLike.re ⟪(nullA5D + nullT5D M hM) f, f⟫_ℂ
  rw [inner_re_symm (𝕜 := ℂ)]
  change 0 ≤ (⟪f, (nullA5D + nullT5D M hM) f⟫_ℂ).re
  refine profileEmbed5D_dense.induction_on f (isClosed_le continuous_const (by fun_prop)) ?_
  intro F
  exact ge_of_tendsto' (massive_boundary_limit_5D hM F) (fun ε => regulatedShellQuad5D_nonneg M ε F)

private theorem conjugate_re_inner (f g : H5D) :
    (⟪nullConj5D.toLinearIsometryEquiv f, nullConj5D.toLinearIsometryEquiv g⟫_ℂ).re = (⟪f, g⟫_ℂ).re := by
  change RCLike.re ⟪nullConj5D.toLinearIsometryEquiv f, nullConj5D.toLinearIsometryEquiv g⟫_ℂ = RCLike.re ⟪f, g⟫_ℂ
  simp only [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
    ← map_add, ← map_sub, LinearIsometryEquiv.norm_map]

/-- Conjugating the ambient covariance reverses the sign of the skew multiplier. -/
theorem nullN5D_sub_J_nonneg {M : ℝ} (hM : 0 < M) :
    0 ≤ (1 : H5D →L[ℂ] H5D) + nullT5D M hM - nullJ5D := by
  have hJ := (nonneg_iff_isPositive.mp nullA5D_nonneg).isSelfAdjoint.sub (IsSelfAdjoint.one _)
  apply nonneg_iff_isPositive.mpr
  refine isPositive_def'.mpr ⟨((IsSelfAdjoint.one _).add (nullT5D_selfAdjoint M hM)).sub hJ, ?_⟩
  intro f
  have h := (nonneg_iff_isPositive.mp (nullB5D_nonneg hM)).re_inner_nonneg_left (nullConj5D.toLinearIsometryEquiv f)
  have he : nullA5D + nullT5D M hM = 1 + nullT5D M hM + nullJ5D := by
    unfold nullJ5D
    abel
  rw [he] at h
  have hconj : nullConj5D.toLinearIsometryEquiv ((1 + nullT5D M hM - nullJ5D) f) =
      (1 + nullT5D M hM + nullJ5D) (nullConj5D.toLinearIsometryEquiv f) := by
    simp only [_root_.sub_apply, _root_.add_apply, one_apply_eq_self, map_sub, map_add, nullConj5D_comm_T, nullConj5D_anti_J,
      sub_neg_eq_add]
  change 0 ≤ (⟪(1 + nullT5D M hM - nullJ5D) f, f⟫_ℂ).re
  rw [← conjugate_re_inner, hconj]
  exact h

end NullConeGravity
