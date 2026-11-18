/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Density
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Density
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mellin integrals and normalized prime-selection densities. -/

import D5.S3.Arith.Robin.Analytic.OmegaTailUpper
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Integrable selection profiles for the distinct-prime tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.Density

open D5.S3.Arith.Robin.Analytic.OmegaTailUpper

/-- The prime-selection profile associated with a positive scale parameter. -/
private def profile (s A u : ℝ) : ℝ := A ^ s / (A ^ s + u ^ s)

/-- The Mellin integral of the prime-selection profile. -/
private theorem mellin_integral {s A r : ℝ} (hs : 0 < s) (hA : 0 < A)
    (hr : r ∈ Ioo 0 s) :
    IntegrableOn (fun u : ℝ => u ^ (r - 1) * profile s A u) (Ioi 0) ∧
      (∫ u in Ioi (0 : ℝ), u ^ (r - 1) * profile s A u) =
        π * A ^ r / (s * sin (π * r / s)) := by
  have hsne := hs.ne'
  have hp : r / s ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hr.1 hs, (div_lt_one hs).mpr hr.2⟩
  let phi : ℝ → ℝ := fun t => A * t ^ (1 / s)
  let phi' : ℝ → ℝ := fun t => A * ((1 / s) * t ^ (1 / s - 1))
  let g : ℝ → ℝ := fun u => u ^ (r - 1) * profile s A u
  have hphi : phi '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact mul_pos hA (Real.rpow_pos_of_pos ht _)
    · intro hu
      refine ⟨(u / A) ^ s, Real.rpow_pos_of_pos (div_pos hu hA) _, ?_⟩
      dsimp only [phi]
      rw [one_div, Real.rpow_rpow_inv (div_pos hu hA).le hsne]
      field_simp [hA.ne']
  have hinj : InjOn phi (Ioi (0 : ℝ)) := by
    intro t ht u hu he
    have he' : t ^ (1 / s) = u ^ (1 / s) := mul_left_cancel₀ hA.ne' he
    exact (Real.rpow_left_inj ht.le hu.le (one_div_ne_zero hsne)).mp he'
  have hder (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt phi (phi' t) (Ioi 0) t := by
    exact ((Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).const_mul A).hasDerivWithinAt
  have hpoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      |phi' t| • g (phi t) = (A ^ r / s) * Real.rpowIntegrand₀₁ (r / s) t 1 := by
    have hphis : (phi t) ^ s = A ^ s * t := by
      dsimp only [phi]
      rw [Real.mul_rpow hA.le (Real.rpow_nonneg ht.le _), one_div,
        Real.rpow_inv_rpow ht.le hsne]
    have hdpos : 0 < phi' t :=
      mul_pos hA (mul_pos (one_div_pos.mpr hs) (Real.rpow_pos_of_pos ht _))
    have htprod : t ^ (1 / s - 1) * t ^ ((1 / s) * (r - 1)) =
        t ^ (r / s - 1) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    have hAprod : A * A ^ (r - 1) = A ^ r := by
      nth_rw 1 [← Real.rpow_one A]
      rw [← Real.rpow_add hA]
      congr 1
      ring
    rw [abs_of_pos hdpos, smul_eq_mul,
      Real.rpowIntegrand₀₁_eq_pow_div hp ht.le zero_le_one]
    dsimp only [g, profile]
    rw [hphis]
    dsimp only [phi', phi]
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
    have hden : A ^ s + A ^ s * t = A ^ s * (t + 1) := by ring
    rw [hden]
    have hAs : A ^ s ≠ 0 := (Real.rpow_pos_of_pos hA s).ne'
    calc
      _ = (A * A ^ (r - 1)) *
          (t ^ (1 / s - 1) * t ^ ((1 / s) * (r - 1))) / (s * (t + 1)) := by
        field_simp [hAs, hsne, ne_of_gt (add_pos (show 0 < t from ht) zero_lt_one)]
        <;> ring
      _ = _ := by
        rw [htprod, hAprod]
        field_simp [hsne, ne_of_gt (add_pos (show 0 < t from ht) zero_lt_one)]
        <;> ring
  have hi : IntegrableOn
      (fun t => (A ^ r / s) * Real.rpowIntegrand₀₁ (r / s) t 1) (Ioi 0) :=
    (Real.integrableOn_rpowIntegrand₀₁_Ioi hp zero_le_one).const_mul _
  have hsubst := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hder hinj g
  have hsubstI := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hder hinj g
  rw [hphi] at hsubst hsubstI
  have hi' : IntegrableOn (fun t => |phi' t| • g (phi t)) (Ioi (0 : ℝ)) :=
    IntegrableOn.congr_fun hi (fun t ht => (hpoint t ht).symm) measurableSet_Ioi
  refine ⟨hsubstI.mpr hi', ?_⟩
  change (∫ u in Ioi (0 : ℝ), g u) = _
  rw [hsubst, setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul,
    D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.power_normalizer _ hp]
  rw [show π * (r / s) = π * r / s by ring]
  ring

/-- The normalized profile used for choosing distinct primes. -/
def q (s u : ℝ) : ℝ := profile s (a s) u

private lemma profile_pos {s A u : ℝ} (hA : 0 < A) (hu : 0 < u) :
    0 < profile s A u := by
  unfold profile
  exact div_pos (rpow_pos_of_pos hA _) (add_pos (rpow_pos_of_pos hA _) (rpow_pos_of_pos hu _))

private lemma profile_lt_one {s A u : ℝ} (hA : 0 < A) (hu : 0 < u) :
    profile s A u < 1 := by
  unfold profile
  exact (div_lt_one (add_pos (rpow_pos_of_pos hA _) (rpow_pos_of_pos hu _))).mpr
    (lt_add_of_pos_right _ (rpow_pos_of_pos hu _))

/-- The profile takes strictly interior Bernoulli probabilities on the positive half-line. -/
theorem q_range {s u : ℝ} (hs : 1 < s) (hu : 0 < u) : q s u ∈ Ioo 0 1 :=
  ⟨profile_pos (a_pos hs) hu, profile_lt_one (a_pos hs) hu⟩

/-- Continuity of the selection density on positive real numbers. -/
theorem q_continuous {s : ℝ} (hs : 1 < s) : ContinuousOn (q s) (Ioi 0) := by
  intro u hu
  have hp : 0 < a s ^ s + u ^ s :=
    add_pos (rpow_pos_of_pos (a_pos hs) _) (rpow_pos_of_pos hu _)
  change ContinuousWithinAt (fun u : ℝ => a s ^ s / (a s ^ s + u ^ s)) (Ioi 0) u
  exact continuousWithinAt_const.div
    (continuousWithinAt_const.add ((continuousAt_id.rpow_const (Or.inl (ne_of_gt hu))).continuousWithinAt))
    hp.ne'

/-- The selection density has unit total mass. -/
theorem q_mass {s : ℝ} (hs : 1 < s) :
    IntegrableOn (q s) (Ioi 0) ∧ (∫ u in Ioi (0 : ℝ), q s u) = 1 := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have ha := a_pos hs
  have h := power_kernel_integral hs (rpow_pos_of_pos ha s)
  have hk : (fun u : ℝ => s * a s ^ s / (u ^ s + a s ^ s)) =
      fun u => s * q s u := by
    funext u
    simp only [q, profile]
    ring
  rw [hk] at h
  have hi : IntegrableOn (q s) (Ioi 0) := by
    change Integrable (q s) (volume.restrict (Ioi 0))
    have hi := h.1.const_mul s⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hs0.ne', one_mul] using hi
  refine ⟨hi, ?_⟩
  rw [integral_const_mul] at h
  have hsin : 0 < sin (π / s) :=
    sin_pos_of_pos_of_lt_pi (div_pos pi_pos hs0) (div_lt_self pi_pos hs)
  rw [← rpow_mul ha.le, mul_one_div_cancel hs0.ne', rpow_one] at h
  have he : π * a s / sin (π / s) = s := by
    dsimp [a]
    field_simp
  rw [he] at h
  exact (mul_left_cancel₀ hs0.ne' (h.2.trans (mul_one s).symm))

/-- The entropy identity behind the prime-selection variational argument. -/
private theorem profile_entropy {s A u : ℝ} (hA : 0 < A) (hu : 0 < u) :
    binEntropy (profile s A u) = log (1 + A ^ s / u ^ s) -
      s * profile s A u * log A + s * profile s A u * log u := by
  have hAs := rpow_pos_of_pos hA s
  have hus := rpow_pos_of_pos hu s
  have hden : 0 < A ^ s + u ^ s := add_pos hAs hus
  have hsub : 1 - profile s A u = u ^ s / (A ^ s + u ^ s) := by
    dsimp [profile]
    field_simp
    <;> ring
  have hlog : log (1 + A ^ s / u ^ s) = log (A ^ s + u ^ s) - s * log u := by
    rw [show 1 + A ^ s / u ^ s = (A ^ s + u ^ s) / u ^ s by field_simp; ring,
      log_div hden.ne' hus.ne', log_rpow hu]
  rw [binEntropy, log_inv, log_inv, hsub, hlog]
  dsimp [profile]
  rw [log_div hAs.ne' hden.ne', log_div hus.ne' hden.ne', log_rpow hA, log_rpow hu]
  field_simp
  <;> ring

private lemma log_moment_bound {u r d : ℝ} (hu : 0 < u) (hd : 0 < d)
    (hr : r ∈ Ioo (1 - d) (1 + d)) :
    |u ^ (r - 1) * log u| ≤ (u ^ (-2 * d) + u ^ (2 * d)) / d := by
  rw [abs_mul, abs_of_pos (rpow_pos_of_pos hu _)]
  by_cases hu1 : u ≤ 1
  · rw [abs_of_nonpos (log_nonpos hu.le hu1)]
    have hb : -log u ≤ u ^ (-d) / d := by
      have := neg_rpow_div_le_log hu.le hd
      simpa only [neg_div, neg_neg] using neg_le_neg this
    have hp : u ^ (r - 1) * (u ^ (-d) / d) = u ^ (r - 1 - d) / d := by
      rw [← mul_div_assoc, ← rpow_add hu]
      simp only [sub_eq_add_neg]
    calc
      _ ≤ u ^ (r - 1) * (u ^ (-d) / d) :=
        mul_le_mul_of_nonneg_left hb (rpow_nonneg hu.le _)
      _ = _ := hp
      _ ≤ u ^ (-2 * d) / d := div_le_div_of_nonneg_right
        (rpow_le_rpow_of_exponent_ge hu hu1 (by linarith [hr.1])) hd.le
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (rpow_nonneg hu.le _)
  · have hu1' : 1 ≤ u := le_of_lt (lt_of_not_ge hu1)
    rw [abs_of_nonneg (log_nonneg hu1')]
    have hp : u ^ (r - 1) * (u ^ d / d) = u ^ (r - 1 + d) / d := by
      rw [← mul_div_assoc, ← rpow_add hu]
    calc
      _ ≤ u ^ (r - 1) * (u ^ d / d) :=
        mul_le_mul_of_nonneg_left (log_le_rpow_div hu.le hd) (rpow_nonneg hu.le _)
      _ = _ := hp
      _ ≤ u ^ (2 * d) / d := div_le_div_of_nonneg_right
        (rpow_le_rpow_of_exponent_le hu1' (by linarith [hr.2])) hd.le
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left (rpow_nonneg hu.le _)

private theorem mellin_derivative {s A : ℝ} (hs : 1 < s) (hA : 0 < A) :
    IntegrableOn (fun u : ℝ => profile s A u * log u) (Ioi 0) ∧
      HasDerivAt (fun r : ℝ => ∫ u in Ioi (0 : ℝ), u ^ (r - 1) * profile s A u)
        (∫ u in Ioi (0 : ℝ), profile s A u * log u) 1 := by
  let d : ℝ := min 1 (s - 1) / 4
  have hd : 0 < d := div_pos (lt_min zero_lt_one (sub_pos.mpr hs)) (by norm_num)
  have hd1 : 2 * d < 1 := by
    have : min 1 (s - 1) ≤ (1 : ℝ) := min_le_left _ _
    dsimp [d]
    linarith
  have hds : 1 + 2 * d < s := by
    have : min 1 (s - 1) ≤ s - 1 := min_le_right _ _
    dsimp [d]
    linarith
  have hs0 : 0 < s := zero_lt_one.trans hs
  let F : ℝ → ℝ → ℝ := fun r u => u ^ (r - 1) * profile s A u
  let F' : ℝ → ℝ → ℝ := fun r u => u ^ (r - 1) * log u * profile s A u
  let B : ℝ → ℝ := fun u =>
    (u ^ (-2 * d) * profile s A u + u ^ (2 * d) * profile s A u) / d
  have hB : IntegrableOn B (Ioi 0) := by
    have hl := (mellin_integral hs0 hA
      (r := 1 - 2 * d) ⟨by linarith, by linarith [hs]⟩).1
    have hh := (mellin_integral hs0 hA
      (r := 1 + 2 * d) ⟨by linarith, hds⟩).1
    change Integrable B (volume.restrict (Ioi 0))
    convert (hl.add hh).div_const d using 1
    funext u
    dsimp [B]
    congr 2 <;> congr 1 <;> ring
  have hFmeas : ∀ᶠ r in 𝓝 (1 : ℝ), AEStronglyMeasurable (F r) (volume.restrict (Ioi 0)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : 1 - d < (1 : ℝ))
      (by linarith : (1 : ℝ) < 1 + d)] with r hr
    exact (mellin_integral hs0 hA (r := r) ⟨by linarith [hr.1], by linarith [hr.2]⟩).1.aestronglyMeasurable
  have hFint : Integrable (F 1) (volume.restrict (Ioi 0)) :=
    (mellin_integral hs0 hA (r := 1) ⟨zero_lt_one, hs⟩).1
  have hF'meas : AEStronglyMeasurable (F' 1) (volume.restrict (Ioi 0)) := by
    have hm : Measurable (F' 1) := by
      dsimp [F', profile]
      fun_prop
    exact hm.aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ r ∈ Ioo (1 - d) (1 + d), ‖F' r u‖ ≤ B u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro r hr
    have hp : 0 ≤ profile s A u := (profile_pos hA hu).le
    have hb := mul_le_mul_of_nonneg_right (log_moment_bound hu hd hr) hp
    simpa only [F', B, Real.norm_eq_abs, abs_mul, abs_of_nonneg hp,
      add_mul, div_mul_eq_mul_div] using hb
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ r ∈ Ioo (1 - d) (1 + d), HasDerivAt (F · u) (F' r u) r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro r _
    have h := (((hasDerivAt_id r).sub_const 1).const_rpow hu).mul_const (profile s A u)
    convert h using 1 <;> dsimp [F, F'] <;> ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : 1 - d < (1 : ℝ)) (by linarith : (1 : ℝ) < 1 + d))
    hFmeas hFint hF'meas hbound hB hdiff
  change Integrable (fun u : ℝ => profile s A u * log u) (volume.restrict (Ioi 0)) ∧ _
  simpa only [F', F, sub_self, rpow_zero, one_mul, mul_comm (log _) (profile s A _)] using h

/-- The logarithmic moment of the normalized prime-selection profile. -/
theorem q_log_moment {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun u : ℝ => q s u * log u) (Ioi 0) ∧
      (∫ u in Ioi (0 : ℝ), q s u * log u) =
        log (a s) - (π / s) * cos (π / s) / sin (π / s) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have ha := a_pos hs
  have hsin : 0 < sin (π / s) :=
    sin_pos_of_pos_of_lt_pi (div_pos pi_pos hs0) (div_lt_self pi_pos hs)
  obtain ⟨hi, hd⟩ := mellin_derivative hs ha
  refine ⟨hi, ?_⟩
  let J : ℝ → ℝ := fun r => π * a s ^ r / (s * sin (π * r / s))
  have he : (fun r : ℝ => ∫ u in Ioi (0 : ℝ), u ^ (r - 1) * profile s (a s) u)
      =ᶠ[𝓝 (1 : ℝ)] J := by
    filter_upwards [Ioo_mem_nhds zero_lt_one hs] with r hr
    exact (mellin_integral hs0 ha hr).2
  have hJ : HasDerivAt J
      (log (a s) - (π / s) * cos (π / s) / sin (π / s)) 1 := by
    have hnum := ((hasStrictDerivAt_const_rpow ha (1 : ℝ)).hasDerivAt).const_mul π
    have harg := ((hasDerivAt_id (1 : ℝ)).const_mul π).div_const s
    have hden := harg.sin.const_mul s
    have h := hnum.div hden (by simpa using (mul_pos hs0 hsin).ne')
    convert h using 1
    · funext r
      dsimp [J]
    · simp only [rpow_one, mul_one, id_eq] 
      dsimp [a]
      field_simp
      <;> ring
  exact (hd.congr_of_eventuallyEq he.symm).unique hJ

private lemma log_weight_nonneg {s c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    0 ≤ log (1 + c / u ^ s) :=
  log_nonneg (le_add_of_nonneg_right (div_nonneg hc.le (rpow_nonneg hu.le _)))

private lemma log_weight_bound {s c u : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hu : 0 < u) (hu1 : u ≤ 1) :
    log (1 + c / u ^ s) ≤ log (1 + c) - s * log u := by
  have hup := rpow_pos_of_pos hu s
  calc
    _ = log (u ^ s + c) - s * log u := by
      rw [show 1 + c / u ^ s = (u ^ s + c) / u ^ s by field_simp,
        log_div (add_pos hup hc).ne' hup.ne', log_rpow hu]
    _ ≤ _ := by
      gcongr
      exact rpow_le_one hu.le hu1 hs.le

private lemma log_weight_upper {s c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    log (1 + c / u ^ s) ≤ c / u ^ s := by
  have h := log_le_sub_one_of_pos (show 0 < 1 + c / u ^ s by positivity)
  linarith

private theorem log_weight_integrable {s c : ℝ} (hs : 1 < s) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => log (1 + c / u ^ s)) (Ioi 0) := by
  have hm : Measurable (fun u : ℝ => log (1 + c / u ^ s)) := by fun_prop
  have hlow : IntegrableOn (fun u : ℝ => log (1 + c / u ^ s)) (Ioc 0 1) := by
    have hb : IntegrableOn (fun u : ℝ => log (1 + c) - s * log u) (Ioc 0 1) := by
      exact (integrableOn_const (by simp only [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).sub
        ((intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)).1.const_mul s)
    apply hb.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (log_weight_nonneg hc hu.1)]
    exact log_weight_bound (zero_lt_one.trans hs) hc hu.1 hu.2
  have hhigh : IntegrableOn (fun u : ℝ => log (1 + c / u ^ s)) (Ioi 1) := by
    have hb := (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1)
      (show (0 : ℝ) < 1 by norm_num)).const_mul c
    apply hb.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    rw [Real.norm_eq_abs, abs_of_nonneg (log_weight_nonneg hc hu0), rpow_neg hu0.le,
      ← div_eq_mul_inv]
    exact log_weight_upper hc hu0
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  exact ⟨hlow, hhigh⟩

set_option maxHeartbeats 1000000 in
private theorem q_log_weight_integral {s : ℝ} (hs : 1 < s) :
    (∫ u in Ioi (0 : ℝ), log (1 + a s ^ s / u ^ s)) = s := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have ha := a_pos hs
  let c : ℝ := a s ^ s
  have hc : 0 < c := rpow_pos_of_pos ha s
  let f : ℝ → ℝ := fun u => u * log (1 + c / u ^ s)
  have htopBound : Tendsto (fun u : ℝ => c * u ^ (1 - s)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).const_mul c
  have htop : Tendsto f atTop (𝓝 0) := by
    apply squeeze_zero' _ _ htopBound
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      exact mul_nonneg hu.le (log_weight_nonneg hc hu)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have hb := mul_le_mul_of_nonneg_left (log_weight_upper (s := s) hc hu) hu.le
      have he : u * (c / u ^ s) = c * u ^ (1 - s) := by
        rw [rpow_sub hu, rpow_one]
        ring
      exact hb.trans_eq he
  have hzeroBound : Tendsto
      (fun u : ℝ => u * log (1 + c) - s * (log u * u)) (𝓝[>] 0) (𝓝 0) := by
    have hl := tendsto_log_mul_rpow_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
    simpa only [rpow_one, zero_mul, mul_zero, sub_zero, id_eq] using
      ((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const (log (1 + c))).sub (hl.const_mul s)
  have hzero : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' _ _ hzeroBound
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact mul_nonneg (show 0 < u from hu).le (log_weight_nonneg hc hu)
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with u hu hu1
      have hb := mul_le_mul_of_nonneg_left (log_weight_bound hs0 hc hu hu1.le) hu.le
      dsimp [f]
      nlinarith
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    apply continuousWithinAt_Ioi_iff_Ici.mp
    change Tendsto f (𝓝[>] 0) (𝓝 (f 0))
    simpa only [f, zero_mul] using hzero
  have hder : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivAt f (log (1 + c / u ^ s) - s * q s u) u := by
    intro u hu
    have h := (hasDerivAt_id u).mul (logWeight_deriv (s := s) hc hu)
    convert h using 1
    · rfl
    · dsimp [abelKernel, q, profile, c, logWeight]
      field_simp [(show 0 < u from hu).ne']
      <;> ring
  have hi := log_weight_integrable hs hc
  have hq := q_mass hs
  have hft := integral_Ioi_of_hasDerivAt_of_tendsto hcont hder
    (hi.sub (hq.1.const_mul s)) htop
  rw [integral_sub hi (hq.1.const_mul s), integral_const_mul, hq.2] at hft
  simp only [f, zero_mul, sub_zero, mul_one] at hft
  change (∫ u in Ioi (0 : ℝ), log (1 + a s ^ s / u ^ s)) - s = 0 at hft
  linarith

/-- The total binary entropy of the normalized profile. -/
theorem q_entropy {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun u : ℝ => binEntropy (q s u)) (Ioi 0) ∧
      (∫ u in Ioi (0 : ℝ), binEntropy (q s u)) =
        s - π * cos (π / s) / sin (π / s) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have ha := a_pos hs
  have hsin : 0 < sin (π / s) :=
    sin_pos_of_pos_of_lt_pi (div_pos pi_pos hs0) (div_lt_self pi_pos hs)
  have hi := log_weight_integrable hs (rpow_pos_of_pos ha s)
  have hq := q_mass hs
  have hl := q_log_moment hs
  have he : EqOn (fun u : ℝ => binEntropy (q s u))
      (fun u => log (1 + a s ^ s / u ^ s) - s * log (a s) * q s u +
        s * (q s u * log u)) (Ioi 0) := by
    intro u hu
    simpa only [q, mul_comm (log (a s)) (profile s (a s) u), mul_assoc] using
      profile_entropy ha hu
  have hint := (hi.sub (hq.1.const_mul (s * log (a s)))).add (hl.1.const_mul s)
  refine ⟨hint.congr_fun (fun u hu => (he hu).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => he hu)]
  change (∫ u in Ioi (0 : ℝ),
    ((fun u => log (1 + a s ^ s / u ^ s)) - fun u => s * log (a s) * q s u) u +
      (fun u => s * (q s u * log u)) u) = _
  rw [integral_add (hi.sub (hq.1.const_mul (s * log (a s)))) (hl.1.const_mul s)]
  change (∫ u in Ioi (0 : ℝ), log (1 + a s ^ s / u ^ s) - s * log (a s) * q s u) +
    (∫ u in Ioi (0 : ℝ), s * (q s u * log u)) = _
  rw [integral_sub hi (hq.1.const_mul (s * log (a s))), integral_const_mul, integral_const_mul,
    q_log_weight_integral hs, hq.2, hl.2]
  field_simp [hs0.ne', hsin.ne']
  <;> ring

end D5.S3.Arith.Robin.Analytic.OmegaTail.Density
