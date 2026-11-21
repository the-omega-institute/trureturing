/- GID: D5/S3/Observer/Linear/ReflectingHeatPhysicalGramian
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatPhysicalGramian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Observer.Linear.ReflectingHeatInverseSupport]
   utility: none
   digest: A centered Fourier density bounds the physical reflecting heat Gramian. -/

import D5.S3.Observer.Linear.ReflectingHeatInverseSupport
import Batteries.Tactic.OpenPrivate

/-! # The reflecting heat Gramian upper bound in physical time -/

namespace D5.S3.Observer.Linear.ReflectingHeatInterpolation

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open D5.S3.Analytic.Hardy.FiniteStripMomentBound (windowNorm)
open D5.S3.Fourier.InverseFourierSupport (frequencyRestriction)
open D5.S3.Observer.Linear.ReflectingHeatStripBound

noncomputable section

private theorem integral_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {d : ℝ} (hd : 0 < d) (a : ℝ) :
    (∫ s : ℝ, f (d * s - a)) = d⁻¹ • ∫ t : ℝ, f t := by
  calc
    _ = |d⁻¹| • ∫ t : ℝ, f (t - a) :=
      Measure.integral_comp_mul_left (fun t => f (t - a)) d
    _ = _ := by
      simp_rw [abs_of_pos (inv_pos.mpr hd), sub_eq_add_neg, integral_add_right_eq_self]

private theorem integral_sq_norm_toLp {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫ t : ℝ, ‖f t‖ ^ 2) = ‖hf.toLp f‖ ^ 2 := by
  have hi : ⟪hf.toLp f, hf.toLp f⟫_ℂ = (↑(∫ t : ℝ, ‖f t‖ ^ 2) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with t ht
    rw [ht, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hi]
  rfl

private theorem centered_inverse_mass {F : ℂ → ℂ} {v : ℝ → ℂ}
    (hg : MemLp (frequencyRestriction F) 2 volume)
    (hv : v =ᵐ[volume] (Lp.fourierTransformₗᵢ ℝ ℂ).symm
      (hg.toLp (frequencyRestriction F))) :
    (∫ t : ℝ, ‖v t‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∫ ω : ℝ, ‖F (ω : ℂ)‖ ^ 2 := by
  have hv₂ : MemLp v 2 volume :=
    (Lp.memLp _).ae_eq hv.symm
  have he : hv₂.toLp v =
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm (hg.toLp (frequencyRestriction F)) :=
    Lp.ext (hv₂.coeFn_toLp.trans hv)
  rw [integral_sq_norm_toLp hv₂, he, LinearIsometryEquiv.norm_map,
    ← integral_sq_norm_toLp hg]
  exact (Measure.integral_comp_mul_left (fun ω : ℝ => ‖F (ω : ℂ)‖ ^ 2)
    (2 * Real.pi)).trans (by rw [abs_of_pos (by positivity), smul_eq_mul])

private theorem normalized_centered_moment {v : ℝ → ℂ} {a q : ℝ} {normalizer : ℂ}
    (hv : Integrable v) (hs : ∀ t : ℝ, a < |t| → v t = 0) :
    (∫ t : ℝ, Real.exp (-q * t) * (v t / normalizer).re) =
      (((∫ t : ℝ, Complex.exp (-(q : ℂ) * (t : ℂ)) * v t) / normalizer)).re := by
  let f (t : ℝ) := Complex.exp (-(q : ℂ) * (t : ℂ)) * v t
  have hExp (t : ℝ) : Complex.exp (-(q : ℂ) * (t : ℂ)) =
      (Real.exp (-q * t) : ℂ) := by norm_cast
  have hf : Integrable f := by
    have hc : Continuous (fun t : ℝ => Complex.exp (-(q : ℂ) * (t : ℂ))) := by
      fun_prop
    apply (hv.norm.const_mul (Real.exp (|q| * a))).mono'
      (hc.aestronglyMeasurable.mul hv.aestronglyMeasurable)
    filter_upwards [] with t
    change ‖f t‖ ≤ Real.exp (|q| * a) * ‖v t‖
    by_cases ht : |t| ≤ a
    · rw [show ‖f t‖ = Real.exp (-q * t) * ‖v t‖ by
          dsimp only [f]
          rw [norm_mul, hExp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
        rw [abs_mul, abs_neg]
        exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)))
    · simp [f, hs t (lt_of_not_ge ht)]
  rw [← integral_div]
  change _ = RCLike.re (∫ t : ℝ, f t / normalizer)
  rw [← integral_re (hf.div_const normalizer)]
  apply integral_congr_ae
  filter_upwards [] with t
  change _ = (f t / normalizer).re
  dsimp only [f]
  rw [hExp, mul_div_assoc, Complex.re_ofReal_mul]

private theorem physical_witness (n : ℕ) (j : Mode n) {L : ℝ}
    {v : ℝ → ℂ} (hv : Integrable v) (hv₂ : MemLp v 2 volume)
    (hs : ∀ t : ℝ, L / 2 < |t| → v t = 0) {normalizer : ℂ} (hnormalizer : normalizer ≠ 0)
    (hm : ∀ k : Mode n, (∫ t : ℝ, Complex.exp (-(rate n k : ℂ) * (t : ℂ)) * v t) =
      if k = j then normalizer else 0) :
    let T := L / (n : ℝ) ^ 2
    ∃ u : ℝ → ℝ, MemLp u 2 volume ∧ (∀ s ∉ Icc 0 T, u s = 0) ∧
      (∀ k : Mode n, (∫ s in Ioo 0 T, u s * (weight n k * Real.exp (-physicalRate n k * s))) =
        if k = j then 1 else 0) ∧
      windowNorm T u ≤ (n : ℝ) * Real.exp (rate n j * L / 2) /
        (weight n j * ‖normalizer‖) * Real.sqrt (∫ t : ℝ, ‖v t‖ ^ 2) := by
  have hn : 0 < (n : ℝ) := by
    have := j.isLt
    exact_mod_cast (show 0 < n by omega)
  let d : ℝ := (n : ℝ) ^ 2
  let a : ℝ := L / 2
  let T := L / d
  let gain := Real.exp (rate n j * a) / weight n j
  let w (t : ℝ) := (v t / normalizer).re
  let u (s : ℝ) := (d * gain) * w (d * s - a)
  have hd : 0 < d := by positivity
  have hgain : 0 < gain := div_pos (Real.exp_pos _) (weight_pos n j)
  have hnorm : 0 < ‖normalizer‖ := norm_pos_iff.mpr hnormalizer
  have hus (s : ℝ) (hs' : s ∉ Icc 0 T) : u s = 0 := by
    have hdt : a < |d * s - a| := by
      apply lt_of_not_ge
      intro ht
      have hbounds := abs_le.mp ht
      apply hs'
      constructor
      · exact nonneg_of_mul_nonneg_right (by linarith [hbounds.1]) hd
      · exact (le_div_iff₀ hd).2 (by
          rw [mul_comm s d]
          dsimp [a] at hbounds
          linarith [hbounds.2])
    simp [u, w, hs _ hdt]
  have haff : Integrable (fun s : ℝ => ‖v (d * s - a)‖ ^ 2) := by
    have hi := (memLp_two_iff_integrable_sq_norm hv₂.aestronglyMeasurable).mp hv₂
    exact (hi.comp_add_right (-a)).comp_mul_left' hd.ne'
  let normFactor := (d * gain / ‖normalizer‖) ^ 2
  have hpoint (s : ℝ) : u s ^ 2 ≤ normFactor * ‖v (d * s - a)‖ ^ 2 := by
    have hw : |w (d * s - a)| ≤ ‖v (d * s - a)‖ / ‖normalizer‖ := by
      rw [← norm_div]
      exact Complex.abs_re_le_norm _
    calc
      u s ^ 2 = (d * gain) ^ 2 * |w (d * s - a)| ^ 2 := by
        dsimp only [u]
        rw [mul_pow, sq_abs]
      _ ≤ (d * gain) ^ 2 * (‖v (d * s - a)‖ / ‖normalizer‖) ^ 2 := by gcongr
      _ = _ := by dsimp [normFactor]; rw [div_pow, div_pow]; ring
  have hum : AEStronglyMeasurable u volume := by
    have hi : Integrable (fun s : ℝ => v (d * s - a) / normalizer) :=
      (((hv.comp_add_right (-a)).comp_mul_left' hd.ne').div_const normalizer)
    exact (Complex.continuous_re.comp_aestronglyMeasurable hi.aestronglyMeasurable).const_mul _
  have hui : Integrable (fun s => u s ^ 2) := by
    apply (haff.const_mul normFactor).mono' (hum.pow 2)
    filter_upwards [] with s
    change ‖u s ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint s
  refine ⟨u, (memLp_two_iff_integrable_sq hum).mpr hui, hus, ?_, ?_⟩
  · intro k
    rw [← integral_Icc_eq_integral_Ioo,
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun s h => by rw [hus s h, zero_mul])]
    have hfactor (s : ℝ) :
        u s * (weight n k * Real.exp (-physicalRate n k * s)) =
          (d * gain * weight n k * Real.exp (-rate n k * a)) *
            (Real.exp (-rate n k * (d * s - a)) * w (d * s - a)) := by
      have he : -physicalRate n k * s = -rate n k * a + -rate n k * (d * s - a) := by
        simp only [physicalRate, d]
        ring
      rw [he, Real.exp_add]
      dsimp [u]
      ring
    simp_rw [hfactor]
    rw [integral_const_mul, integral_affine (fun t => Real.exp (-rate n k * t) * w t) hd a,
      smul_eq_mul]
    have hmoment :
        (∫ t : ℝ, Real.exp (-rate n k * t) * w t) = if k = j then 1 else 0 := by
      change (∫ t : ℝ, Real.exp (-rate n k * t) * (v t / normalizer).re) = _
      rw [normalized_centered_moment hv hs, hm]
      by_cases hk : k = j
      · simp [hk, hnormalizer]
      · simp [hk]
    rw [hmoment]
    by_cases hk : k = j
    · subst k
      rw [ite_eq_left rfl, mul_one]
      have hexp : Real.exp (rate n j * a) * Real.exp (-rate n j * a) = 1 := by
        rw [← Real.exp_add, show rate n j * a + -rate n j * a = 0 by ring, Real.exp_zero]
      dsimp [gain]
      calc
        d * (Real.exp (rate n j * a) / weight n j) * weight n j *
            Real.exp (-rate n j * a) * d⁻¹ =
            Real.exp (rate n j * a) * Real.exp (-rate n j * a) := by
          field_simp [hd.ne', (weight_pos n j).ne']
        _ = 1 := hexp
    · simp [hk]
  · unfold windowNorm
    rw [← integral_Icc_eq_integral_Ioo,
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun s h => by rw [hus s h]; norm_num)]
    calc
      _ ≤ Real.sqrt (∫ s : ℝ, normFactor * ‖v (d * s - a)‖ ^ 2) :=
        Real.sqrt_le_sqrt (integral_mono hui (haff.const_mul normFactor) hpoint)
      _ = _ := by
        rw [integral_const_mul, integral_affine (fun t => ‖v t‖ ^ 2) hd a, smul_eq_mul,
          ← mul_assoc]
        have hfactor : normFactor * d⁻¹ =
            ((n : ℝ) * Real.exp (rate n j * L / 2) / (weight n j * ‖normalizer‖)) ^ 2 := by
          dsimp [normFactor, gain, a, d]
          rw [show rate n j * (L / 2) = rate n j * L / 2 by ring]
          field_simp [hn.ne', (weight_pos n j).ne', hnorm.ne']
        rw [hfactor, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq]
        exact div_nonneg (mul_nonneg hn.le (Real.exp_pos _).le)
          (mul_nonneg (weight_pos n j).le hnorm.le)

#print axioms physical_witness

end

end D5.S3.Observer.Linear.ReflectingHeatInterpolation
