/- GID: D5/S3/Fourier/Concentration/FejerRelativeLocalization
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FejerRelativeLocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The nonnegative Fejer collision moment controls its own relative far-time remainder. -/

import D5.S3.Fourier.Concentration.FejerCollisionVariance

/-! A relative truncation bound uniform in the finite spectrum and degree. -/

open Finset Set MeasureTheory Filter
open scoped Topology
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Concentration.FejerCollisionVariance
open D5.S3.Analytic.Fourier.AngularFejerKernel

noncomputable section

namespace D5.S3.Fourier.Concentration.FejerRelativeLocalization

/-- The Fejer kernel is uniformly positive inside the reciprocal resolution window. -/
private theorem K_floor {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : |t| ≤ T) :
    1/(8*Real.pi*T) ≤ K T⁻¹ t := by
  have hx : |T⁻¹*t/2| ≤ 1/2 := by
    rw [abs_div,abs_mul,abs_of_pos (inv_pos.mpr hT)]
    norm_num
    have := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hT.le)
    rw [inv_mul_cancel₀ hT.ne'] at this
    linarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x := T⁻¹*t/2)
  have hs := Real.cos_le_sinc (show |T⁻¹*t/2| < Real.pi/2 by linarith [Real.pi_gt_three])
  have hs' : (1:ℝ)/2 ≤ Real.sinc (T⁻¹*t/2) := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hx
    nlinarith only [hcos,hs,hlo,hhi,mul_nonneg (by linarith : 0 ≤ T⁻¹*t/2+1/2)
      (by linarith : 0 ≤ 1/2-T⁻¹*t/2)]
  have hsq : (1:ℝ)/4 ≤ Real.sinc (T⁻¹*t/2)^2 := by
    calc
      _ = ((1:ℝ)/2)^2 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hs' 2
  calc
    _ = (T⁻¹/(2*Real.pi))*(1/4) := by field_simp <;> ring
    _ ≤ K T⁻¹ t := mul_le_mul_of_nonneg_left hsq (by positivity)

/-- At positive resolution the relative far-time error is uniform over degrees
and all finite spectra with nonnegative weights. -/
theorem relative_fejer_truncation {J : Type*} [Fintype J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (p : ℕ)
    {η R : ℝ} (hη : 0 < η) (hR : 1 ≤ η*R) :
    let kernel := fun z : ℝ × ℝ => K z.1 z.2
    let f := fun t => ‖complexScore g w t‖^(2*p)
    let M := ∫ t : ℝ, kernel (η,t)*f t
    M - (∫ t in -R..R, kernel (η,t)*f t) ≤ (64/(η*R))*M := by
  classical
  intro kernel f M
  change (∫ t : ℝ, K η t*f t) - (∫ t in -R..R, K η t*f t) ≤ (64/(η*R))*M
  have hRpos : 0 < R := by
    by_contra! hn
    linarith [mul_nonpos_of_nonneg_of_nonpos hη.le hn]
  let H (t : ℝ) := K η t*f t
  let I (r : ℝ) := ∫ t in -r..r, H t
  change M - I R ≤ (64/(η*R))*M
  have hf : Continuous f := (complexScore_continuous g w).norm.pow _
  have hf0 (t : ℝ) : 0 ≤ f t := by dsimp [f]; positivity
  have hH : Continuous H := (K_continuous η).mul hf
  have hwhole (b : ℝ) (hb : 0 < b) : Integrable (fun t => K b t*f t) := by
    dsimp [f]
    simp_rw [moment_eq_pair]
    exact kernel_pair_integrable _ _ _ hb
  have hcompare (b : ℝ) (hb : 0 < b) (hbe : b ≤ η) : (∫ t : ℝ, K b t*f t) ≤ M := by
    dsimp [f,M,kernel]
    rw [(fejer_collision_comparison g w p hb).1,(fejer_collision_comparison g w p hη).1]
    refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (monomialWeight_nonneg w hw m) (monomialWeight_nonneg w hw n))
    unfold phi
    exact max_le_max_left _ (sub_le_sub_left (div_le_div_of_nonneg_left (abs_nonneg _) hb hbe) _)
  have hlocal (T : ℝ) (hT : 0 < T) (hTη : 1 ≤ η*T) :
      (∫ t in -T..T, f t) ≤ 8*Real.pi*T*M := by
    have hb : 0 < T⁻¹ := inv_pos.mpr hT
    have hbe : T⁻¹ ≤ η := by rw [inv_eq_one_div,div_le_iff₀ hT]; exact hTη
    have hc : Continuous (fun t => K T⁻¹ t*f t) := (K_continuous _).mul hf
    have hA : -T ≤ T := by linarith
    have hbound : (1/(8*Real.pi*T))*(∫ t in -T..T, f t) ≤ M := by
      rw [← intervalIntegral.integral_const_mul]
      calc
        _ ≤ ∫ t in -T..T, K T⁻¹ t*f t :=
          intervalIntegral.integral_mono_on hA ((hf.const_mul _).intervalIntegrable _ _) (hc.intervalIntegrable _ _)
            (fun t ht => mul_le_mul_of_nonneg_right (K_floor hT (abs_le.mpr ht)) (hf0 t))
        _ ≤ ∫ t : ℝ, K T⁻¹ t*f t := by
          rw [intervalIntegral.integral_of_le hA]
          exact setIntegral_le_integral (hwhole _ hb) (ae_of_all _ fun t =>
            mul_nonneg ((fejer_law hb).1 t) (hf0 t))
        _ ≤ M := hcompare _ hb hbe
    rw [one_div,inv_mul_eq_div,div_le_iff₀ (by positivity : 0 < 8*Real.pi*T)] at hbound
    linarith
  have hstep (r : ℝ) (hr : 0 < r) (hrη : 1 ≤ η*r) :
      I (2*r) - I r ≤ (32/(η*r))*M := by
    let c := 2/(Real.pi*η*r^2)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hpoint (t : ℝ) (ht : r ≤ |t|) : H t ≤ c*f t := by
      have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
      have hsq : r^2 ≤ t^2 := by
        rw [← sq_abs t]
        exact pow_le_pow_left₀ hr.le ht 2
      apply mul_le_mul_of_nonneg_right _ (hf0 t)
      exact (K_bound hη ht0).trans (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hsq (by positivity)))
    have hFleft : (∫ t in -(2*r)..-r, H t) ≤ c*(∫ t in -(2*r)..-r, f t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by linarith) (hH.intervalIntegrable _ _) ((hf.const_mul _).intervalIntegrable _ _)
      intro t ht
      exact hpoint t (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2])
    have hFright : (∫ t in r..2*r, H t) ≤ c*(∫ t in r..2*r, f t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by linarith) (hH.intervalIntegrable _ _) ((hf.const_mul _).intervalIntegrable _ _)
      intro t ht
      exact hpoint t (by rw [abs_of_nonneg (hr.le.trans ht.1)]; exact ht.1)
    have hsplit (F : ℝ → ℝ) (hF : Continuous F) :
        (∫ t in -(2*r)..2*r, F t) = (∫ t in -(2*r)..-r, F t) +
          (∫ t in -r..r, F t) + (∫ t in r..2*r, F t) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)]
    have hmid : 0 ≤ ∫ t in -r..r,f t := intervalIntegral.integral_nonneg_of_forall (by linarith) hf0
    have hparts : (∫ t in -(2*r)..-r, f t) + (∫ t in r..2*r, f t) ≤ 8*Real.pi*(2*r)*M := by
      have h := hlocal (2*r) (by positivity) (by linarith)
      rw [hsplit f hf] at h
      linarith
    have hboth := add_le_add hFleft hFright
    have htail := mul_le_mul_of_nonneg_left hparts hc
    have he : c*(8*Real.pi*(2*r)*M) = (32/(η*r))*M := by
      dsimp [c]
      field_simp
      <;> ring
    dsimp [I]
    rw [hsplit H hH,← he]
    linarith only [hboth,htail]
  let radius (n : ℕ) := R*2^n
  have hradius (n : ℕ) : 0 < radius n := by dsimp [radius]; positivity
  have hscale (n : ℕ) : 1 ≤ η*radius n := by
    dsimp [radius]
    rw [← mul_assoc]
    exact one_le_mul_of_one_le_of_one_le hR (one_le_pow₀ (by norm_num))
  have hgeom (n : ℕ) : I (radius n) ≤ I R + (64/(η*R))*M*(1-(1/2:ℝ)^n) := by
    induction n with
    | zero => simp [radius]
    | succ n ih =>
      have h := hstep (radius n) (hradius n) (hscale n)
      have hn : radius (n+1) = 2*radius n := by dsimp [radius]; rw [pow_succ]; ring
      rw [hn]
      have he : (32/(η*radius n))*M = ((64/(η*R))*M)*(1/2:ℝ)^(n+1) := by
        dsimp [radius]
        rw [pow_succ,div_pow]
        field_simp
        <;> ring
      rw [he] at h
      rw [pow_succ]
      rw [pow_succ] at h
      linarith only [ih,h]
  have hradlim : Tendsto radius atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).const_mul_atTop hRpos
  have hilim : Tendsto (fun n => I (radius n)) atTop (𝓝 M) :=
    intervalIntegral_tendsto_integral (hwhole η hη) (tendsto_neg_atTop_atBot.comp hradlim) hradlim
  have hglim : Tendsto (fun n : ℕ => I R + (64/(η*R))*M*(1-(1/2:ℝ)^n)) atTop
      (𝓝 (I R + (64/(η*R))*M)) := by
    have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hq := (tendsto_const_nhds (x := (1:ℝ))).sub hp
    have hm := (tendsto_const_nhds (x := (64/(η*R))*M)).mul hq
    simpa only [sub_zero,mul_one] using (tendsto_const_nhds (x := I R)).add hm
  have := le_of_tendsto_of_tendsto hilim hglim (Eventually.of_forall hgeom)
  linarith

#print axioms relative_fejer_truncation

end D5.S3.Fourier.Concentration.FejerRelativeLocalization
