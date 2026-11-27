/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedBound
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: On the actual zero line the weighted Chebyshev integral has explicit asymmetric bounds. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RobinActualWeightedTail
import Batteries.Tactic.OpenPrivate
import D5.S3.Arith.GoldenResource.RobinRationalBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U psiErrorKernel)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace

open private log_pi_lower_r6 from D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

/-- The ordinary weighted Chebyshev error integral. -/
def J (j x : ℝ) : ℝ := ∫ t in Ioi x, psiErrorKernel t * (t ^ (1-j) * H j (Real.log t))

def weight (j t : ℝ) : ℝ := H j (Real.log t) / t ^ (j+1)

lemma J_eq_integral {j x : ℝ} (hx : 0 < x) :
    J j x = ∫ t in Ioi x, (Chebyshev.psi t-t)*weight j t := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 := hx.trans ht
  simp only [psiErrorKernel, weight]
  rw [← Real.rpow_natCast, Nat.cast_ofNat]
  rw [show (1-j:ℝ) = 2-(j+1) by ring, Real.rpow_sub ht0]
  rw [show t ^ (2:ℝ) / t^(j+1) = t^(2:ℝ) / t^(j+1) by rfl]
  field_simp [Real.rpow_pos_of_pos ht0 (2:ℝ) |>.ne', (Real.rpow_pos_of_pos ht0 (j+1)).ne']

private lemma K_integrable {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn (fun v => Real.exp v * psiErrorKernel (Real.exp v)) (Ioi u) := by
  exact (integrableOn_comp_exp_Ioi psiErrorKernel u).mpr
    (chebyshev_error_kernel_integrable.mono_set (Ioi_subset_Ioi (Real.one_le_exp_iff.mpr hu)))

private lemma tail_K (u : ℝ) : (∫ v in Ioi u, Real.exp v * psiErrorKernel (Real.exp v)) = Q (Real.exp u) :=
  integral_comp_exp_Ioi psiErrorKernel u

private lemma Q_exp_formula {v : ℝ} (hv : Real.log 2 ≤ v) :
    Q (Real.exp v) = (zeroQ v).re + Real.exp (-v)*(trivialT v - Real.log (2*Real.pi)) := by
  have hv0 : 0 < v := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans_le hv
  have hx : 2 ≤ Real.exp v := by simpa [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr hv
  have h := D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    chebyshev_error_kernel_integrable hx
  change Q (Real.exp v) = _ at h
  have hQ : Q (Real.exp v) = -U (Real.exp v) / Real.exp v := by
    rw [h,U]
    field_simp [(Real.exp_ne_zero v)]
    ring
  have hf := congrArg Complex.re (actual_integrated_explicit_formula hv0)
  simp only [Complex.ofReal_re] at hf
  rw [hQ,zeroQ,neg_mul,Complex.neg_re,Complex.re_ofReal_mul, hf, Real.exp_neg]
  ring

private lemma J_transport {j u : ℝ} (hj : 1 ≤ j) (hu : Real.log 2 ≤ u) :
    IntegrableOn (fun t => psiErrorKernel t * (t^(1-j)*H j (Real.log t))) (Ioi (Real.exp u)) ∧
    J j (Real.exp u) = A j u * Q (Real.exp u) - ∫ v in Ioi u, d j v * Q (Real.exp v) := by
  have hu0 : 0 < u := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans_le hu
  have h := logarithmic_transport hj hu0 (K_integrable hu0.le)
  have he : (fun v => Real.exp v * psiErrorKernel (Real.exp v) * A j v) =
    (fun v => Real.exp v • (psiErrorKernel (Real.exp v) * ((Real.exp v)^(1-j)*H j (Real.log (Real.exp v))))) := by
    funext v
    unfold A
    rw [← Real.exp_mul, Real.log_exp, smul_eq_mul, mul_comm v (1-j)]
    ring
  refine ⟨(integrableOn_comp_exp_Ioi _ u).mp (he ▸ h.1), ?_⟩
  rw [J, ← integral_comp_exp_Ioi, ← he, h.2.2, tail_K]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [tail_K]

private def F (v : ℝ) : ℝ := Real.exp (-v)*trivialT v

private lemma F_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ F v :=
  mul_nonneg (Real.exp_nonneg _) (trivialT_nonneg hv)

private lemma T_antitone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : trivialT v ≤ trivialT u := by
  apply (trivialT_summable (hu.trans huv)).tsum_le_tsum _ (trivialT_summable hu)
  intro k
  apply mul_le_mul_of_nonneg_left _ (trivialCoeff_nonneg k)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left huv (neg_nonpos.mpr (by positivity))

private lemma F_antitone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : F v ≤ F u := by
  unfold F
  exact mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg huv)) (T_antitone hu huv)
    (trivialT_nonneg (hu.trans huv)) (Real.exp_nonneg _)

private lemma T_quarter_bound {u : ℝ} (hu : Real.log 2 ≤ u) : trivialT u ≤ 1/12 := by
  have hu0 : 0 ≤ u := (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans hu
  have hlt : (2/3:ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hsum : trivialT u ≤ (1/4:ℝ)*(1-Real.log 2) := by
    unfold trivialT
    rw [← trivialCoeff_hasSum.tsum_eq, ← tsum_mul_left]
    refine (trivialT_summable hu0).tsum_le_tsum (fun k => ?_) (trivialCoeff_hasSum.summable.mul_left _)
    have harg : -(2*((k:ℝ)+1))*u ≤ -(2*Real.log 2) := by
      nlinarith only [hu, mul_nonneg (Nat.cast_nonneg k : 0 ≤ (k:ℝ)) hu0]
    have he : Real.exp (-(2*Real.log 2)) = 1/4 := by
      rw [Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log (by norm_num : (0:ℝ)<2), Real.rpow_two]
      norm_num
    rw [mul_comm (1/4:ℝ)]
    apply mul_le_mul_of_nonneg_left _ (trivialCoeff_nonneg k)
    rw [← he]
    exact Real.exp_le_exp.mpr harg
  linarith

private lemma F_d_integrable {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) :
    IntegrableOn (fun v => d j v * F v) (Ioi u) := by
  apply ((d_integrable hj hu).mul_const (F u)).mono'
  · have hc : ContinuousOn F (Ioi u) := by
      unfold F
      exact (by fun_prop : Continuous fun v : ℝ => Real.exp (-v)).continuousOn.mul
        (trivialT_continuousOn.mono (fun _ hv => (hu.trans hv).le))
    exact (show ContinuousOn (d j) (Ioi u) by
      intro v hv
      have hv0 := hu.trans hv
      unfold d H
      fun_prop (disch := positivity)).mul hc |>.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (d_nonneg hj (hu.trans hv)) (F_nonneg (hu.trans hv).le))]
    exact mul_le_mul_of_nonneg_left (F_antitone hu.le hv.le) (d_nonneg hj (hu.trans hv))

private lemma exp_d_integrable {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) :
    IntegrableOn (fun v => d j v * Real.exp (-v)) (Ioi u) := by
  have h := logarithmic_transport hj hu (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) u)
  apply h.2.1.congr
  filter_upwards with v
  rw [integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0)]
  norm_num

private lemma const_response {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) :
    A j u * Real.exp (-u) - (∫ v in Ioi u, d j v*Real.exp (-v)) = Real.exp (-j*u)/u := by
  have h := logarithmic_transport hj hu (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) u)
  have htail (v : ℝ) : (∫ t in Ioi v, Real.exp (-1*t)) = Real.exp (-v) := by
    rw [integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0)]
    norm_num
  simp_rw [htail] at h
  have hi : IntegrableOn (fun v => Real.exp (-j*v)*H j v) (Ioi u) := by
    apply h.1.congr
    filter_upwards with v
    unfold A
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hderiv (v : ℝ) (hv : 0 < v) : HasDerivAt (fun t => -(Real.exp (-j*t)/t)) (Real.exp (-j*v)*H j v) v := by
    have hd := ((((hasDerivAt_id v).const_mul (-j)).exp).div (hasDerivAt_id v) hv.ne').neg
    convert hd using 1
    · ext t; simp
    · simp only [id_eq]; unfold H; field_simp [hv.ne']; ring
  have htend : Tendsto (fun t => -(Real.exp (-j*t)/t)) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-j*t)) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using (he.mul hinv).neg
  have heval : (∫ v in Ioi u, Real.exp (-j*v)*H j v) = Real.exp (-j*u)/u := by
    simpa using integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun v hv => hderiv v (hu.trans_le hv)) hi htend
  rw [← h.2.2, ← heval]
  exact setIntegral_congr_fun measurableSet_Ioi (fun v _ => by
    unfold A; rw [← mul_assoc, ← Real.exp_add]; congr 2; ring)

private lemma residual_response {j u : ℝ} (hj : 1 ≤ j) (hj10 : j ≤ 10) (hu : Real.log 2 ≤ u) :
    let R := A j u * (F u-Real.log (2*Real.pi)*Real.exp (-u)) -
      ∫ v in Ioi u, d j v*(F v-Real.log (2*Real.pi)*Real.exp (-v));
    -Real.log (2*Real.pi)*Real.exp (-j*u)/u ≤ R ∧ R ≤ 0 := by
  dsimp only
  have hu2 : (2/3:ℝ) < u := (lt_trans (by norm_num) Real.log_two_gt_d9).trans_le hu
  have hu0 : 0 < u := by linarith
  let T := A j u * F u - ∫ v in Ioi u, d j v*F v
  have hT0 : 0 ≤ T := by
    have hb : (∫ v in Ioi u, d j v*F v) ≤ A j u*F u := by
      rw [← d_mass hj hu0, ← integral_mul_const]
      exact setIntegral_mono_on (F_d_integrable hj hu0) ((d_integrable hj hu0).mul_const _) measurableSet_Ioi
        (fun v hv => mul_le_mul_of_nonneg_left (F_antitone hu0.le hv.le) (d_nonneg hj (hu0.trans hv)))
    dsimp [T]; linarith
  have hTupper : T ≤ Real.log (2*Real.pi)*Real.exp (-j*u)/u := by
    have h0 : 0 ≤ ∫ v in Ioi u, d j v*F v := setIntegral_nonneg measurableSet_Ioi
      (fun v hv => mul_nonneg (d_nonneg hj (hu0.trans hv)) (F_nonneg (hu0.trans hv).le))
    have hl : 1 ≤ Real.log (2*Real.pi) := by
      have h := Real.log_le_log (by norm_num : (0:ℝ)<4) (by linarith [Real.pi_gt_three] : 4 ≤ 2*Real.pi)
      rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)] at h
      linarith [Real.log_two_gt_d9]
    have h1 : j + 1/u ≤ 12 := by
      have : 1/u ≤ 2 := (div_le_iff₀ hu0).mpr (by linarith)
      linarith
    have h2 : (j+1/u)*trivialT u ≤ Real.log (2*Real.pi) := by
      have hh : (j+1/u)*trivialT u ≤ 12*(1/12:ℝ) :=
        mul_le_mul h1 (T_quarter_bound hu) (trivialT_nonneg hu0.le) (by norm_num)
      linarith
    have he : A j u*F u = (Real.exp (-j*u)/u)*((j+1/u)*trivialT u) := by
      unfold A F H
      have he : Real.exp ((1-j)*u)*Real.exp (-u) = Real.exp (-j*u) := by
        rw [← Real.exp_add]; congr 1; ring
      calc
        _ = (Real.exp ((1-j)*u)*Real.exp (-u)) * (j/u+1/u^2)*trivialT u := by ring
        _ = _ := by rw [he]; ring
    calc
      T ≤ A j u*F u := by dsimp [T]; linarith
      _ ≤ Real.log (2*Real.pi)*Real.exp (-j*u)/u := by
        rw [he]
        calc
          _ ≤ (Real.exp (-j*u)/u)*Real.log (2*Real.pi) := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = _ := by ring
  have hsplit : (∫ v in Ioi u, d j v*(F v - Real.log (2*Real.pi)*Real.exp (-v))) =
      (∫ v in Ioi u, d j v*F v) - Real.log (2*Real.pi)*(∫ v in Ioi u, d j v*Real.exp (-v)) := by
    calc
      _ = ∫ v in Ioi u, d j v*F v - Real.log (2*Real.pi)*(d j v*Real.exp (-v)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun v _ => by ring)
      _ = _ := by rw [integral_sub (F_d_integrable hj hu0) ((exp_d_integrable hj hu0).const_mul _), integral_const_mul]
  have h : A j u*(F u-Real.log (2*Real.pi)*Real.exp (-u)) -
      (∫ v in Ioi u, d j v*(F v-Real.log (2*Real.pi)*Real.exp (-v))) =
      T - Real.log (2*Real.pi)*Real.exp (-j*u)/u := by
    rw [hsplit]
    dsimp [T]
    have hc := const_response hj hu0
    linear_combination -Real.log (2*Real.pi)*hc
  rw [h]
  constructor
  · exact (by simpa only [zero_sub, neg_div, neg_mul] using sub_le_sub_right hT0 (Real.log (2*Real.pi)*Real.exp (-j*u)/u))
  · exact sub_nonpos.mpr hTupper

/-- Exact two-sided weighted bound at the exponents required for Robin's prime bands. -/
theorem J_log_bounds (hline : ∀ k : ℕ, (actualZero k).re = 1/2) {j u : ℝ} (hj : 1 ≤ j) (hj10 : j ≤ 10)
    (hu : Real.log 2 ≤ u) :
    let E := firstLiMass*Real.exp ((1/2-j)*u)*H j u;
    -E-Real.log (2*Real.pi)*Real.exp (-j*u)/u ≤ J j (Real.exp u) ∧ J j (Real.exp u) ≤ E := by
  dsimp only
  have hu0 : 0 < u := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans_le hu
  have hz : IntegrableOn (fun v => d j v*(zeroQ v).re) (Ioi u) := by
    have h := (zeroQ_d_integrable hj hu0).re
    change IntegrableOn (fun v => ((d j v:ℂ)*zeroQ v).re) (Ioi u) at h
    simpa only [Complex.re_ofReal_mul] using h
  have hR : IntegrableOn (fun v => d j v*(F v-Real.log (2*Real.pi)*Real.exp (-v))) (Ioi u) := by
    apply ((F_d_integrable hj hu0).sub ((exp_d_integrable hj hu0).const_mul (Real.log (2*Real.pi)))).congr
    filter_upwards with v
    simp only [Pi.sub_apply]; ring
  have hsplit : (∫ v in Ioi u,d j v*Q (Real.exp v)) =
      (∫ v in Ioi u,d j v*(zeroQ v).re) + (∫ v in Ioi u,d j v*(F v-Real.log (2*Real.pi)*Real.exp (-v))) := by
    rw [← integral_add hz hR]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [Q_exp_formula (hu.trans hv.le),F]
    ring
  have hzre := congrArg Complex.re (zeroQ_response hj hu0)
  have hre := integral_re (zeroQ_d_integrable hj hu0)
  change (∫ v in Ioi u, ((d j v:ℂ)*zeroQ v).re) = (∫ v in Ioi u, (d j v:ℂ)*zeroQ v).re at hre
  rw [Complex.sub_re, Complex.re_ofReal_mul, ← hre] at hzre
  simp only [Complex.re_ofReal_mul] at hzre
  have hbound := actualWeightedZeroSum_norm_le_of_line hj hu0 hline
  have habs := (Complex.abs_re_le_norm _).trans hbound
  have htotal : J j (Real.exp u) = (∑' k, actualWeightedZeroContribution j k u).re +
      (A j u*(F u-Real.log (2*Real.pi)*Real.exp (-u)) - ∫ v in Ioi u,d j v*(F v-Real.log (2*Real.pi)*Real.exp (-v))) := by
    rw [(J_transport hj hu).2, hsplit, Q_exp_formula hu, ← hzre, F]
    ring
  rw [htotal]
  obtain ⟨hlo,hhi⟩ := residual_response hj hj10 hu
  constructor
  · convert add_le_add (abs_le.mp habs).1 hlo using 1 <;> ring
  · simpa only [add_zero] using add_le_add (abs_le.mp habs).2 hhi

theorem firstLiMass_lt_twentieth : firstLiMass < 1/20 := by
  rw [firstLiMass_split]
  linarith [D5.S3.Arith.GoldenResource.RobinRationalBasis.eulerMascheroni_decimal_bounds.2,
    D5.S3.Arith.GoldenResource.RobinRationalBasis.log_two_decimal_bounds.1,
    log_pi_lower_r6]

theorem log_two_pi_lt_two : Real.log (2*Real.pi) < 2 := by
  apply (Real.log_lt_iff_lt_exp (by positivity)).mpr
  rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
  nlinarith [Real.pi_lt_d6, Real.exp_one_gt_d9]

theorem J_one_eq_weightedTail (x : ℝ) : J 1 x =
    D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail psiErrorKernel x := by
  unfold J D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [H, D5.S3.Weil.Mertens.WeightedTailTransport.r]
  rw [sub_self,Real.rpow_zero,one_mul]
  by_cases h : Real.log t = 0
  · simp [h]
  · field_simp [h]
    ring

theorem actual_weighted_tail_lower (hline : ∀ k : ℕ, (actualZero k).re = 1/2) {x : ℝ} (hx : 2 ≤ x) :
    -((1/20:ℝ)*(1+1/Real.log x)+2/Real.sqrt x) ≤
      Real.sqrt x*Real.log x*D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail psiErrorKernel x := by
  have hx0 : 0 < x := by linarith
  have hu : 0 < Real.log x := Real.log_pos (by linarith)
  have h := (J_log_bounds hline (j:=1) (by norm_num) (by norm_num) (Real.log_le_log (by norm_num) hx)).1
  rw [Real.exp_log hx0, J_one_eq_weightedTail] at h
  have he : Real.exp ((1/2-1)*Real.log x) = (Real.sqrt x)⁻¹ := by
    rw [show (1/2-1:ℝ) = -(1/2) by norm_num,neg_mul,Real.exp_neg,
      Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx0,mul_comm (Real.log x) (1/2)]
  have he2 : Real.exp (-1*Real.log x) = x⁻¹ := by rw [neg_one_mul,Real.exp_neg,Real.exp_log hx0]
  rw [he,he2] at h
  have hs := mul_le_mul_of_nonneg_left h (show 0 ≤ Real.sqrt x*Real.log x by positivity)
  have hs2 : Real.sqrt x*Real.log x *
      (-(firstLiMass*(Real.sqrt x)⁻¹*H 1 (Real.log x)) - Real.log (2*Real.pi)*x⁻¹/Real.log x) =
      -(firstLiMass*(1+1/Real.log x) + Real.log (2*Real.pi)/Real.sqrt x) := by
    have hsx : Real.sqrt x * x⁻¹ = (Real.sqrt x)⁻¹ := by
      field_simp [(Real.sqrt_pos.mpr hx0).ne',hx0.ne']
      nlinarith [Real.sq_sqrt hx0.le]
    calc
      _ = -(firstLiMass*(1+1/Real.log x) + Real.log (2*Real.pi)*(Real.sqrt x*x⁻¹)) := by
        unfold H
        field_simp [hu.ne',(Real.sqrt_pos.mpr hx0).ne']
        ring
      _ = _ := by rw [hsx]; ring
  rw [hs2] at hs
  refine le_trans ?_ hs
  have h1 := mul_le_mul_of_nonneg_right firstLiMass_lt_twentieth.le
    (show 0 ≤ 1+1/Real.log x by positivity)
  have h2 := div_le_div_of_nonneg_right log_two_pi_lt_two.le (Real.sqrt_nonneg x)
  linarith

end D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
