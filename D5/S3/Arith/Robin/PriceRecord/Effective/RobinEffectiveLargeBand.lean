/- GID: D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand
   mirror-E: none(waiver:analytic-arithmetic-inequality)
   anchors: []
   utility: none
   digest: The actual weighted zero bound and exact arithmetic give Robin’s inequality above 5040. -/

import D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel
import D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeBandCertificates
import D5.S3.Arith.Robin.Finite.EffectiveRobinTangentRows
import D5.S3.Arith.Robin.ActualRobinInterval
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real MeasureTheory Finset
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
open D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel
open D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit

namespace D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveLargeBand

private lemma root_power_bounds {u : ℝ} (hu : Real.log 140 ≤ u) :
    Real.exp (-(1/6)*u) ≤ 44/100 ∧ Real.exp (-(3/10)*u) ≤ 23/100 ∧
    Real.exp (-(1/4)*u) ≤ 30/100 ∧ Real.exp (-(1/3)*u) ≤ 20/100 ∧
    Real.exp (-(2/5)*u) ≤ 14/100 := by
  have h1 : Real.exp (-(1:ℝ)*Real.log 140) = 1/140 := by rw [neg_one_mul,Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
  have h2 : Real.exp (-(2:ℝ)*Real.log 140) = 1/140^2 := by rw [neg_mul,Real.exp_neg,mul_comm,Real.exp_mul,Real.exp_log (by norm_num),Real.rpow_two]; norm_num
  have h3 : Real.exp (-(3:ℝ)*Real.log 140) = 1/140^3 := by rw [neg_mul,Real.exp_neg,mul_comm,Real.exp_mul,Real.exp_log (by norm_num),show (3:ℝ) = ((3:ℕ):ℝ) by norm_num,Real.rpow_natCast]; norm_num
  refine ⟨exp_power_bound (n:=6) hu (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_,
    exp_power_bound (n:=10) hu (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_,
    exp_power_bound (n:=4) hu (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_,
    exp_power_bound (n:=3) hu (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_,
    exp_power_bound (n:=5) hu (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_⟩
  · rw [show -(↑(6:ℕ):ℝ)*(1/6) = -1 by norm_num,h1]; norm_num
  · rw [show -(↑(10:ℕ):ℝ)*(3/10) = -3 by norm_num,h3]; norm_num
  · rw [show -(↑(4:ℕ):ℝ)*(1/4) = -1 by norm_num,h1]; norm_num
  · rw [show -(↑(3:ℕ):ℝ)*(1/3) = -1 by norm_num,h1]; norm_num
  · rw [show -(↑(5:ℕ):ℝ)*(2/5) = -2 by norm_num,h2]; norm_num

private lemma sqrt_exp (u : ℝ) : Real.sqrt (Real.exp u) = Real.exp (u/2) := by
  rw [Real.sqrt_eq_rpow,← Real.exp_mul]; congr 1; ring

private lemma normalized_P_two (hline : ∀ k : ℕ, (actualZero k).re = 1/2) {x : ℝ} (hx : 140 ≤ x) (hv : 49/10 ≤ Real.log x) :
    x*Real.sqrt x*Real.log x*P 2 x ≤ 128236/55125 := by
  let u := Real.log x
  have hx0 : 0 < x := by linarith
  have hu : 0 < u := by dsimp [u]; linarith
  have hlog : Real.log 140 ≤ u := Real.log_le_log (by norm_num) hx
  obtain ⟨h6,h310,h4,h3,h25⟩ := root_power_bounds hlog
  have hk {k : ℝ} (hk : 1 ≤ k) (hk5 : k ≤ 5) : Real.log 2 ≤ u/k := by
    refine (le_div_iff₀ (by linarith : 0 < k)).mpr ?_
    have h := mul_le_mul (show Real.log 2 ≤ 7/10 by linarith [Real.log_two_lt_d9]) hk5 (by linarith) (by norm_num)
    dsimp [u]; linarith
  have h2 := normalized_root_bound hline (k:=2) (by norm_num) (by norm_num) hu (hk (by norm_num) (by norm_num))
  have h3' := normalized_root_bound hline (k:=3) (by norm_num) (by norm_num) hu (hk (by norm_num) (by norm_num))
  have h5 := normalized_root_bound hline (k:=5) (by norm_num) (by norm_num) hu (hk (by norm_num) (by norm_num))
  norm_num at h2 h3' h5
  have hrw : Real.exp ((3/2)*u) = x*Real.sqrt x := by
    dsimp [u]
    rw [show (3/2:ℝ)*Real.log x = Real.log x + Real.log x/2 by ring, Real.exp_add,Real.exp_log hx0,← sqrt_exp,Real.exp_log hx0]
  rw [Real.exp_log hx0] at h2 h3' h5
  have hi : 1/u ≤ 10/49 := by
    apply (div_le_iff₀ hu).mpr
    dsimp [u]; linarith
  have c2 : 2+1/u ≤ 108/49 := by linarith
  simp only [div_eq_mul_inv,one_mul] at c2
  simp only [neg_mul] at h6 h310 h4 h3 h25
  have hscale : 0 ≤ Real.exp ((3/2)*u)*u := by positivity
  have hP := mul_le_mul_of_nonneg_left (P_upper_root (j:=2) (by norm_num) (by linarith : 1 < x)) hscale
  rw [hrw] at hP
  have hterm2 : Real.exp ((3/2)*u)*u*(B 2 (2:ℝ)⁻¹ u+(1/2)*J 4 (x^(2:ℝ)⁻¹)) ≤
      (4/3:ℝ)+2*(1/20)*(108/49)*(30/100) := by
    norm_num
    refine h2.trans ?_
    have h := mul_le_mul c2 h4 (Real.exp_nonneg _) (show 0 ≤ (108/49:ℝ) by norm_num)
    nlinarith only [h]
  have hterm3 : Real.exp ((3/2)*u)*u*(B 2 (3:ℝ)⁻¹ u+(1/3)*J 6 (x^(3:ℝ)⁻¹)) ≤
      (6/5:ℝ)*(44/100)+3*(1/20)*(108/49)*(20/100) := by
    norm_num
    refine h3'.trans ?_
    have h := mul_le_mul c2 h3 (Real.exp_nonneg _) (show 0 ≤ (108/49:ℝ) by norm_num)
    nlinarith only [h,h6]
  have hterm5 : Real.exp ((3/2)*u)*u*(B 2 (5:ℝ)⁻¹ u+(1/5)*J 10 (x^(5:ℝ)⁻¹)) ≤
      (10/9:ℝ)*(23/100)+5*(1/20)*(108/49)*(14/100) := by
    norm_num
    refine h5.trans ?_
    have h := mul_le_mul c2 h25 (Real.exp_nonneg _) (show 0 ≤ (108/49:ℝ) by norm_num)
    nlinarith only [h,h310]
  rw [hrw] at hterm2 hterm3 hterm5
  norm_num at hP hterm2 hterm3 hterm5
  linarith only [hP,hterm2,hterm3,hterm5]

private lemma J_two_normalized (hline : ∀ k : ℕ, (actualZero k).re = 1/2) {x : ℝ} (hx : 2 ≤ x) :
    -((1/20)*(2+1/Real.log x)/Real.sqrt x+2/x) ≤ x*Real.log x*J 2 x ∧
    x*Real.log x*J 2 x ≤ (1/20)*(2+1/Real.log x)/Real.sqrt x := by
  let u := Real.log x
  have hx0 : 0 < x := by linarith
  have hu : 0 < u := Real.log_pos (by linarith)
  have hlog : Real.log 2 ≤ u := Real.log_le_log (by norm_num) hx
  obtain ⟨hlo,hhi⟩ := J_log_bounds hline (j:=2) (by norm_num) (by norm_num) hlog
  have hscale : 0 ≤ x*u := by positivity
  have hm : x*u*(firstLiMass*Real.exp ((1/2-2)*u)*H 2 u) = firstLiMass*(2+1/u)/Real.sqrt x := by
    have hs : Real.exp ((1/2-2)*u) = (x*Real.sqrt x)⁻¹ := by
      rw [show (1/2-2:ℝ)*u = -(u+u/2) by ring,Real.exp_neg,Real.exp_add,← sqrt_exp,Real.exp_log hx0]
    rw [hs]; unfold H; field_simp [hx0.ne',hu.ne',(Real.sqrt_pos.mpr hx0).ne'] <;> ring
  have hc : x*u*(Real.log (2*Real.pi)*Real.exp (-2*u)/u) = Real.log (2*Real.pi)/x := by
    have he : Real.exp (-2*u) = (x^2)⁻¹ := by
      rw [show -2*u = -(u*2) by ring,Real.exp_neg,Real.exp_mul,Real.exp_log hx0,Real.rpow_two]
    rw [he]; field_simp [hx0.ne',hu.ne']
  rw [Real.exp_log hx0] at hlo hhi
  have h1 := mul_le_mul_of_nonneg_left hlo hscale
  rw [mul_sub,mul_neg,hm,hc] at h1
  have h2 := mul_le_mul_of_nonneg_left hhi hscale
  rw [hm] at h2
  have hM := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right firstLiMass_lt_twentieth.le
    (show 0 ≤ 2+1/u by positivity)) (Real.sqrt_nonneg x)
  have hC := div_le_div_of_nonneg_right log_two_pi_lt_two.le hx0.le
  exact ⟨by linarith only [h1,hM,hC], h2.trans hM⟩

private lemma B_two_normalized {x : ℝ} (hx : 1 < x) :
    2-1/Real.log x ≤ x*Real.log x*B 2 1 (Real.log x) ∧ x*Real.log x*B 2 1 (Real.log x) ≤ 2 := by
  have hx0 : 0 < x := by linarith
  have hu := Real.log_pos hx
  have hlo := mul_le_mul_of_nonneg_left (B_two_lower hu) (show 0 ≤ x*Real.log x by positivity)
  have hhi := mul_le_mul_of_nonneg_left (B_upper (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)<2) hu) (show 0 ≤ x*Real.log x by positivity)
  have he : Real.exp (-Real.log x) = x⁻¹ := by rw [Real.exp_neg,Real.exp_log hx0]
  rw [he] at hlo
  rw [show (1-2:ℝ) = -1 by norm_num,neg_one_mul,he] at hhi
  constructor
  · convert hlo using 1 <;> field_simp [hx0.ne',hu.ne'] <;> ring
  · convert hhi using 1 <;> field_simp [hx0.ne',hu.ne'] <;> norm_num

private lemma T_two_lower (hline : ∀ k : ℕ, (actualZero k).re = 1/2) {x : ℝ} (hx : 140 ≤ x) (hu : 49/10 ≤ Real.log x) :
    194203/1212750 ≤ x*Real.log x*T 2 x-Real.log 4 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hv : 0 < Real.log x := Real.log_pos hx1
  have hs : 11 ≤ Real.sqrt x := by
    have hsq := Real.sq_sqrt hx0.le
    nlinarith [Real.sqrt_nonneg x]
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hi : 1/Real.log x ≤ 10/49 := (div_le_iff₀ hv).mpr (by nlinarith)
  have hP := normalized_P_two hline hx hu
  have hP' : x*Real.log x*P 2 x ≤ (128236/55125)/Real.sqrt x := by
    apply (le_div_iff₀ hs0).2
    convert hP using 1 <;> ring
  have hPr := hP'.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0:ℝ)<11) hs)
  have hJ := (J_two_normalized hline (by linarith : 2 ≤ x)).1
  have hJ1 : (1/20)*(2+1/Real.log x)/Real.sqrt x ≤ (1/20)*(108/49)/11 := by
    apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ (1/20:ℝ)*(2+1/Real.log x)) (by norm_num : (0:ℝ)<11) hs).trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith only [hi]
  have hJ2 : 2/x ≤ 2/140 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have hB := (B_two_normalized hx1).1
  have hlog4 : Real.log 4 ≤ 7/5 := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
  rw [T_eq (by norm_num) hx1]
  rw [mul_sub,mul_add]
  linarith only [hPr,hJ,hJ1,hJ2,hB,hlog4,hi]

private lemma T_two_upper (hline : ∀ k : ℕ, (actualZero k).re = 1/2) {x : ℝ} (hx : 10000 ≤ x) (hu : 9 ≤ Real.log x) :
    D x*T 2 x ≤ 36019/1800000 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hv : 0 < Real.log x := by linarith
  have hs : 100 ≤ Real.sqrt x := by
    have hsq := Real.sq_sqrt hx0.le
    nlinarith [Real.sqrt_nonneg x]
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hi : 1/Real.log x ≤ 1/9 := (div_le_iff₀ hv).mpr (by nlinarith)
  have hJ := (J_two_normalized hline (by linarith : 2 ≤ x)).2
  have hJ1 : (1/20)*(2+1/Real.log x)/Real.sqrt x ≤ 19/18000 := by
    apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ (1/20:ℝ)*(2+1/Real.log x)) (by norm_num : (0:ℝ)<100) hs).trans
    norm_num
    have hi' : (Real.log x)⁻¹ ≤ 1/9 := by simpa [div_eq_mul_inv] using hi
    linarith only [hi']
  have hB := (B_two_normalized hx1).2
  have hP : 0 ≤ x*Real.log x*P 2 x := mul_nonneg (by positivity) (P_nonneg (by norm_num) hx1)
  have ht : x*Real.log x*T 2 x ≤ 2+19/18000 := by
    rw [T_eq (by norm_num) hx1,mul_sub,mul_add]
    linarith only [hB,hJ,hJ1,hP]
  have he : D x*T 2 x = (x*Real.log x*T 2 x)/Real.sqrt x := by
    unfold D
    field_simp [hs0.ne']
    rw [Real.sq_sqrt hx0.le]; ring
  rw [he]
  refine (div_le_div_of_nonneg_right ht hs0.le).trans ?_
  exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs).trans_eq (by norm_num)

private lemma cutoff_geometry {z : ℝ} (hz : 10000 ≤ z) :
    let a := Real.sqrt (2*z)
    140 ≤ a ∧ a ≤ z ∧ 9 ≤ Real.log z ∧ 49/10 ≤ Real.log a ∧ 126/97 ≤ D z/(a*Real.log a) := by
  dsimp only
  let a := Real.sqrt (2*z)
  have hz0 : 0 < z := by linarith
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a^2 = 2*z := Real.sq_sqrt (by positivity)
  have ha : 140 ≤ a := by nlinarith [Real.sqrt_nonneg (2*z)]
  have haz : a ≤ z := by nlinarith [mul_nonneg (show 0 ≤ z-2 by linarith) hz0.le]
  have hlogz : (92/10:ℝ) ≤ Real.log z := by
    have hlog := Real.log_le_log (by norm_num : (0:ℝ)<10000) hz
    rw [show (10000:ℝ) = (2*5)^4 by norm_num,Real.log_pow,Real.log_mul (by norm_num) (by norm_num)] at hlog
    norm_num at hlog
    linarith [Real.log_two_gt_d9,Real.log_five_gt_d9]
  have hloga : Real.log a = (Real.log z+Real.log 2)/2 := by
    dsimp [a]; rw [Real.log_sqrt (by positivity),Real.log_mul (by norm_num) hz0.ne']; ring
  have haLog : 49/10 ≤ Real.log a := by linarith [hloga,Real.log_two_gt_d9]
  refine ⟨ha,haz,by linarith,haLog,?_⟩
  have haeq : a = Real.sqrt 2*Real.sqrt z := Real.sqrt_mul (by norm_num) z
  have hs : 7/5 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  have hs0 := Real.sqrt_pos.mpr hz0
  have hu0 : 0 < Real.log z := by linarith
  have hal : 0 < Real.log a := by linarith
  have hratio : D z/(a*Real.log a) = Real.sqrt 2*Real.log z/(Real.log z+Real.log 2) := by
    rw [D,hloga,haeq]
    have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    field_simp [(Real.sqrt_pos.mpr hz0).ne',(Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne',show Real.log z+Real.log 2 ≠ 0 by linarith [Real.log_two_gt_d9]]
    nlinarith only [h2]
  rw [hratio]
  apply (le_div_iff₀ (by linarith [Real.log_two_gt_d9])).2
  have h := mul_le_mul_of_nonneg_right hs hu0.le
  linarith [Real.log_two_lt_d9]

private lemma primeBand_eq {z : ℝ} (hz : 0 ≤ z) :
    primeBand z = (Finset.Ioc ⌊Real.sqrt (2*z)⌋₊ ⌊z⌋₊).filter Nat.Prime := by
  ext p
  simp only [primeBand,mem_filter,Nat.mem_primesLE,Finset.mem_Ioc]
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2*z)
  have hf : ⌊Real.sqrt (2*z)⌋₊ < p ↔ Real.sqrt (2*z) < (p:ℝ) := by
    exact Nat.floor_lt (by positivity)
  rw [hf]
  have h : 2*z < (p:ℝ)^2 ↔ Real.sqrt (2*z) < (p:ℝ) := by
    conv_lhs => rw [← hsq]
    exact sq_lt_sq₀ (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  rw [h]
  tauto

private theorem normalized_square_band (hline : ∀ k : ℕ, (actualZero k).re = 1/2) {z : ℝ} (hz : 10000 ≤ z) :
    2527497289/13444200000 ≤ D z*∑ p ∈ primeBand z, 1/(p:ℝ)^2 := by
  let a := Real.sqrt (2*z)
  obtain ⟨ha,haz,huz,hua,hratio⟩ := cutoff_geometry hz
  change 140 ≤ a at ha
  change a ≤ z at haz
  change 49/10 ≤ Real.log a at hua
  change 126/97 ≤ D z/(a*Real.log a) at hratio
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hal := Real.log_pos ha1
  have hD : 0 ≤ D z := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have h := theta_abel_from_tails ha1 haz
  have ht := T_two_lower hline ha hua
  have htz := T_two_upper hline hz huz
  have hscaled := mul_le_mul_of_nonneg_left h hD
  have hlower : D z*T 2 a-D z*Real.log 4/(a*Real.log a) ≥ (126/97)*(194203/1212750) := by
    have h := mul_le_mul hratio ht (by norm_num) (div_nonneg hD (by positivity : 0 ≤ a*Real.log a))
    convert h using 1 <;> field_simp [ha0.ne',hal.ne'] <;> ring
  rw [primeBand_eq (by linarith : 0 ≤ z)]
  change _ ≤ D z*∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊z⌋₊).filter Nat.Prime, 1/(p:ℝ)^2
  have hre : D z*(T 2 a-T 2 z-Real.log 4/(a*Real.log a)) = (D z*T 2 a-D z*Real.log 4/(a*Real.log a))-D z*T 2 z := by ring
  rw [hre] at hscaled
  calc
    _ = (126/97)*(194203/1212750)-(36019/1800000:ℝ) := by norm_num
    _ ≤ _ := (sub_le_sub hlower htz).trans hscaled

/-- Strict analytic reserve for every real cutoff at least ten thousand. -/
theorem normalized_prime_band_large (hline : ∀ k : ℕ, (actualZero k).re = 1/2) {z : ℝ} (hz : 10000 ≤ z) :
    neededReserve z < normalizedPrimeBand z := by
  have hz0 : 0 < z := by linarith
  obtain ⟨ha,haz,huz,hua,hratio⟩ := cutoff_geometry hz
  have hu0 : 0 < Real.log z := by linarith
  have hs : 100 ≤ Real.sqrt z := by nlinarith [Real.sq_sqrt hz0.le,Real.sqrt_nonneg z]
  have hD : 0 ≤ D z := by unfold D; positivity
  have hp (p : ℕ) (hp : p ∈ primeBand z) : (49/100:ℝ)*(1/(p:ℝ)^2) ≤ primeBandWeight p := by
    rw [primeBand_eq hz0.le] at hp
    have hg := (Finset.mem_Ioc.mp (mem_filter.mp hp).1).1
    have hpa : Real.sqrt (2*z) < (p:ℝ) := (Nat.floor_lt (by positivity)).mp hg
    have hp140 : 140 < (p:ℝ) := ha.trans_lt hpa
    have hp0 : 0 < (p:ℝ) := by linarith
    have hp1 : 0 < (p:ℝ)-1 := by linarith
    unfold primeBandWeight
    apply (le_div_iff₀ (by positivity : 0 < 2*((p:ℝ)-1)*(p:ℝ)^2)).2
    have he : (49/100:ℝ)*(1/(p:ℝ)^2)*(2*((p:ℝ)-1)*(p:ℝ)^2) = (49/50)*((p:ℝ)-1) := by
      field_simp [hp0.ne']
      ring
    rw [he]
    linarith
  have hsum := Finset.sum_le_sum hp
  rw [← Finset.mul_sum] at hsum
  have hband := mul_le_mul_of_nonneg_left hsum hD
  have h := mul_le_mul_of_nonneg_left (normalized_square_band hline hz) (by norm_num : (0:ℝ)≤49/100)
  have hlow : (17692481023/192060000000:ℝ) ≤ normalizedPrimeBand z := by
    unfold normalizedPrimeBand
    linarith only [h,hband]
  have hi : 1/Real.log z ≤ 1/9 := (div_le_iff₀ hu0).mpr (by nlinarith)
  have hroot : 2/Real.sqrt z ≤ 2/100 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hc : (1+1/Real.log z)/(8*z*Real.sqrt z) ≤ (1+1/9)/(8*10000*100) := by
    refine (div_le_div_of_nonneg_right (add_le_add le_rfl hi) (by positivity : 0 ≤ 8*z*Real.sqrt z)).trans ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have h := mul_le_mul hz hs (by norm_num : (0:ℝ)≤100) hz0.le
    nlinarith
  unfold neededReserve
  linarith only [hi,hroot,hc,hlow]

/-- The complete effective RH-forward Robin inequality. -/
theorem effective_robin_margin (hline : ∀ k : ℕ, (actualZero k).re = 1/2) :
    ∀ n : ℕ, 5040 < n → 0 < D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin n := by
  apply robin_margin_of_effective_band
  · exact fun n hn hh => D5.S3.Arith.Robin.Finite.EffectiveRobinTangentRows.robin_margin_through_height_101 hn hh
  · intro z hz
    rcases le_total z 10000 with h | h
    · exact D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeBandCertificates.normalized_prime_band_finite hz h
    · exact normalized_prime_band_large hline h
  · intro z hz
    exact actual_weighted_tail_lower hline (by linarith)

/-- The classical inequality in its original integer divisor-sum form. -/
theorem effective_robin_of_line (hline : ∀ k : ℕ, (actualZero k).re = 1/2) :
    ∀ n : ℕ, 5040 < n → (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant*n*Real.log (Real.log n) := by
  intro n hn
  exact D5.S3.Arith.Robin.ActualRobinInterval.original_robin_of_margin (by omega)
    (effective_robin_margin hline n hn)

/-- The original Robin inequality for every integer above 5040 follows from RH. -/
theorem effective_robin_of_rh (hRH : RiemannHypothesis) :
    ∀ n : ℕ, 5040 < n → (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant*n*Real.log (Real.log n) :=
  effective_robin_of_line
    (D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope.on_line hRH)

end D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveLargeBand
