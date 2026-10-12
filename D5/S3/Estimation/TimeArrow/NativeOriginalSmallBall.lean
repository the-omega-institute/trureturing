/- GID: D5/S3/Estimation/TimeArrow/NativeOriginalSmallBall
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeOriginalSmallBall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original growth supplies shared-root arithmetic bounds on native environment values. -/

import D5.S3.Estimation.TimeArrow.NativeGrowthRounding
import D5.S3.Estimation.TimeArrow.OriginalScoreWindow

open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeGrowthRounding
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeAnchoredSmallBall
open D5.S3.Estimation.TimeArrow.OriginalScoreWindow
open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.NativeOriginalSmallBall
noncomputable section

/-- The finite numerator retains all original decimal digits through the current index. -/
def decimalNumerator (n : ℕ) : ℕ := ∑ j ∈ range (n+1),10^(decimalExponent n-decimalExponent j)

/-- The fixed original amplitude is characterized by this complete decimal series. -/
def decimalAlpha : ℝ := ∑' j : ℕ, 1/(denominator j : ℝ)

/-- The unused decimal digits form the positive rational-approximation error. -/
def decimalTail (n : ℕ) : ℝ := ∑' j : ℕ,1/(denominator (n+1+j) : ℝ)

private theorem exponent_strictMono : StrictMono decimalExponent := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := Nat.mul_le_pow (a := 10) (by decide : 10 ≠ 1) (5*decimalExponent n)
  have hn := decimalExponent_index n
  change decimalExponent n < 10^(5*decimalExponent n)
  omega

private theorem decimal_summable : Summable (fun j : ℕ => 1/(denominator j : ℝ)) := by
  simp only [denominator,Nat.cast_pow,Nat.cast_ofNat]
  exact summable_one_div_pow_of_le (by norm_num : (1 : ℝ) < 10)
    (fun n => (Nat.le_succ n).trans (decimalExponent_index n))

private theorem decimal_tail_bounds (n : ℕ) :
    0 < decimalTail n ∧ decimalTail n ≤ 2/(denominator (n+1) : ℝ) := by
  have hs : Summable (fun j : ℕ => 1/(denominator (n+1+j) : ℝ)) := by
    convert! (summable_nat_add_iff (n+1)).2 decimal_summable using 1
    funext j
    rw [Nat.add_comm]
  have hn (j : ℕ) : 0 ≤ 1/(denominator (n+1+j) : ℝ) := by unfold denominator; positivity
  have hfirst : 0 < 1/(denominator (n+1+0) : ℝ) := by unfold denominator; positivity
  refine ⟨hfirst.trans_le (hs.le_tsum 0 (fun j _ => hn j)),?_⟩
  let B := fun j : ℕ => (1/(denominator (n+1) : ℝ))*(1/10 : ℝ)^j
  have hB : Summable B := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/10)
    (by norm_num : (1/10 : ℝ) < 1)).mul_left _
  have hbound (j : ℕ) : 1/(denominator (n+1+j) : ℝ) ≤ B j := by
    have he : decimalExponent (n+1)+j ≤ decimalExponent (n+1+j) := by
      simpa only [Nat.add_comm] using exponent_strictMono.add_le_nat j (n+1)
    have hh : (10 : ℝ)^(decimalExponent (n+1)+j) ≤ (10 : ℝ)^decimalExponent (n+1+j) :=
      pow_le_pow_right₀ (by norm_num) he
    have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 10^(decimalExponent (n+1)+j)) hh
    simpa only [B,denominator,Nat.cast_pow,Nat.cast_ofNat,pow_add,one_div_mul_one_div,one_div_pow] using hi
  have ht := hs.tsum_le_tsum hbound hB
  have hsum : (∑' j,B j) = (1/(denominator (n+1) : ℝ))*(1-(1/10 : ℝ))⁻¹ := by
    rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/10) (by norm_num : (1/10 : ℝ) < 1)]
  dsimp only [decimalTail]
  apply ht.trans
  rw [hsum]
  have hh : (1-(1/10 : ℝ))⁻¹ ≤ 2 := by norm_num
  convert mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1/(denominator (n+1) : ℝ)) using 1 <;> ring

private theorem decimal_partial_sum (n : ℕ) :
    (decimalNumerator n : ℝ)/(denominator n : ℝ) = ∑ j ∈ range (n+1),1/(denominator j : ℝ) := by
  unfold decimalNumerator
  push_cast
  rw [sum_div]
  apply sum_congr rfl
  intro j hj
  have he : decimalExponent j ≤ decimalExponent n := exponent_strictMono.monotone (by
    have hh := mem_range.mp hj; omega)
  have hpow : (10 : ℝ)^decimalExponent n =
      (10 : ℝ)^(decimalExponent n-decimalExponent j)*(10 : ℝ)^decimalExponent j := by
    rw [←pow_add,Nat.sub_add_cancel he]
  unfold denominator
  push_cast
  rw [hpow]
  field_simp

private theorem decimal_series_decomposition (n : ℕ) :
    decimalAlpha = (decimalNumerator n : ℝ)/(denominator n : ℝ)+decimalTail n := by
  rw [decimal_partial_sum]
  exact (decimal_summable.sum_add_tsum_nat_add (n+1)).symm.trans (by
    congr 1
    apply tsum_congr
    intro j
    rw [Nat.add_comm])


private theorem decimal_alpha_lt_one : decimalAlpha < 1 := by
  have hg : Summable (fun j : ℕ => (1/10 : ℝ)^(j+1)) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/10)
      (by norm_num : (1/10 : ℝ) < 1)).comp_injective Nat.succ_injective
  have hbound (j : ℕ) : 1/(denominator j : ℝ) ≤ (1/10 : ℝ)^(j+1) := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (decimalExponent_index j)
    have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 10^(j+1)) hh
    simpa only [denominator,Nat.cast_pow,Nat.cast_ofNat,one_div_pow] using hi
  have ht := decimal_summable.tsum_le_tsum hbound hg
  have hs : (∑' j : ℕ,(1/10 : ℝ)^(j+1)) = (1/10 : ℝ)*(1-1/10)⁻¹ := by
    simp_rw [pow_succ']
    rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/10)
      (by norm_num : (1/10 : ℝ) < 1)]
  exact ht.trans_lt (by rw [hs]; norm_num)

private theorem decimal_numerator_lt (n : ℕ) : decimalNumerator n < denominator n := by
  have h := decimal_series_decomposition n
  have ht := (decimal_tail_bounds n).1
  have hQ : (0 : ℝ) < denominator n := by unfold denominator; positivity
  have hh : (decimalNumerator n : ℝ)/(denominator n : ℝ) < 1 := by
    linarith only [decimal_alpha_lt_one,h,ht]
  exact_mod_cast (div_lt_one hQ).mp hh

private theorem denominator_atTop : Tendsto (fun n => (denominator n : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop_mono _ (tendsto_atTop_mono
    (fun n => (Nat.le_succ n).trans (decimalExponent_index n)) tendsto_id)
  intro n
  exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 10)).trans
    (Nat.mul_le_pow (a := 10) (by decide : 10 ≠ 1) (decimalExponent n))

private theorem decimal_tail_exponential (H : ℝ) :
    ∀ᶠ n in atTop, decimalTail n ≤ Real.exp (-H*(scale n : ℝ)) := by
  have hlog : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp denominator_atTop).eventually
    (eventually_ge_atTop ((H+1)/Real.log 10)),
    scale_tendsto.eventually (eventually_ge_atTop 1)] with n hQ hL
  have hnext : decimalExponent (n+1) = denominator n^5 := by
    simp only [decimalExponent,denominator,←pow_mul,Nat.mul_comm]
  have he : (denominator (n+1) : ℝ) =
      Real.exp (Real.log 10*(denominator n : ℝ)^5) := by
    rw [←Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
    rw [show (denominator n : ℝ)^5 = (decimalExponent (n+1) : ℝ) by rw [hnext]; push_cast; rfl]
    rw [Real.rpow_natCast]
    simp [denominator]
  have hexp : 2 ≤ Real.exp (scale n : ℝ) := by
    have hh := Real.add_one_le_exp (scale n : ℝ)
    linarith only [hh,hL]
  have hpower : (H+1)*(scale n : ℝ) ≤ Real.log 10*(denominator n : ℝ)^5 := by
    have hh := (div_le_iff₀ hlog).mp hQ
    have hm := mul_le_mul_of_nonneg_right hh
      (by positivity : 0 ≤ (denominator n : ℝ)^3)
    convert hm using 1 <;> first | rfl | (try dsimp only [Function.comp_apply,scale]; push_cast; ring)
  apply (decimal_tail_bounds n).2.trans
  rw [he,div_eq_mul_inv,←Real.exp_neg]
  calc
    _ ≤ Real.exp (scale n : ℝ)*Real.exp (-(Real.log 10*(denominator n : ℝ)^5)) := by gcongr
    _ = Real.exp ((scale n : ℝ)-Real.log 10*(denominator n : ℝ)^5) := by rw [←Real.exp_add] <;> congr 1 <;> ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hpower])

private theorem compensation_signal_zero (r β : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 1/2 < β) (hβ1 : β < 1) :
    Tendsto (fun n => compensation (population r β (scale n))
      (signalSize r β (scale n)) r*(scale n : ℝ)*signalSize r β (scale n)) atTop (𝓝 0) := by
  have hφ := (information_rate_bounds r hr hr1).1
  have hβ0 : 0 < β := by linarith only [hβ]
  let C := Real.log ((1+r)/(1-r))
  let D := 2*phi r-phi r/β
  have hD : 0 < D := by
    dsimp [D]
    have hh : phi r/β < 2*phi r := (div_lt_iff₀ hβ0).mpr (by nlinarith only [hφ,hβ])
    linarith only [hh]
  have hz := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) D hD).comp
    scale_tendsto).const_mul (4*r*Real.exp (2*C))
  simp only [Function.comp_apply,Real.rpow_one,mul_zero] at hz
  refine squeeze_zero' (Eventually.of_forall fun n => by unfold compensation; positivity) ?_ hz
  have hB : 0 < phi r/β-phi r := by
    apply sub_pos.mpr
    exact (lt_div_iff₀ hβ0).mpr (by nlinarith only [hφ,hβ1])
  have hlarge := (Real.tendsto_exp_atTop.comp (scale_tendsto.const_mul_atTop hB)).eventually
    (eventually_ge_atTop 4)
  filter_upwards [hlarge,(original_density_scales r β hr hr1 0).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    original_native_scale_conditions r β 1 1 1 hr hr1 hβ0 hβ1 (by norm_num)] with n hlarge hd hn
  simp only [pow_zero,one_mul] at hd
  obtain ⟨_,hq,hqm,_,_,_,_,_,_,_,_,_,_⟩ := hn
  have hM : (0 : ℝ) < population r β (scale n) := by unfold population; positivity
  have hq0 : (0 : ℝ) < signalSize r β (scale n) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have he := compensation_density_bound (population r β (scale n)) (signalSize r β (scale n))
    r hr.le hqm hd.le
  have hqhi := (signal_exponential_bounds r β (scale n) hr.le hr1 hφ.le hβ0 hlarge).2
  have hMlo := (population_exponential_bounds r β (scale n) hφ.le hβ0).1
  calc
    _ ≤ 2*r*((signalSize r β (scale n) : ℝ)/population r β (scale n))*
        (scale n : ℝ)*signalSize r β (scale n) := by gcongr
    _ = 2*r*(scale n : ℝ)*(signalSize r β (scale n) : ℝ)^2/population r β (scale n) := by ring
    _ ≤ 2*r*(scale n : ℝ)*Real.exp ((phi r/β-phi r)*(scale n : ℝ)+C)^2/
        (Real.exp (phi r/β*(scale n : ℝ))/2) := by gcongr
    _ = 4*r*Real.exp (2*C)*((scale n : ℝ)*Real.exp (-D*(scale n : ℝ))) := by
      rw [←Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [div_div_eq_mul_div]
      rw [show 2*r*(scale n : ℝ)*Real.exp (2*((phi r/β-phi r)*(scale n : ℝ)+C))*2/
        Real.exp (phi r/β*(scale n : ℝ)) = 4*r*(scale n : ℝ)*
          (Real.exp (2*((phi r/β-phi r)*(scale n : ℝ)+C))/Real.exp (phi r/β*(scale n : ℝ))) by ring,
        ←Real.exp_sub]
      dsimp only [D,C]
      rw [show 2*((phi r/β-phi r)*(scale n : ℝ)+Real.log ((1+r)/(1-r)))-
        phi r/β*(scale n : ℝ) = 2*Real.log ((1+r)/(1-r))+
          -(2*phi r-phi r/β)*(scale n : ℝ) by ring,Real.exp_add]
      ring

private theorem decimal_tail_signal_zero (r β : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n => decimalTail n*(scale n : ℝ)*signalSize r β (scale n)) atTop (𝓝 0) := by
  let B := phi r/β-phi r
  let C := Real.log ((1+r)/(1-r))
  have hz := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) 1 (by norm_num)).comp
    scale_tendsto).const_mul (Real.exp C)
  simp only [Function.comp_apply,Real.rpow_one,neg_mul,one_mul,mul_zero] at hz
  refine squeeze_zero' (Eventually.of_forall fun n => by
    exact mul_nonneg (mul_nonneg (decimal_tail_bounds n).1.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) ?_ hz
  have hφ := (information_rate_bounds r hr hr1).1
  have hB : 0 < phi r/β-phi r := by
    apply sub_pos.mpr
    exact (lt_div_iff₀ hβ).mpr (by nlinarith only [hφ,hβ1])
  have hlarge := (Real.tendsto_exp_atTop.comp (scale_tendsto.const_mul_atTop hB)).eventually
    (eventually_ge_atTop 4)
  filter_upwards [decimal_tail_exponential (B+1),hlarge] with n hn hlarge
  have hqhi := (signal_exponential_bounds r β (scale n) hr.le hr1
    (information_rate_bounds r hr hr1).1.le hβ hlarge).2
  calc
    _ ≤ Real.exp (-(B+1)*(scale n : ℝ))*(scale n : ℝ)*
        Real.exp (B*(scale n : ℝ)+C) := by gcongr
    _ = Real.exp C*((scale n : ℝ)*Real.exp (-(scale n : ℝ))) := by
      rw [show Real.exp (-(B+1)*(scale n : ℝ))*(scale n : ℝ)*
        Real.exp (B*(scale n : ℝ)+C) = (scale n : ℝ)*(Real.exp (-(B+1)*(scale n : ℝ))*
          Real.exp (B*(scale n : ℝ)+C)) by ring,←Real.exp_add]
      rw [show -(B+1)*(scale n : ℝ)+(B*(scale n : ℝ)+C) = C+-(scale n : ℝ) by ring,Real.exp_add]
      ring

set_option maxHeartbeats 1000000 in
/-- The original rational approximants and original uncorrected window
satisfy all compensated-grid inputs along the original population sequence. -/
private theorem original_window_sequence_conditions (r β : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 1/2 < β) (hβ1 : β < 1)
    (hα : Real.log (1+r)/(-Real.log (1-r)) = decimalAlpha) :
    ∀ᶠ n in atTop,
      let lam := scale n
      let M := population r β lam
      let q := signalSize r β lam
      let k := centralPositive r lam
      let l := centralNegative r lam
      let width := Real.sqrt ((lam : ℝ)/q)
      k+l+2 ≤ 8*lam ∧ decimalNumerator n < denominator n ∧ 0 < width ∧
      0 < decimalTail n ∧
      Real.log (1+r) = (-Real.log (1-r))*
        ((decimalNumerator n : ℝ)/denominator n+decimalTail n) ∧
      (-Real.log (1-r))*decimalTail n*(8*lam+k+l)+2*compensation M q r*(8*lam)+
        |(k : ℝ)*Real.log (1+r)+l*Real.log (1-r)-Real.log ((M : ℝ)/q)| ≤ width/2 ∧
      (denominator n : ℝ)*width ≤ (-Real.log (1-r))/4 := by
  let h := -Real.log (1-r)
  have hh : 0 < h := neg_pos.mpr (Real.log_neg (by linarith only [hr1]) (by linarith only [hr]))
  have hβ0 : 0 < β := by linarith only [hβ]
  filter_upwards [(decimal_tail_signal_zero r β hr hr1 hβ0 hβ1).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1/(9*h))),
    (compensation_signal_zero r β hr hr1 hβ hβ1).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/16)),
    ((original_polynomial_scales r β hr hr1 hβ0 hβ1 2).1).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < (h/4)^2)),
    original_native_scale_conditions r β 1 1 1 hr hr1 hβ0 hβ1 (by norm_num),
    scale_tendsto.eventually (eventually_ge_atTop 64)] with n ht he hg hn hlam
  dsimp only
  let lam := scale n
  let M := population r β lam
  let q := signalSize r β lam
  let k := centralPositive r lam
  let l := centralNegative r lam
  let w := Real.sqrt ((lam : ℝ)/q)
  obtain ⟨_,hq,hqm,_,_,_,_,_,_,_,_,_,_⟩ := hn
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hlam0 : (0 : ℝ) < lam := by dsimp [lam]; linarith only [hlam]
  have hM0 : (0 : ℝ) < M := by unfold M population; positivity
  have hkl : k+l=lam := by
    have hk := (central_rounding r lam hr.le hr1.le).1
    dsimp only [k,l,centralNegative]
    omega
  have hw : 0 < w := Real.sqrt_pos.mpr (div_pos hlam0 hq0)
  have hwsq : w^2=(lam : ℝ)/q := Real.sq_sqrt (div_nonneg hlam0.le hq0.le)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hwq : 8 ≤ w*q := by
    have hs := (eq_div_iff hq0.ne').mp hwsq
    have hlam64 : (64 : ℝ) ≤ lam := hlam
    have hprod := mul_le_mul_of_nonneg_left hq1 hlam0.le
    nlinarith only [hs,hprod,hlam64,hw.le,hq0.le]
  have hlog := signal_log_rounding r β lam (lt_of_lt_of_le Nat.zero_lt_one hq)
  dsimp only at hlog
  have hraw : |(k : ℝ)*Real.log (1+r)+l*Real.log (1-r)-Real.log ((M : ℝ)/q)| ≤ 1/q := by
    rw [Real.log_div hM0.ne' hq0.ne']
    change |center r lam-(Real.log (M : ℝ)-Real.log (q : ℝ))| ≤ _
    have hid := hlog.2.2
    have hx : center r lam-(Real.log (M : ℝ)-Real.log (q : ℝ)) =
        -Real.log ((population r β lam : ℝ)*Real.exp (-center r lam)/q) := by linarith only [hid]
    rw [hx,abs_neg,abs_of_nonneg hlog.1]
    exact hlog.2.1
  have ht1 : h*decimalTail n*(8*lam+k+l) ≤ 1/q := by
    have hcast : (k : ℝ)+l=lam := by exact_mod_cast hkl
    apply (le_div_iff₀ hq0).mpr
    have hb := (lt_div_iff₀ (by positivity : 0 < 9*h)).mp ht
    rw [show 8*(lam : ℝ)+k+l=9*(lam : ℝ) by linarith only [hcast]]
    convert hb.le using 1 <;> ring
  have he1 : 2*compensation M q r*(8*lam) ≤ 1/q := by
    apply (le_div_iff₀ hq0).mpr
    dsimp only [M,q,lam] at *
    nlinarith only [he]
  have hQ : (0 : ℝ) < denominator n := by unfold denominator; positivity
  have hQ1 : (1 : ℝ) ≤ denominator n := by unfold denominator; exact_mod_cast (show 1 ≤ 10^decimalExponent n from one_le_pow₀ (by norm_num))
  have hlam_eq : (lam : ℝ)=(denominator n : ℝ)^3 := by simp [lam,scale]
  have hgrid : (denominator n : ℝ)*w ≤ h/4 := by
    have ha := mul_le_mul_of_nonneg_left hQ1 (sq_nonneg (denominator n : ℝ))
    have ha' : (denominator n : ℝ)^2 ≤ lam := by
      rw [hlam_eq]
      nlinarith only [ha]
    have hp := mul_le_mul_of_nonneg_right ha' hlam0.le
    have hsq : ((denominator n : ℝ)*w)^2 ≤ (lam : ℝ)^2/q := by
      rw [mul_pow,hwsq,←mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hq0.le
      nlinarith only [hp]
    have hgg : (lam : ℝ)^2/q < (h/4)^2 := hg
    nlinarith only [hsq,hgg,hh,hw.le,hQ.le]
  have hH : k+l+2 ≤ 8*lam := by
    have hn : 4 ≤ lam := by exact_mod_cast ((by norm_num : (4 : ℝ) ≤ 64).trans hlam)
    omega
  refine ⟨hH,decimal_numerator_lt n,hw,(decimal_tail_bounds n).1,?_,?_,hgrid⟩
  · rw [←decimal_series_decomposition]
    simpa only [h,mul_comm] using (div_eq_iff hh.ne').mp hα
  · have hsum := add_le_add (add_le_add ht1 he1) hraw
    have hh' := (div_le_iff₀ hq0).mpr hwq
    dsimp only [w,h,k,l,M,q,lam] at *
    simp only [div_eq_mul_inv] at hsum hh' ⊢
    have hi : 0 ≤ (signalSize r β (scale n) : ℝ)⁻¹ := inv_nonneg.mpr hq0.le
    linarith only [hsum,hh',hi]


/-- Complete calibration exists for every full observation, including empty rectangles. -/
private theorem complete_root {M q s : ℕ} (r : ℝ) (e : Experiment)
    (o : Obs M s e) (hq : 1 ≤ q) (hqm : q < M) :
    ∃ x : ℝ, (∑ i : Fin M, Real.sigmoid (x+score q r e o i-
      Real.log (((M-q : ℕ) : ℝ)/q))) = q := by
  obtain ⟨x,hx⟩ := exists_calibration_root
    (fun i : Fin M => score q r e o i-Real.log (((M-q : ℕ) : ℝ)/q))
    0 0 0 0 0 q 0 (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq))
    (by simpa using (show (q : ℝ) < M by exact_mod_cast hqm))
  refine ⟨x,?_⟩
  simpa [calibratedMean,cellCounts,Fin.sum_univ_four,add_sub_assoc] using hx

/-- The same returned feedback constants satisfy every scalar-engine size input
throughout the original rectangle comparison interval. -/
private theorem original_engine_scales (r β v a γ c η V0 cN CN : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hv : 0 < v) (ha : 0 < a) (hγ : 0 < γ) (hc : 0 < c)
    (hη : 0 < η) (hcN : 0 < cN) :
    ∀ᶠ n in atTop, ∀ N : ℕ,
      cN*(signalSize r β (scale n) : ℝ)/scale n ≤ N →
      (N : ℝ) ≤ CN*(signalSize r β (scale n) : ℝ)/scale n →
      1 < N ∧ max 4 (32/(a*v)) ≤ Real.sqrt N ∧
      (N : ℝ)/signalSize r β (scale n) ≤ v/2 ∧
      (N : ℝ)/signalSize r β (scale n) ≤ v*Real.log 2/8 ∧
      a*((N : ℝ)/signalSize r β (scale n)) < η ∧
      c*((N : ℝ)/signalSize r β (scale n)) ≤ 1 ∧
      V0 ≤ v*(signalSize r β (scale n) : ℝ)/4 ∧
      1 ≤ γ*(c*((N : ℝ)/signalSize r β (scale n)))*Real.sqrt N := by
  let δ := min (v/2) (min (v*Real.log 2/8) (min (η/(2*a)) (min (1/c) (γ*c))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδv : δ ≤ v/2 := min_le_left _ _
  have hδlog : δ ≤ v*Real.log 2/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ ≤ η/(2*a) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδc : δ ≤ 1/c := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδγ : δ ≤ γ*c := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  filter_upwards [original_rectangle_feedback_scales r β cN CN δ
    (max 4 (32/(a*v))) hr hr1 hβ hβ1 hcN hδ,
    ((original_populations_tendsto r β hr hr1 hβ hβ1).1).eventually
      (eventually_ge_atTop (max 1 (4*V0/v)))] with n hn hq
  intro N hlo hhi
  obtain ⟨hlarge,hsize,hinv⟩ := hn N hlo hhi
  have hN0 : (0 : ℝ) < N := by
    have hh := (le_max_left 4 (32/(a*v))).trans hlarge
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hq0 : (0 : ℝ) < signalSize r β (scale n) :=
    (by norm_num : (0 : ℝ) < 1).trans_le ((le_max_left _ _).trans hq)
  have hN : 1 < N := by
    have hh := (le_max_left 4 (32/(a*v))).trans hlarge
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    have hh' : (1 : ℝ) < N := by nlinarith [Real.sqrt_nonneg (N : ℝ)]
    exact_mod_cast hh'
  refine ⟨hN,hlarge,hsize.trans hδv,hsize.trans hδlog,?_,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left (hsize.trans hδa) ha.le
    have he : a*(η/(2*a)) = η/2 := by field_simp <;> ring
    rw [he] at hh
    linarith only [hh,hη]
  · exact (mul_le_mul_of_nonneg_left (hsize.trans hδc) hc.le).trans_eq
      (by field_simp)
  · have hh := (div_le_iff₀ hv).mp ((le_max_right _ _).trans hq)
    nlinarith only [hh]
  · have hh := (div_le_iff₀ (mul_pos hN0 (Real.sqrt_pos.mpr hN0))).mp
      (hinv.trans hδγ)
    rw [show γ*(c*((N : ℝ)/signalSize r β (scale n)))*Real.sqrt N =
      (γ*c*((N : ℝ)*Real.sqrt N))/signalSize r β (scale n) by ring]
    apply (le_div_iff₀ hq0).mpr
    simpa only [one_mul] using hh


open scoped Classical in
set_option maxHeartbeats 4000000 in
/-- The original growth and floor sequence supplies the full native arithmetic
estimate on environment values with a uniform vanishing failure budget. The
conditional law is the original minimal readout, with no success flag added. -/
theorem original_native_environment_small_ball (r β : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hβ : 1/2 < β) (hβ1 : β < 1)
    (hα : Real.log (1+r)/(-Real.log (1-r)) = decimalAlpha) :
    ∃ cN CN c : ℝ, 0 < cN ∧ 0 < CN ∧ 0 < c ∧
    ∀ ell : ℤ, ell ≠ 0 → ∃ (Cell : ℝ) (budget : ℕ → ℝ), 0 < Cell ∧
      Tendsto budget atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      let lam := scale n
      let M := population r β lam
      let q := signalSize r β lam
      let k := centralPositive r lam
      let l := centralNegative r lam
      ∀ (S : Support M q) (e : Experiment),
      (∑ o : Obs M (2*M*lam) e,
        let N : ℝ := (nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card
        let s0 := c*(N/q)
        if ¬(cN*(q : ℝ)/lam ≤ N ∧ N ≤ CN*(q : ℝ)/lam ∧
            ∀ L τ : ℝ, 0 < L → 0 ≤ τ →
            (∑ y : Obs M (2*M*lam) e,
              if fullRectangleReadout S e k l y = fullRectangleReadout S e k l o ∧
                (∃ b : ℤ, |(ell : ℝ)*(1/2-
                  originalGroupPosteriorMean q r (Real.log ((M : ℝ)/q)) (Real.sqrt ((lam : ℝ)/q))
                    ((k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
                      l*Real.log ((1-r)/(1+compensation M q r))) e y)-b| ≤ τ)
              then probability r e S y else 0)/
              (∑ y : Obs M (2*M*lam) e,
                if fullRectangleReadout S e k l y = fullRectangleReadout S e k l o
                then probability r e S y else 0) ≤
              Cell*(L*(s0+τ)+(1+τ/s0)/Real.sqrt N+L^(-2 : ℤ)))
        then probability r e S o else 0) ≤ budget n := by
  classical
  have hβ0 : 0 < β := by linarith only [hβ]
  obtain ⟨cN,CN,bgBudget,hcN,hCN,hbgBudget,hgeometry⟩ :=
    original_rectangle_scale_budget r β hr hr1 hβ0 hβ1
  obtain ⟨vr,A,hvr,hA,hroots⟩ := original_complete_root_budget r β hr hr1 hβ hβ1
  let v := vr/4
  have hv : 0 < v := by dsimp [v]; positivity
  obtain ⟨Cpost,V0,hCpost,hV0,hsmall⟩ := original_full_env_small_ball
  obtain ⟨a,γ,η,c,Cfb,ha,hγ,hγsmall,hη,hc,hCfb,hsmall⟩ := hsmall r v hr hr1 hv
  let κ₀ := a*cN/4
  have hκ₀ : 0 < κ₀ := by dsimp [κ₀]; positivity
  obtain ⟨hrootBudget,hroots⟩ := hroots κ₀ hκ₀
  refine ⟨cN,CN,c,hcN,hCN,hc,?_⟩
  intro ell hell
  obtain ⟨Cell,hCell,hsmall⟩ := hsmall ell hell
  let budget := fun n => 16/15*(bgBudget n+rootFailureBudget r β vr κ₀ A n)
  have hbudget : Tendsto budget atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (hbgBudget.add hrootBudget).const_mul (16/15)
  refine ⟨Cell,budget,hCell,hbudget,?_⟩
  have hcomp := original_compensation_scales r β hr hr1 0
  simp only [pow_zero,one_mul] at hcomp
  filter_upwards [original_window_sequence_conditions r β hr hr1 hβ hβ1 hα,hgeometry,hroots,
    original_native_scale_conditions r β 1 1 1 hr hr1 hβ0 hβ1 (by norm_num),
    original_engine_scales r β v a γ c η V0 cN CN hr hr1 hβ0 hβ1 hv ha hγ hc hη hcN,
    hcomp.eventually (gt_mem_nhds (lt_min hη (by norm_num : (0 : ℝ) < 1/2))),
    scale_tendsto.eventually (eventually_ge_atTop 1)] with n hwindow hgeometry hroots hn hengine hcomp hlam
  dsimp only
  let lam := scale n
  let M := population r β lam
  let q := signalSize r β lam
  let k := centralPositive r lam
  let l := centralNegative r lam
  obtain ⟨_,hq,hqm,hlam4,_,_,_,_,_,_,_,_,_⟩ := hn
  have hε : 0 ≤ compensation M q r := by dsimp [M,q,compensation]; positivity
  have hεη : |compensation M q r| < η := by
    rw [abs_of_nonneg hε]
    exact hcomp.trans_le (min_le_left _ _)
  have hεhalf : compensation M q r ≤ 1/2 := (hcomp.trans_le (min_le_right _ _)).le
  have hε1 : compensation M q r < 1 := by
    have hh := hcomp.trans_le (min_le_right _ _)
    linarith only [hh]
  intro S e
  letI : Fintype (Sites (2*M*lam) e) := by cases e <;> unfold Sites <;> infer_instance
  have hx (o : Obs M (2*M*lam) e) := complete_root r e o hq hqm
  let x : Obs M (2*M*lam) e → ℝ := fun o => (hx o).choose
  have hxroot (o : Obs M (2*M*lam) e) := (hx o).choose_spec
  let D := fun o : Obs M (2*M*lam) e => ∑ i : Fin M,
    Real.sigmoid (x o+score q r e o i-Real.log (((M-q : ℕ) : ℝ)/q))*
      (1-Real.sigmoid (x o+score q r e o i-Real.log (((M-q : ℕ) : ℝ)/q)))
  let Geom := fun o : Obs M (2*M*lam) e =>
    let V := nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)
    let R := (V.filter fun i => count e o i.val 1 = k).card
    let U := (V.filter fun i => count e o i.val (-1) = l).card
    cN*(q : ℝ)/lam ≤ V.card ∧ (V.card : ℝ) ≤ CN*(q : ℝ)/lam ∧
      3/8*(V.card : ℝ) ≤ R ∧ (R : ℝ) ≤ 5/8*V.card ∧
      3/8*(V.card : ℝ) ≤ U ∧ (U : ℝ) ≤ 5/8*V.card ∧
      ((nativeCalibrationCells (⟨univ,by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ)
        ≤ 5/12*V.card
  let Root := fun o : Obs M (2*M*lam) e =>
    |x o+cellLogit r β lam| ≤ κ₀/(lam : ℝ) ∧ v*(q : ℝ) ≤ D o ∧ D o ≤ q ∧
      ∀ i : Fin M, count e o i 1+count e o i (-1) ≤ 8*lam
  let G := fun o => Geom o ∧ Root o
  have hgeo : (∑ o : Obs M (2*M*lam) e,if ¬Geom o then probability r e S o else 0) ≤ bgBudget n := by
    simpa only [Geom,lam,M,q,k,l] using hgeometry S e
  have hroot : (∑ o : Obs M (2*M*lam) e,if ¬Root o then probability r e S o else 0) ≤
      rootFailureBudget r β vr κ₀ A n := by
    have hh := hroots S e x hxroot
    dsimp only at hh
    simpa only [Root,D,v,not_and_or,not_le,not_forall,div_mul_eq_mul_div,lam,M,q] using hh
  have hp := (finite_support_bayes (s := 2*M*lam) hq hqm hr hr1 hε hε1 e).2.1.1 S
  have hG : (∑ o : Obs M (2*M*lam) e,if ¬G o then probability r e S o else 0) ≤
      bgBudget n+rootFailureBudget r β vr κ₀ A n := by
    apply le_trans _ (add_le_add hgeo hroot)
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro o _
    by_cases hg : Geom o <;> by_cases hx : Root o <;>
      simp only [G,hg,hx,true_and,false_and,not_true_eq_false,not_false_eq_true,if_true,if_false] <;>
      linarith only [hp o]
  have hsize (o : Obs M (2*M*lam) e) (ho : G o) :
      1 < (nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card :=
    (hengine _ ho.1.1 ho.1.2.1).1
  have hanchors := full_native_environment_anchor_budget S r e hq hqm hr hr1 hε hε1 k l G hsize
  have hpay : (16/15)*(∑ y : Obs M (2*M*lam) e,
      if ¬G y then probability r e S y else 0) ≤
      (16/15)*(bgBudget n+rootFailureBudget r β vr κ₀ A n) :=
    mul_le_mul_of_nonneg_left hG (by norm_num)
  have hfinal : (∑ y : Obs M (2*M*lam) e,
      if ¬∃ z, fullRectangleReadout S e k l z = fullRectangleReadout S e k l y ∧ G z ∧
        (let V := nativeRectangleRows S e z k l (⟨z,rfl⟩ : Fiber S e z)
         let R := (V.filter fun i => count e z i.val 1 = k).card
         let U := (V.filter fun i => count e z i.val (-1) = l).card
         |(nativeRectangleACount S e z k l (⟨z,rfl⟩ : Fiber S e z) : ℝ)-(U : ℝ)*R/V.card| ≤
           2*Real.sqrt V.card)
      then probability r e S y else 0) ≤ budget n := by
    convert hanchors.trans (by
      convert hpay using 1 <;> first | rfl | (congr 1; apply sum_congr rfl; intro y _; split_ifs <;> rfl)) using 1
    all_goals first | rfl | (apply sum_congr rfl; intro y _; split_ifs <;> rfl)
  apply le_trans _ hfinal
  apply sum_le_sum
  intro o _
  dsimp only
  by_cases hz : ∃ z : Obs M (2*M*lam) e,
      fullRectangleReadout S e k l z = fullRectangleReadout S e k l o ∧ G z ∧
      let V := nativeRectangleRows S e z k l (⟨z,rfl⟩ : Fiber S e z)
      let R := (V.filter fun i => count e z i.val 1 = k).card
      let U := (V.filter fun i => count e z i.val (-1) = l).card
      |(nativeRectangleACount S e z k l (⟨z,rfl⟩ : Fiber S e z) : ℝ)-(U : ℝ)*R/V.card| ≤
        2*Real.sqrt V.card
  · obtain ⟨z,henv,hgz,hcentral⟩ := hz
    let V := nativeRectangleRows S e z k l (⟨z,rfl⟩ : Fiber S e z)
    let N : ℝ := V.card
    let R : ℝ := (V.filter fun i => count e z i.val 1 = k).card
    let U : ℝ := (V.filter fun i => count e z i.val (-1) = l).card
    let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
      l*Real.log ((1-r)/(1+compensation M q r))
    let xA := x z+cellLogit r β lam
    have hNcard : V.card = (nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card :=
      congrArg Finset.card (congrArg (fun u => u.2.1) henv)
    obtain ⟨hN,hlarge,hsize,hsize',hηscale,hs1,hV0,hfeedback⟩ :=
      hengine V.card hgz.1.1 hgz.1.2.1
    have hrootA : (∑ i : Fin M,Real.sigmoid (xA+(score q r e z i-z0))) = q := by
      convert hxroot z using 1
      apply sum_congr rfl
      intro i _
      congr 1
      dsimp only [xA,z0,cellLogit,k,l,M,q,lam]
      ring
    have hidentity (i : Fin M) : xA+(score q r e z i-z0) =
        x z+score q r e z i-Real.log (((M-q : ℕ) : ℝ)/q) := by
      dsimp only [xA,z0,cellLogit,k,l,M,q,lam]
      ring
    have hvarA : v*(q : ℝ) ≤ ∑ i : Fin M,Real.sigmoid (xA+(score q r e z i-z0))*
        (1-Real.sigmoid (xA+(score q r e z i-z0))) := by
      simp_rw [hidentity]
      exact hgz.2.2.1
    have hxA : |xA| ≤ a*N/(4*q) := by
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
      have hlam0 : (0 : ℝ) < lam := by exact_mod_cast (show 0 < lam by omega)
      apply hgz.2.1.trans
      dsimp only [κ₀,N]
      apply (le_div_iff₀ (by positivity : 0 < 4*(q : ℝ))).mpr
      have hh := (div_le_iff₀ hlam0).mp hgz.1.1
      change cN*(q : ℝ) ≤ (V.card : ℝ)*lam at hh
      field_simp
      nlinarith [hh]
    obtain ⟨hH,hPQ,hwidth,hζ,hlog,herror,hgrid⟩ := hwindow
    have hNnonneg : 0 ≤ N := Nat.cast_nonneg V.card
    have hRlo : N/4 ≤ R := by
      have hh : 3/8*N ≤ R := hgz.1.2.2.1
      nlinarith only [hh,hNnonneg]
    have hRhi : R ≤ 3*N/4 := by
      have hh : R ≤ 5/8*N := hgz.1.2.2.2.1
      nlinarith only [hh,hNnonneg]
    have hUlo : N/4 ≤ U := by
      have hh : 3/8*N ≤ U := hgz.1.2.2.2.2.1
      nlinarith only [hh,hNnonneg]
    have hUhi : U ≤ 3*N/4 := by
      have hh : U ≤ 5/8*N := hgz.1.2.2.2.2.2.1
      nlinarith only [hh,hNnonneg]
    have hbgN : ((nativeCalibrationCells (⟨univ,by simp⟩ : Support M M) e z k l 0 \ S.val).card : ℝ) ≤ N := by
      have hb : ((nativeCalibrationCells (⟨univ,by simp⟩ : Support M M) e z k l 0 \ S.val).card : ℝ) ≤
          5/12*N := hgz.1.2.2.2.2.2.2
      have hN0 : 0 ≤ N := Nat.cast_nonneg V.card
      linarith only [hb,hN0]
    have hbound (L τ : ℝ) (hL : 0 < L) (hτ : 0 ≤ τ) :=
      hsmall M q (2*M*lam) S e z k l (8*lam) (denominator n) (decimalNumerator n)
        (Real.log ((M : ℝ)/q)) (Real.sqrt ((lam : ℝ)/q)) (decimalTail n) hq hqm hε hεhalf
        hN hRlo hRhi hUlo hUhi
        hlarge hsize hsize' (by simpa only [mul_div_assoc] using hηscale) hεη hbgN hs1 hV0 hfeedback
        hH hPQ hwidth hζ hlog (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using herror) hgrid
        (⟨z,rfl⟩ : Fiber S e z) xA rfl hgz.2.2.2.2 hrootA hvarA hxA hcentral L τ hL hτ
    have hgood : cN*(q : ℝ)/lam ≤ (nativeRectangleRows S e o k l
        (⟨o,rfl⟩ : Fiber S e o)).card ∧
        ((nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card : ℝ) ≤ CN*(q : ℝ)/lam ∧
        ∀ L τ : ℝ, 0 < L → 0 ≤ τ →
        (∑ y : Obs M (2*M*lam) e,
          if fullRectangleReadout S e k l y = fullRectangleReadout S e k l o ∧
            (∃ b : ℤ, |(ell : ℝ)*(1/2-originalGroupPosteriorMean q r (Real.log ((M : ℝ)/q)) (Real.sqrt ((lam : ℝ)/q))
                    ((k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
                      l*Real.log ((1-r)/(1+compensation M q r))) e y)-b| ≤ τ)
          then probability r e S y else 0)/
          (∑ y : Obs M (2*M*lam) e,
            if fullRectangleReadout S e k l y = fullRectangleReadout S e k l o
            then probability r e S y else 0) ≤
          Cell*(L*(c*((nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card/q)+τ)+
            (1+τ/(c*((nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card/q)))/
              Real.sqrt (nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card+L^(-2 : ℤ)) := by
      refine ⟨by simpa only [←hNcard] using hgz.1.1,
        by simpa only [←hNcard] using hgz.1.2.1,?_⟩
      intro L τ hL hτ
      rw [←henv,←hNcard]
      convert hbound L τ hL hτ using 1 <;> first
        | rfl
        | (congr 2; apply sum_congr rfl; intro y _; split_ifs <;> rfl)
    split_ifs with hbad hbad' hbad'
    all_goals first
      | exact le_rfl
      | exact hp o
      | (exfalso
         apply hbad
         refine ⟨hgood.1,hgood.2.1,?_⟩
         intro L τ hL hτ
         convert hgood.2.2 L τ hL hτ using 1
         all_goals first
           | rfl
           | (congr 1 <;> apply sum_congr rfl <;> intro y _ <;> split_ifs <;> rfl))

  · try simp only [hz,not_false_eq_true,if_true]
    split_ifs <;> first | exact le_rfl | exact hp o


open scoped Classical in
set_option maxHeartbeats 1600000 in
/-- The original cube pair and path experiments satisfy the complete-window
conditional bound uniformly over true supports, outside a vanishing environment budget. -/
theorem original_cube_environment_small_ball (r β : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hβ : 1/2 < β) (hβ1 : β < 1)
    (hα : Real.log (1+r)/(-Real.log (1-r)) = decimalAlpha) :
    ∃ cN CN c : ℝ, 0 < cN ∧ 0 < CN ∧ 0 < c ∧
    ∀ ell : ℤ, ell ≠ 0 → ∃ (Cell : ℝ) (budget : ℕ → ℝ), 0 < Cell ∧
      Tendsto budget atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      let lam := scale n
      let d := ⌊phi r * (lam : ℝ) / (β * Real.log 2)⌋₊
      let M := 2^d
      let q := signalSize r β lam
      let k := centralPositive r lam
      let l := centralNegative r lam
      ∀ (S : Support M q) (e : Experiment),
      letI : Fintype (Sites (2*M*lam) e) := by cases e <;> unfold Sites <;> infer_instance
      (∑ X : Sites (2*M*lam) e → Fin (d+1) → ℤˣ,
        let o := cubeObservationEquiv d (2*M*lam) e X
        let N : ℝ := (nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card
        let s0 := c*(N/q)
        if ¬(cN*(q : ℝ)/lam ≤ N ∧ N ≤ CN*(q : ℝ)/lam ∧
            ∀ L τ : ℝ, 0 < L → 0 ≤ τ →
            (∑ Y : Sites (2*M*lam) e → Fin (d+1) → ℤˣ,
              let y := cubeObservationEquiv d (2*M*lam) e Y
              if fullRectangleReadout S e k l y = fullRectangleReadout S e k l o ∧
                (∃ b : ℤ, |(ell : ℝ)*(1/2-
                  originalCubeGroupPosteriorMean q r (Real.log ((M : ℝ)/q)) (Real.sqrt ((lam : ℝ)/q))
                    ((k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
                      l*Real.log ((1-r)/(1+compensation M q r))) e Y)-b| ≤ τ)
              then originalCubeProbability r e S Y else 0)/
              (∑ Y : Sites (2*M*lam) e → Fin (d+1) → ℤˣ,
              let y := cubeObservationEquiv d (2*M*lam) e Y
                if fullRectangleReadout S e k l y = fullRectangleReadout S e k l o
                then originalCubeProbability r e S Y else 0) ≤
              Cell*(L*(s0+τ)+(1+τ/s0)/Real.sqrt N+L^(-2 : ℤ)))
        then originalCubeProbability r e S X else 0) ≤ budget n := by
  classical
  obtain ⟨cN,CN,c,hcN,hCN,hc,hmain⟩ :=
    original_native_environment_small_ball r β hr hr1 hβ hβ1 hα
  refine ⟨cN,CN,c,hcN,hCN,hc,?_⟩
  intro ell hell
  obtain ⟨Cell,budget,hCell,hbudget,hmain⟩ := hmain ell hell
  refine ⟨Cell,budget,hCell,hbudget,?_⟩
  filter_upwards [hmain] with n hn
  dsimp only [population] at hn ⊢
  intro S e
  let lam := scale n
  let d := ⌊phi r * (lam : ℝ) / (β * Real.log 2)⌋₊
  let M := 2^d
  let q := signalSize r β lam
  let k := centralPositive r lam
  let l := centralNegative r lam
  let s := 2*M*lam
  letI : Fintype (Sites s e) := by cases e <;> unfold Sites <;> infer_instance
  let E := cubeObservationEquiv d s e
  have hnative := hn S e
  apply le_of_eq_of_le _ hnative
  apply Fintype.sum_equiv E
  intro X
  rw [original_cube_probability_eq_native]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  apply propext
  constructor
  · intro h L τ hL hτ
    have hb := h L τ hL hτ
    let Pred := fun y : Obs M s e => ∃ b : ℤ,
      |(ell : ℝ)*(1/2-originalGroupPosteriorMean q r (Real.log ((M : ℝ)/q))
        (Real.sqrt ((lam : ℝ)/q))
        ((k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
          l*Real.log ((1-r)/(1+compensation M q r))) e y)-b| ≤ τ
    have heq := original_cube_conditional_mass_eq r e S X k l Pred
    conv at hb =>
      lhs
      simp only [original_cube_group_eq_native]
    calc
      _ = _ := by
        convert heq.symm using 1
        all_goals first
          | rfl
          | (congr 1 <;> apply sum_congr rfl <;> intro y _ <;> split_ifs <;> rfl)
      _ ≤ _ := by
        convert hb using 1
        all_goals first
          | rfl
          | (congr 1 <;> apply sum_congr rfl <;> intro y _ <;> split_ifs <;> rfl)
  · intro h L τ hL hτ
    let Pred := fun y : Obs M s e => ∃ b : ℤ,
      |(ell : ℝ)*(1/2-originalGroupPosteriorMean q r (Real.log ((M : ℝ)/q))
        (Real.sqrt ((lam : ℝ)/q))
        ((k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
          l*Real.log ((1-r)/(1+compensation M q r))) e y)-b| ≤ τ
    have heq := original_cube_conditional_mass_eq r e S X k l Pred
    conv_lhs => simp only [original_cube_group_eq_native]
    calc
      _ = _ := by
        convert heq using 1
        all_goals first
          | rfl
          | (congr 1 <;> apply sum_congr rfl <;> intro y _ <;> split_ifs <;> rfl)
      _ ≤ _ := by
        convert h L τ hL hτ using 1
        all_goals first
          | rfl
          | (congr 1 <;> apply sum_congr rfl <;> intro y _ <;> split_ifs <;> rfl)

end
end D5.S3.Estimation.TimeArrow.NativeOriginalSmallBall
