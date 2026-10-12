/- GID: D5/S3/Estimation/TimeArrow/NativeOriginalWindowSequence
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeOriginalWindowSequence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original decimal series supplies the compensated score grid and window. -/

import D5.S3.Estimation.TimeArrow.NativeGrowthRounding
import D5.S3.Estimation.TimeArrow.OriginalScoreWindow

open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeGrowthRounding
open D5.S3.Estimation.TimeArrow.OriginalScoreWindow
open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.NativeOriginalWindowSequence
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

private theorem shifted_exponent (n j : ℕ) : decimalExponent n+j ≤ decimalExponent (n+j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hh := exponent_strictMono (Nat.lt_succ_self (n+j))
    change decimalExponent (n+j) < decimalExponent (n+j+1) at hh
    have he : n+(j+1) = n+j+1 := by omega
    rw [he]
    omega

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
    have he := shifted_exponent (n+1) j
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
      rw [div_div_eq_mul_div,←Real.exp_sub]
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
theorem original_window_sequence_conditions (r β : ℝ) (hr : 0 < r) (hr1 : r < 1)
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
  have hkl : k+l=lam := (central_rounding r lam hr.le hr1.le).2.1
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
  have hlam : (lam : ℝ)=(denominator n : ℝ)^3 := by simp [lam,scale]
  have hgrid : (denominator n : ℝ)*w ≤ h/4 := by
    have hb := (div_lt_iff₀ hq0).mp hg
    have hp : (denominator n : ℝ)^2*(lam : ℝ) ≤ (lam : ℝ)^2 := by rw [hlam]; nlinarith [sq_nonneg ((denominator n : ℝ)-1)]
    have hs := (eq_div_iff hq0.ne').mp hwsq
    have hm := mul_le_mul_of_nonneg_left hs.le (sq_nonneg (denominator n : ℝ))
    nlinarith only [hb,hp,hm,hh,hw.le,hQ.le,hq0]
  refine ⟨by change k+l+2 ≤ 8*lam; have hn : 4 ≤ lam := by exact_mod_cast (hlam.trans' (by norm_num : (4 : ℝ) ≤ 64)); omega,decimal_numerator_lt n,hw,(decimal_tail_bounds n).1,?_,?_,hgrid⟩
  · rw [←decimal_series_decomposition]
    simpa only [h,mul_comm] using (div_eq_iff hh.ne').mp hα
  · have hsum := add_le_add (add_le_add ht1 he1) hraw
    have hh' := (div_le_iff₀ hq0).mpr hwq
    dsimp only [w,h,k,l,M,q,lam] at *
    linarith only [hsum,hh']

end
end D5.S3.Estimation.TimeArrow.NativeOriginalWindowSequence
