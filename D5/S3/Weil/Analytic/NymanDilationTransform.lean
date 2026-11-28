/- GID: D5/S3/Weil/Analytic/NymanDilationTransform
   generality: I
   mirror-B: none(waiver:weighted-dilation-factorization-support)
   mirror-E: none(waiver:nyman-centered-prime-analysis)
   anchors: []
   utility: none
   digest: Mellin factorization for compactly supported weighted dilations. -/

import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Mellin factorization for compactly supported weighted dilations. -/

set_option autoImplicit false

noncomputable section

open Complex Filter Finset MeasureTheory Set
open scoped Topology

namespace NymanDilationTransform

def dilatedSum (a : ℕ → ℂ) (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, a n * W ((n : ℝ) * t)

/-- Compact support makes the weighted dilations locally finite at positive scales. -/
theorem continuousOn_dilatedSum (a : ℕ → ℂ) {W : ℝ→ℂ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) :
    ContinuousOn (dilatedSum a W) (Set.Ioi 0) := by
  intro t ht
  let R : ℕ := ⌈4/t⌉₊
  have hpos : 0<t := ht
  have he : dilatedSum a W =ᶠ[𝓝[Set.Ioi 0] t]
      fun x => ∑ n∈range (R+1), a n*W ((n:ℝ)*x) := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show t/2<t by linarith))] with x hx
    unfold dilatedSum
    apply tsum_eq_sum
    intro n hn
    have hnR : R<n := by simpa [Finset.mem_range,not_lt] using hn
    have hR : 4/t≤(R:ℝ) := Nat.le_ceil _
    have hRn : (R:ℝ)<n := by exact_mod_cast hnR
    have hnt : (4:ℝ)<(n:ℝ)*t := by
      exact (div_lt_iff₀ hpos).mp (hR.trans_lt hRn)
    have hnx : 2≤(n:ℝ)*x := by
      have hn0 : (0:ℝ)≤n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hx.le hn0]
    rw [hW _ (by intro h; exact (not_lt_of_ge hnx) h.2),mul_zero]
  apply (Continuous.continuousWithinAt (f:=fun x => ∑ n∈range (R+1), a n*W ((n:ℝ)*x)) ?_).congr_of_eventuallyEq_of_mem he ht
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (hc.comp (continuous_const.mul continuous_id))

private theorem W_convergent {W : ℝ→ℂ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) (s : ℂ) : MellinConvergent W s := by
  have hzTop : W=ᶠ[atTop] (fun _ => (0:ℂ)) := eventually_atTop.2 ⟨2,fun x hx => hW _ (by intro h; linarith [h.2])⟩
  have hzBot : W=ᶠ[𝓝[>] (0:ℝ)] (fun _ => (0:ℂ)) := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with x hx
    exact hW _ (by intro h; exact (not_lt_of_ge hx.le) h.1)
  refine mellinConvergent_of_isBigO_rpow (a:=s.re+1) (b:=s.re-1)
    (hc.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ (by linarith)
  · exact (Asymptotics.isBigO_zero _ _).congr' hzTop.symm (Filter.EventuallyEq.rfl)
  · exact (Asymptotics.isBigO_zero _ _).congr' hzBot.symm (Filter.EventuallyEq.rfl)

/-- The Mellin transform of a continuous kernel supported in the fixed compact
interval is continuous at every exponent. -/
theorem continuous_mellin_kernel {W : ℝ → ℂ} (hc : Continuous W)
    (hW : ∀ x ∉ Set.Ioo (1 : ℝ) 2, W x = 0) : Continuous (mellin W) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hzTop : W =ᶠ[atTop] (fun _ => (0 : ℂ)) :=
    eventually_atTop.2 ⟨2, fun x hx => hW _ (by intro h; linarith [h.2])⟩
  have hzBot : W =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : ℂ)) := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    exact hW _ (by intro h; exact (not_lt_of_ge hx.le) h.1)
  have hd : DifferentiableAt ℂ (mellin W) s := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
      (hc.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ (by linarith)
    · exact (Asymptotics.isBigO_zero _ _).congr' hzTop.symm (Filter.EventuallyEq.rfl)
    · exact (Asymptotics.isBigO_zero _ _).congr' hzBot.symm (Filter.EventuallyEq.rfl)
  exact hd.continuousAt

private theorem integrable_term {a : ℕ → ℂ} (ha : a 0 = 0) {W : ℝ→ℂ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) (s : ℂ) (n : ℕ) :
    Integrable (fun t : ℝ => (t:ℂ)^(s-1)*(a n*W ((n:ℝ)*t))) (volume.restrict (Set.Ioi 0)) := by
  rcases eq_or_ne n 0 with rfl|hn
  · simp [ha]
  · have hnpos : (0:ℝ)<n := by positivity
    have h := (MellinConvergent.comp_mul_left hnpos).mpr (W_convergent hc hW s)
    unfold MellinConvergent at h
    simpa only [smul_eq_mul,mul_left_comm] using h.const_mul (a n)

private theorem integral_term {a : ℕ → ℂ} (ha : a 0 = 0) {W : ℝ→ℂ} (s : ℂ) (n : ℕ) :
    (∫ t in Set.Ioi (0:ℝ),(t:ℂ)^(s-1)*(a n*W ((n:ℝ)*t))) =
      LSeries.term a s n*mellin W s := by
  rcases eq_or_ne n 0 with rfl|hn
  · simp [ha, LSeries.term_zero]
  · have hnpos : (0:ℝ)<n := by positivity
    simp_rw [mul_left_comm ((_:ℂ)^(s-1)) (a n),integral_const_mul]
    change a n*mellin (fun t => W ((n:ℝ)*t)) s = _
    rw [mellin_comp_mul_left W s hnpos,LSeries.term_of_ne_zero hn,smul_eq_mul,Complex.cpow_neg]
    push_cast
    ring

private theorem norm_integral_term {a : ℕ → ℂ} (ha : a 0 = 0) {W : ℝ→ℂ} (s : ℂ) (n : ℕ) :
    (∫ t in Set.Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*(a n*W ((n:ℝ)*t))‖) =
      ‖LSeries.term a s n‖ *
        (∫ t in Set.Ioi (0:ℝ), ‖(t:ℂ)^(s-1)*W t‖) := by
  rcases eq_or_ne n 0 with rfl|hn
  · simp [ha, LSeries.term_zero]
  · let G : ℝ→ℝ := fun t => ‖(t:ℂ)^(s-1)*W t‖
    have hnpos : (0:ℝ)<n := by positivity
    have hpoint (t : ℝ) (ht : 0<t) :
        ‖(t:ℂ)^(s-1)*(a n*W ((n:ℝ)*t))‖ =
          ‖a n‖ * (n:ℝ)^(1-s.re) * G ((n:ℝ)*t) := by
      unfold G
      rw [norm_mul,norm_mul,norm_mul,Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hnpos.le ht.le,norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      have he : (s-1).re=s.re-1 := by simp
      rw [he]
      have hp : (n:ℝ)^(1-s.re)*(n:ℝ)^(s.re-1)=1 := by
        rw [←Real.rpow_add hnpos,show 1-s.re+(s.re-1)=0 by ring,Real.rpow_zero]
      calc
        _ = ‖a n‖ * (((n:ℝ)^(1-s.re)*(n:ℝ)^(s.re-1)) *
          (‖(t:ℂ)^(s-1)‖*‖W ((n:ℝ)*t)‖)) := by rw [hp,one_mul]; ring
        _ = _ := by ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint,integral_const_mul,
      integral_comp_mul_left_Ioi G 0 hnpos,mul_zero]
    change ‖a n‖*(n:ℝ)^(1-s.re) * ((n:ℝ)⁻¹ * ∫ t in Set.Ioi 0,G t) = _
    rw [LSeries.term_of_ne_zero hn,norm_div]
    rw [show (n:ℂ)=((n:ℝ):ℂ) by push_cast; rfl,Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    have hpow : (n:ℝ)^(1-s.re)*(n:ℝ)⁻¹=((n:ℝ)^s.re)⁻¹ := by
      rw [←Real.rpow_neg_one,←Real.rpow_add hnpos,←Real.rpow_neg hnpos.le]
      congr 1
      ring
    rw [show ∫ t in Set.Ioi (0:ℝ),‖(t:ℂ)^(s-1)*W t‖ = ∫ t in Set.Ioi 0,G t by rfl, mul_assoc,←mul_assoc ((n:ℝ)^(1-s.re)),hpow]
    ring

/-- Absolute summability of the Dirichlet coefficients justifies applying
the Mellin transform termwise to the dilations. -/
theorem mellin_dilatedSum {a : ℕ → ℂ} (ha : a 0 = 0) {W : ℝ → ℂ}
    (hc : Continuous W) (hW : ∀ x ∉ Set.Ioo (1 : ℝ) 2, W x = 0)
    {s : ℂ} (hs : LSeriesSummable a s) :
    mellin (dilatedSum a W) s = LSeries a s * mellin W s := by
  have hsum : Summable (fun n : ℕ => ∫ t in Set.Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) := by
    simp_rw [norm_integral_term ha]
    exact hs.norm.mul_right _
  unfold mellin at ⊢
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), ∑' n, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := by
      simp_rw [dilatedSum, smul_eq_mul, tsum_mul_left]
    _ = ∑' n : ℕ, ∫ t in Set.Ioi (0 : ℝ),
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) :=
      (integral_tsum_of_summable_integral_norm (integrable_term ha hc hW s) hsum).symm
    _ = _ := by
      simp_rw [integral_term ha]
      rw [tsum_mul_right]
      rfl

end NymanDilationTransform
