/- GID: D5/S1/Words/Patterns/Separable/OccupiedTruncatedMixture
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedTruncatedMixture
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence]
   utility: none
   digest: The truncated exponent mixture has a positive logarithmic generator gain. -/

import D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual symmetric jump generator commutes with the finite exponent
integral. The positive Kelvin gap survives integration on a logarithmic scale. -/

open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace D5.S1.Words.Patterns.Separable.OccupiedTruncatedMixture

open OccupiedComparison OccupiedActualPowerGenerator OccupiedMellinKelvin

private theorem kernel_nonneg (i : ℕ) : 0 ≤ kernelWeight i := by
  have hr : 0 ≤ rho := sq_nonneg b
  unfold kernelWeight shapeWeight
  split_ifs
  · exact add_nonneg (mul_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
      (div_nonneg hr (by norm_num))
  · exact add_nonneg (mul_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _)) le_rfl

private theorem kernel_summable : Summable kernelWeight := critical_shape_masses.2.2.1

noncomputable def truncatedProfile (z : ℤ) : ℝ :=
  ∫ s in (0 : ℝ)..(1 / 4), powerProfile ((1 / 2 : ℝ) + s) z

private noncomputable def mixtureTerm (z : ℤ) (i : ℕ) (s : ℝ) : ℝ :=
  kernelWeight i *
    (powerProfile (1 / 2 + s) (z + (i + 1 : ℕ)) +
      powerProfile (1 / 2 + s) (z - (i + 1 : ℕ)) - 2 * powerProfile (1 / 2 + s) z)

private theorem profile_beta_continuous (x : ℤ) :
    Continuous (fun s : ℝ => powerProfile (1 / 2 + s) x) := by
  unfold powerProfile
  have h : Continuous (fun s : ℝ => -((1 / 2 : ℝ) + s)) := by fun_prop
  exact (Real.continuous_const_rpow (show 2+|(x : ℝ)| ≠ 0 by positivity)).comp h

private theorem mixtureTerm_continuous (z : ℤ) (i : ℕ) :
    Continuous (mixtureTerm z i) := by
  exact continuous_const.mul
    (((profile_beta_continuous _).add (profile_beta_continuous _)).sub
      (continuous_const.mul (profile_beta_continuous _)))

private theorem profile_bound {s : ℝ} (hs : 0 ≤ s) (x : ℤ) :
    |powerProfile (1 / 2 + s) x| ≤ 1 := by
  have hx : 1 ≤ 2+|(x : ℝ)| := by linarith [abs_nonneg (x : ℝ)]
  unfold powerProfile
  rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)

private theorem mixtureTerm_bound (z : ℤ) (i : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖mixtureTerm z i s‖ ≤ 4 * kernelWeight i := by
  unfold mixtureTerm
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg i)]
  have h1 := profile_bound hs (z + (i + 1 : ℕ))
  have h2 := profile_bound hs (z - (i + 1 : ℕ))
  have h3 := profile_bound hs z
  have hD : |powerProfile (1 / 2 + s) (z + (i + 1 : ℕ)) +
      powerProfile (1 / 2 + s) (z - (i + 1 : ℕ)) - 2 * powerProfile (1 / 2 + s) z| ≤ 4 := by
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact (add_le_add (abs_add_le _ _) le_rfl).trans (by linarith only [h1,h2,h3])
  exact (mul_le_mul_of_nonneg_left hD (kernel_nonneg i)).trans_eq (by ring)

private theorem mixture_integrand_continuousOn (z : ℤ) :
    ContinuousOn (fun s : ℝ => actualGenerator (powerProfile (1 / 2 + s)) z)
      (Icc (0 : ℝ) (1 / 4)) := by
  change ContinuousOn (fun s : ℝ => ∑' i : ℕ, mixtureTerm z i s) (Icc (0 : ℝ) (1 / 4))
  exact continuousOn_tsum (fun i => (mixtureTerm_continuous z i).continuousOn)
    (kernel_summable.mul_left 4) (fun i _ hs => mixtureTerm_bound z i hs.1)

/-- The finite exponent integral commutes with the actual generator.
Absolute integral-norm summability is supplied by the real critical mass. -/
private theorem actualGenerator_truncatedProfile (z : ℤ) :
    actualGenerator truncatedProfile z =
      ∫ s in (0 : ℝ)..(1 / 4), actualGenerator (powerProfile (1 / 2 + s)) z := by
  let f := mixtureTerm z
  let I := Ioc (0 : ℝ) (1 / 4)
  have h01 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hI (i : ℕ) : Integrable (f i) (volume.restrict I) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp
      ((mixtureTerm_continuous z i).intervalIntegrable _ _)
  have hNorm (i : ℕ) : ‖∫ s, ‖f i s‖ ∂volume.restrict I‖ ≤ kernelWeight i := by
    rw [← intervalIntegral.integral_of_le h01]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 / 4 : ℝ))
      (f := fun s => ‖f i s‖) (C := 4 * kernelWeight i)
      (fun s hs => by
        rw [uIoc_of_le h01] at hs
        rw [Real.norm_of_nonneg (norm_nonneg (f i s))]
        exact mixtureTerm_bound z i hs.1.le)
    exact hb.trans_eq (by rw [sub_zero, abs_of_nonneg h01]; ring)
  have hS : Summable fun i : ℕ => ∫ s, ‖f i s‖ ∂volume.restrict I :=
    kernel_summable.of_norm_bounded hNorm
  rw [intervalIntegral.integral_of_le h01]
  change actualGenerator truncatedProfile z = ∫ s, (∑' i : ℕ, f i s) ∂volume.restrict I
  rw [← integral_tsum_of_summable_integral_norm hI hS]
  unfold actualGenerator
  apply tsum_congr
  intro i
  rw [← intervalIntegral.integral_of_le h01]
  dsimp only [f, mixtureTerm, truncatedProfile]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
  all_goals
    first
    | exact (profile_beta_continuous _).intervalIntegrable _ _
    | exact ((profile_beta_continuous _).add (profile_beta_continuous _)).intervalIntegrable _ _
    | exact (continuous_const.mul (profile_beta_continuous _)).intervalIntegrable _ _

private theorem log_weighted_first_moment (L : ℝ) (hL : 4 ≤ L) :
    Real.exp (-1) / (2 * L ^ 2) ≤ ∫ s in (0 : ℝ)..(1 / 4), s * Real.exp (-L * s) := by
  let f (s : ℝ) := s * Real.exp (-L * s)
  have hLp : 0 < L := by linarith
  have hd : 0 ≤ L⁻¹ := inv_nonneg.mpr hLp.le
  have htop : L⁻¹ ≤ 1 / 4 :=
    ((inv_le_inv₀ hLp (by norm_num : (0 : ℝ)<4)).2 hL).trans_eq (by ring)
  have hf : Continuous f := by fun_prop
  have hg : Continuous (fun s : ℝ => Real.exp (-1) * s) := by fun_prop
  have hm : (∫ s in (0 : ℝ)..L⁻¹, Real.exp (-1) * s) ≤ ∫ s in (0 : ℝ)..L⁻¹, f s := by
    apply intervalIntegral.integral_mono_on hd
      (hg.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
    intro s hs
    change Real.exp (-1) * s ≤ s * Real.exp (-L * s)
    rw [mul_comm (Real.exp (-1)) s]
    apply mul_le_mul_of_nonneg_left _ hs.1
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hs.2 hLp.le
    rw [mul_inv_cancel₀ hLp.ne'] at h
    linarith
  have hc : 0 ≤ ∫ s in L⁻¹..(1 / 4 : ℝ), f s := by
    apply intervalIntegral.integral_nonneg htop
    exact fun s hs => mul_nonneg (hd.trans hs.1) (Real.exp_nonneg _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (0 : ℝ) L⁻¹) (hf.intervalIntegrable L⁻¹ (1 / 4 : ℝ))
  rw [intervalIntegral.integral_const_mul, integral_id, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    sub_zero] at hm
  have he : Real.exp (-1) * ((L⁻¹) ^ 2 / 2) = Real.exp (-1) / (2 * L ^ 2) := by
    field_simp
  rw [he] at hm
  change Real.exp (-1) / (2 * L ^ 2) ≤ ∫ s in (0 : ℝ)..(1 / 4), f s
  rw [← hsplit]
  exact hm.trans (le_add_of_nonneg_right hc)

private theorem log_sq_eventual (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ 2 ≤ c * (n : ℝ) ^ (1 / 80 : ℝ) := by
  have h0 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ)<1 / 80)).bound hc
  have h := tendsto_natCast_atTop_atTop.eventually h0
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn h1
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast h1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hN) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hn
  simpa only [← Real.rpow_natCast, Nat.cast_ofNat] using hn

/-- The actual kernel acting on the truncated log mixture has an eventual
positive contribution of order 1 / (n log² n). This does not include the
large-exponent tail of the profile or the nonlinear loss term. -/
private theorem eventual_truncated_generator_gain :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) ≤ actualGenerator truncatedProfile (n : ℤ) := by
  obtain ⟨A,hA,C,hC,H⟩ := actual_generator_power_comparison
  let B := A * gapCoefficient
  have hB : 0 < B := mul_pos hA signed_mellin_cancellation_and_gap.2.2.1
  let c := B * Real.exp (-1) / 4
  have hc : 0 < c := div_pos (mul_pos hB (Real.exp_pos _)) (by norm_num)
  refine ⟨c,hc,?_⟩
  have hbig := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  have he := log_sq_eventual (4 * c / (C + 1)) (div_pos (by positivity) (by positivity))
  filter_upwards [eventually_ge_atTop (4 ^ 20 : ℕ), hbig, he] with n hn hL he
  let N := (n : ℝ)
  let L := Real.log N
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (4 ^ 20 : ℕ)) hn
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast hn0
  have hLp : 0 < L := by change 4 ≤ L at hL; linarith
  let err := C * N ^ (-(1 / 80 : ℝ))
  have herr : 0 ≤ err := mul_nonneg hC (Real.rpow_nonneg hN.le _)
  let f (s : ℝ) := s * Real.exp (-L * s)
  let D (s : ℝ) := actualGenerator (powerProfile (1 / 2 + s)) (n : ℤ)
  have h0 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hPoint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (1 / 4)) :
      B * f s - err ≤ N * D s := by
    have hβ₁ : (1 / 2 : ℝ) ≤ 1 / 2 + s := by linarith [hs.1]
    have hβ₂ : (1 / 2 : ℝ) + s ≤ 3 / 4 := by linarith [hs.2]
    have h := (H _ hβ₁ hβ₂ n hn).2
    have hx : ((1 / 2 : ℝ) + s) - 1 / 2 = s := by ring
    have hy : ((1 / 2 : ℝ) + s) + (1 / 2 : ℝ) = 1 + s := by ring
    rw [hx,hy] at h
    change A * (gapCoefficient * s) - err ≤ N ^ (1 + s) * D s at h
    let W := Real.exp (-L * s)
    have hWp : 0 ≤ W := Real.exp_nonneg _
    have hW1 : W ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hLp.le) hs.1)
    have hWr : W = N ^ (-s) := by
      rw [Real.rpow_def_of_pos hN]
      unfold W L
      congr 1
      ring
    have hcancel : N ^ (1 + s) * W = N := by
      rw [hWr, ← Real.rpow_add hN, show (1 + s)+ -s = 1 by ring, Real.rpow_one]
    have hMul := mul_le_mul_of_nonneg_right h hWp
    rw [mul_right_comm, hcancel] at hMul
    have hErr := mul_le_mul_of_nonneg_left hW1 herr
    calc
      _ ≤ (A * (gapCoefficient * s) - err) * W := by
        change B * (s * W) - err ≤ _
        dsimp only [B]
        rw [sub_mul]
        have halg : A * gapCoefficient * (s * W) = A * (gapCoefficient * s) * W := by ring
        rw [halg]
        exact sub_le_sub_left (by simpa only [mul_one] using hErr) _
      _ ≤ _ := hMul
  have hf : Continuous f := by fun_prop
  have hModel : Continuous (fun s : ℝ => B * f s - err) :=
    (continuous_const.mul hf).sub continuous_const
  have hDint : IntervalIntegrable D volume 0 (1 / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h0]
    exact mixture_integrand_continuousOn (n : ℤ)
  have hInt := intervalIntegral.integral_mono_on (μ := volume) h0
    (hModel.intervalIntegrable _ _) (hDint.const_mul N) hPoint
  have hBf : IntervalIntegrable (fun s : ℝ => B * f s) volume 0 (1 / 4) :=
    (hf.intervalIntegrable _ _).const_mul B
  have hErrInt : IntervalIntegrable (fun _ : ℝ => err) volume 0 (1 / 4) :=
    intervalIntegrable_const
  have hSub := intervalIntegral.integral_sub hBf hErrInt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hSub
  rw [hSub, intervalIntegral.integral_const_mul] at hInt
  have hMain := mul_le_mul_of_nonneg_left (log_weighted_first_moment L hL) hB.le
  have hMainEq : B * (Real.exp (-1) / (2 * L ^ 2)) = 2 * (c / L ^ 2) := by dsimp only [c]; ring
  rw [hMainEq] at hMain
  have hErr : (1 / 4 : ℝ) * err ≤ c / L ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hLp)).2
    change L ^ 2 ≤ (4 * c / (C + 1)) * N ^ (1 / 80 : ℝ) at he
    have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ (1 / 4 : ℝ) * err by positivity)
    have heq : ((1 / 4 : ℝ) * err) * ((4 * c / (C + 1)) * N ^ (1 / 80 : ℝ)) =
        (C / (C + 1)) * c := by
      dsimp only [err]
      have hx : N ^ (-(1 / 80 : ℝ)) * N ^ (1 / 80 : ℝ) = 1 := by
        rw [← Real.rpow_add hN]; norm_num
      calc
        _ = (C / (C + 1)) * c * (N ^ (-(1 / 80 : ℝ)) * N ^ (1 / 80 : ℝ)) := by ring
        _ = _ := by rw [hx,mul_one]
    rw [heq] at hmul
    exact hmul.trans ((mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (by positivity : 0 < C + 1)).2 (by linarith)) hc.le).trans_eq (one_mul _))
  have hd := actualGenerator_truncatedProfile (n : ℤ)
  change actualGenerator truncatedProfile (n : ℤ) = ∫ s in (0 : ℝ)..(1 / 4), D s at hd
  have hb : c / L ^ 2 ≤ N * actualGenerator truncatedProfile (n : ℤ) := by
    rw [hd]
    linarith only [hMain,hInt,hErr]
  change c / (N * L ^ 2) ≤ _
  rw [mul_comm N, ← div_div]
  exact (div_le_iff₀ hN).2 (hb.trans_eq (by ring))

/-- Evaluation of the finite exponent integral for a positive logarithmic base. -/
private theorem exponent_integral_closed {X : ℝ} (hX : 1 < X) :
    (∫ s in (0 : ℝ)..(1 / 4), X ^ (-(1 / 2 + s))) =
      (1 - X ^ (-(1 / 4 : ℝ))) / (Real.sqrt X * Real.log X) := by
  have hx : 0 < X := zero_lt_one.trans hX
  have hl := Real.log_pos hX
  have hr : 0 < Real.sqrt X := Real.sqrt_pos.mpr hx
  have factor (s : ℝ) :
      X ^ (-(1 / 2 + s)) = X ^ (-(1 / 2 : ℝ)) * Real.exp (s * (-Real.log X)) := by
    simp only [Real.rpow_def_of_pos hx]
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [factor]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_right Real.exp (neg_ne_zero.mpr hl.ne'),
    integral_exp]
  simp only [zero_mul, Real.exp_zero, smul_eq_mul, inv_neg]
  rw [show (1 / 4 : ℝ) * (-Real.log X) = Real.log X * (-(1 / 4 : ℝ)) by ring,
    ← Real.rpow_def_of_pos hx, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  field_simp; ring


/-- Actual sum-integral interchange, the closed form at every integer position,
and the eventual positive gain on the positive integer tail. -/
theorem truncated_profile_analysis :
    (∀ z : ℤ,
      let X : ℝ := 2 + |(z : ℝ)|
      actualGenerator truncatedProfile z =
        (∫ s in (0 : ℝ)..(1 / 4), actualGenerator (powerProfile (1 / 2 + s)) z) ∧
      truncatedProfile z =
        (1 - X ^ (-(1 / 4 : ℝ))) / (Real.sqrt X * Real.log X)) ∧
    (∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) ≤ actualGenerator truncatedProfile (n : ℤ)) := by
  refine ⟨fun z => ⟨actualGenerator_truncatedProfile z, ?_⟩, eventual_truncated_generator_gain⟩
  unfold truncatedProfile powerProfile
  exact exponent_integral_closed (by linarith [abs_nonneg (z : ℝ)])

end D5.S1.Words.Patterns.Separable.OccupiedTruncatedMixture
