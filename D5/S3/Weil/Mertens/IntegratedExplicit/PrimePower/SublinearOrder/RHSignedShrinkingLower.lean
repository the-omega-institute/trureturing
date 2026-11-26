/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSignedShrinkingLower
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSignedShrinkingLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A logarithmic lower scale for late signed prime windows of shrinking width. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootLateIncrement
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoffFourier

/-! The cusp persists under the positive exponential average of the signed window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set MeasureTheory ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity (weight)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit phaseOrbit_cluster_iff)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder (phaseOrbit_eq_mode)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (coeff_real on_line)

private theorem root_imaginary_coefficient (hRH : RiemannHypothesis) (r : ℝ) (k : ℕ) :
    (rootCoeff r k).im =
      r * (r - 1) * (actualZero k).im * weight k /
        ((r - 1 / 2) ^ 2 + (actualZero k).im ^ 2) := by
  unfold rootCoeff weight
  rw [Complex.div_im, Complex.normSq_mul]
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    neg_zero, zero_mul, zero_sub, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.normSq_apply, on_line hRH k, ← pow_two, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The odd part about the origin is bounded linearly under RH. -/
theorem odd_root_increment (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) {h : ℝ}
    (hh : 0 ≤ h) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    |rootSignal r h - rootSignal r (-h)| ≤ 2 * (r - 1) * firstLiMass * h / s := by
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  have hr0 : 0 < r := by linarith
  have hs : 0 < s := by
    dsimp [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  have hw : HasSum weight firstLiMass := by
    unfold weight
    simpa only [coeff_real hRH, Complex.ofReal_re] using Complex.hasSum_re actualCoeff_hasSum
  let term := fun (u : ℝ) (k : ℕ) =>
    (rootCoeff r k * Complex.exp (frequency k / (r : ℂ) * (u : ℂ))).re
  let raw := fun u : ℝ => (∑' k, rootCoeff r k * Complex.exp (frequency k / (r : ℂ) * (u : ℂ))).re
  have hsum : HasSum (fun k => term h k - term (-h) k) (raw h - raw (-h)) :=
    (root_series_hasSum hRH hr h).sub (root_series_hasSum hRH hr (-h))
  have hmajor := hw.mul_left (2 * (r - 1) * h)
  have hbound (k : ℕ) : |term h k - term (-h) k| ≤ 2 * (r - 1) * h * weight k := by
    let γ := (actualZero k).im
    let a := r - 1 / 2
    let x := γ * (h / r)
    have ha : 0 < a := by dsimp [a]; linarith
    have hden : 0 < a ^ 2 + γ ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg _)
    have hwk : 0 ≤ weight k := by unfold weight; positivity
    have hphase (u : ℝ) : frequency k / (r : ℂ) * (u : ℂ) =
        (((γ * (u / r) : ℝ) : ℂ)) * Complex.I := by
      exact phase_eq hRH hr u k
    have hcancel : term h k - term (-h) k = -2 * (rootCoeff r k).im * Real.sin x := by
      simp only [term, hphase, neg_div, mul_neg, Real.cos_neg, Real.sin_neg,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.mul_re, x]
      ring
    have hr1 : 0 ≤ r - 1 := sub_nonneg.mpr hr.le
    have hcoef : |(rootCoeff r k).im| =
        r * (r - 1) * |γ| * weight k / (a ^ 2 + γ ^ 2) := by
      rw [root_imaginary_coefficient hRH, abs_div, abs_of_pos hden, abs_mul, abs_mul,
        abs_mul, abs_of_nonneg hr0.le, abs_of_nonneg hr1, abs_of_nonneg hwk]
    have hscale : |x| = |γ| * (h / r) := by
      dsimp only [x]
      rw [abs_mul, abs_of_nonneg (div_nonneg hh hr0.le)]
    rw [hcancel, abs_mul, abs_mul, show |(-2 : ℝ)| = 2 by norm_num, hcoef]
    calc
      _ ≤ 2 * (r * (r - 1) * |γ| * weight k / (a ^ 2 + γ ^ 2)) * |x| :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := x)) (by positivity)
      _ = (γ ^ 2 / (a ^ 2 + γ ^ 2)) * (2 * (r - 1) * h * weight k) := by
        rw [hscale, ← sq_abs γ]
        field_simp [hr0.ne', hden.ne']
      _ ≤ 1 * (2 * (r - 1) * h * weight k) :=
        mul_le_mul_of_nonneg_right
          ((div_le_one hden).2 (le_add_of_nonneg_left (sq_nonneg _))) (by positivity)
      _ = _ := one_mul _
  change |raw h / s - raw (-h) / s| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hs]
  apply div_le_div_of_nonneg_right ?_ hs.le
  rw [show 2 * (r - 1) * firstLiMass * h = 2 * (r - 1) * h * firstLiMass by ring,
    ← hsum.tsum_eq, ← hmajor.tsum_eq, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hsum.summable.norm).trans
    (hsum.summable.norm.tsum_le_tsum (fun k => by simpa only [Real.norm_eq_abs] using hbound k)
      hmajor.summable)

private theorem one_sided_root_lower (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    ∃ H ∈ Ioo (0 : ℝ) (1 / 2), ∀ h : ℝ, 0 < h → h < H →
      h * Real.log (1 / h) / (4 * s) ≤ rootSignal r h - rootSignal r 0 := by
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  have hr0 : 0 < r := by linarith
  have hs : 0 < s := by
    dsimp [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  obtain ⟨C, hC, hcusp⟩ := root_signal_symmetric_cusp hRH hr
  let B := |Real.log r - 2 * c| + s * C + 2 * (r - 1) * firstLiMass
  let H := min (1 / 4) (min (r / 2) (Real.exp (-(2 * B))))
  have hH0 : 0 < H := lt_min (by norm_num) (lt_min (by positivity) (Real.exp_pos _))
  have hH1 : H < 1 / 2 := (min_le_left (1 / 4) _).trans_lt (by norm_num)
  refine ⟨H, ⟨hH0, hH1⟩, ?_⟩
  intro h hh hhH
  have hh1 : h ≤ 1 := by linarith
  have hhr : h ≤ r / 2 := hhH.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhexp : h < Real.exp (-(2 * B)) :=
    hhH.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hlog : 2 * B < Real.log (1 / h) := by
    rw [one_div, Real.log_inv]
    linarith [Real.log_lt_log hh hhexp, Real.log_exp (-(2 * B))]
  have htwo := (abs_le.mp (hcusp h hh hhr)).1
  change -(C * h ^ 2) ≤ rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0 -
    h / s * (Real.log (1 / h) + Real.log r - 2 * c) at htwo
  have hsym := mul_le_mul_of_nonneg_right htwo hs.le
  rw [sub_mul, mul_right_comm (h / s), div_mul_cancel₀ _ hs.ne'] at hsym
  have hodd := mul_le_mul_of_nonneg_right (abs_le.mp (odd_root_increment hRH hr hh.le)).1 hs.le
  change -(2 * (r - 1) * firstLiMass * h / s) * s ≤ _ at hodd
  rw [neg_mul, div_mul_cancel₀ _ hs.ne'] at hodd
  have hlin := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log r - 2 * c)) hh.le
  have hC' : C * h ^ 2 ≤ C * h := by
    nlinarith [mul_nonneg (mul_nonneg hC.le hh.le) (sub_nonneg.mpr hh1)]
  have hquad := mul_le_mul_of_nonneg_right hC' hs.le
  have hbudget := mul_lt_mul_of_pos_left hlog hh
  dsimp [B] at hbudget
  apply (div_le_iff₀ (by positivity : 0 < 4 * s)).2
  nlinarith only [hsym, hodd, hlin, hquad, hbudget]

private theorem origin_average_lower (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    ∃ H ∈ Ioo (0 : ℝ) (1 / 2), ∀ L : ℝ, 0 < L → L < H →
      Real.exp (-s) / (8 * s) * L * Real.log (1 / L) ≤
        (∫ t in (0 : ℝ)..L, Real.exp (-s * t) * rootSignal r t) /
          (∫ t in (0 : ℝ)..L, Real.exp (-s * t)) - rootSignal r 0 := by
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  have hs : 0 < s := by
    dsimp [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  obtain ⟨H, hH, hlocal⟩ := one_sided_root_lower hRH hr
  refine ⟨H, hH, ?_⟩
  intro L hL hLH
  have hL1 : L < 1 := by linarith [hH.2]
  let w := fun t : ℝ => Real.exp (-s * t)
  let F := rootSignal r
  let m := ∫ t in (0 : ℝ)..L, w t
  let a := Real.exp (-s) * Real.log (1 / L) / (4 * s)
  have ha : 0 ≤ a := by
    have hlog : 0 ≤ Real.log (1 / L) :=
      Real.log_nonneg ((le_div_iff₀ hL).2 (by linarith))
    dsimp [a]
    positivity
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hF : Continuous F := (root_signal_uniformContinuous hRH hr).continuous
  have hwinterval (t : ℝ) (ht : t ∈ Icc 0 L) : Real.exp (-s) ≤ w t ∧ w t ≤ 1 := by
    dsimp [w]
    constructor
    · apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (show t ≤ 1 by linarith [ht.2]) hs.le
      linarith
    · exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.1)
  have hm0 : 0 < m := by
    have hlow := intervalIntegral.integral_mono_on («μ» := volume) hL.le
      (continuous_const.intervalIntegrable 0 L) (hw.intervalIntegrable 0 L)
      (fun t ht => (hwinterval t ht).1)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlow
    exact (mul_pos hL (Real.exp_pos _)).trans_le hlow
  have hmL : m ≤ L := by
    have hhigh := intervalIntegral.integral_mono_on («μ» := volume) hL.le
      (hw.intervalIntegrable 0 L) (continuous_const.intervalIntegrable 0 L)
      (fun t ht => (hwinterval t ht).2)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using hhigh
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 L) : a * t ≤ w t * (F t - F 0) := by
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · simp [← ht0]
    · have hloc := hlocal t ht0 (ht.2.trans_lt hLH)
      have hlog : Real.log (1 / L) ≤ Real.log (1 / t) := by
        rw [one_div, one_div, Real.log_inv, Real.log_inv, neg_le_neg_iff]
        exact Real.log_le_log ht0 ht.2
      have hsmall : t * Real.log (1 / L) / (4 * s) ≤ F t - F 0 :=
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog ht.1) (by positivity)).trans hloc
      have hbase : 0 ≤ t * Real.log (1 / L) / (4 * s) := by
        have hlog0 : 0 ≤ Real.log (1 / L) :=
          Real.log_nonneg ((le_div_iff₀ hL).2 (by linarith))
        positivity
      calc
        a * t = Real.exp (-s) * (t * Real.log (1 / L) / (4 * s)) := by dsimp [a]; ring
        _ ≤ w t * (t * Real.log (1 / L) / (4 * s)) :=
          mul_le_mul_of_nonneg_right (hwinterval t ht).1 hbase
        _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (Real.exp_nonneg _)
  have hInt : a * L ^ 2 / 2 ≤ ∫ t in (0 : ℝ)..L, w t * (F t - F 0) := by
    have haInt : Continuous (fun t : ℝ => a * t) := continuous_const.mul continuous_id
    have hfInt : Continuous (fun t => w t * (F t - F 0)) :=
      hw.mul (hF.sub continuous_const)
    have h := intervalIntegral.integral_mono_on («μ» := volume) hL.le
      (haInt.intervalIntegrable 0 L) (hfInt.intervalIntegrable 0 L) hpoint
    rw [intervalIntegral.integral_const_mul, integral_id] at h
    simpa [mul_div_assoc] using h
  have hshift : (∫ t in (0 : ℝ)..L, w t * (F t - F 0)) =
      (∫ t in (0 : ℝ)..L, w t * F t) - m * F 0 := by
    simp_rw [mul_sub]
    have hLeft : IntervalIntegrable (fun t => w t * F t) volume 0 L :=
      (hw.mul hF).intervalIntegrable _ _
    have hRight : IntervalIntegrable (fun t => w t * F 0) volume 0 L :=
      (hw.mul continuous_const).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hLeft hRight, intervalIntegral.integral_mul_const]
  change Real.exp (-s) / (8 * s) * L * Real.log (1 / L) ≤
    (∫ t in (0 : ℝ)..L, w t * F t) / m - F 0
  rw [show (∫ t in (0 : ℝ)..L, w t * F t) / m - F 0 =
      ((∫ t in (0 : ℝ)..L, w t * F t) - m * F 0) / m by field_simp [hm0.ne']]
  apply (le_div_iff₀ hm0).2
  rw [← hshift]
  calc
    _ = (a * L / 2) * m := by
      dsimp [a]
      field_simp [hs.ne']
      ring
    _ ≤ (a * L / 2) * L := mul_le_mul_of_nonneg_left hmL (by positivity)
    _ = a * L ^ 2 / 2 := by ring
    _ ≤ _ := hInt

private theorem normalized_root_error_returns (hRH : RiemannHypothesis) {r L : ℝ}
    (hr : 1 < r) (hL : 0 < L) (U : ℝ) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    let D := fun u : ℝ =>
      (rootPrimitive r (Real.exp (u + L)) - rootPrimitive r (Real.exp u)) /
        powerGap s (Real.exp u) (Real.exp (u + L)) - rootSignal r u
    ∀ b : ℝ, b < D 0 → ∃ u ≥ U, b < D u := by
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  let D := fun u : ℝ =>
    (rootPrimitive r (Real.exp (u + L)) - rootPrimitive r (Real.exp u)) /
      powerGap s (Real.exp u) (Real.exp (u + L)) - rootSignal r u
  change ∀ b : ℝ, b < D 0 → ∃ u ≥ U, b < D u
  intro b hb
  let Q := fun p : ℕ → Circle => (∑' k, windowCoefficient r L (actualZero k) * (p k : ℂ)).re
  let S := readSignal r 0
  have hQ : Continuous Q := by
    unfold Q
    apply Complex.continuous_re.comp
    apply continuous_tsum (fun k => by fun_prop) (window_coefficients_summable hRH hr hL)
    intro k p
    simp [Circle.norm_coe]
  have hS : Continuous S := read_signal_continuous hRH hr 0
  have horbit (v : ℝ) : Q (phaseOrbit v) - S (phaseOrbit v) = D (r * v) := by
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hcast (k : ℕ) : frequency k / (r : ℂ) * ((r * v : ℝ) : ℂ) = frequency k * (v : ℂ) := by
      push_cast
      field_simp
    have hseries := congrArg Complex.re (normalized_width_series hRH hr hL (r * v))
    simp only [Complex.ofReal_re, hcast] at hseries
    have hsignal : S (phaseOrbit v) = rootSignal r (r * v) := by
      simpa only [S, add_zero] using read_signal_orbit hRH hr 0 v
    rw [hsignal]
    simp only [D, Q, s, phaseOrbit_eq_mode hRH]
    rw [hseries]
  have hreturn := (phaseOrbit_cluster_iff (phaseOrbit 0)).2 (subset_closure (mem_range_self _))
  have hzero : b < Q (phaseOrbit 0) - S (phaseOrbit 0) := by simpa [horbit] using hb
  have hf := (hreturn.continuousAt_comp (hQ.sub hS).continuousAt).frequently
    (eventually_gt_nhds hzero)
  obtain ⟨v, hv, hU⟩ := (hf.and_eventually (eventually_ge_atTop (U / r))).exists
  refine ⟨r * v, ?_, ?_⟩
  · rw [mul_comm]
    exact (div_le_iff₀ (by linarith : 0 < r)).mp hU
  · change b < Q (phaseOrbit v) - S (phaseOrbit v) at hv
    exact (horbit v) ▸ hv

/-- Under RH, the shrinking prime-window discrepancy exceeds a logarithmic scale in the direction opposite to the Möbius coefficient at arbitrarily late starts. -/
theorem signed_window_even_cutoff_shrinking_lower (hRH : RiemannHypothesis)
    (m r : ℕ) (hm : 2 ≤ m) (heven : m + 1 = 2 * r) (hmu : μ r ≠ 0) :
    let s := orderRate m
    let cₘ := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
    ∃ H ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioo 0 (Real.exp (-s) / (8 * s)),
      ∀ L : ℝ, 0 < L → L < H → ∀ U : ℝ,
      ∃ u ≥ U, d * L * Real.log (1 / L) ≤
        -(μ r : ℝ) * (signedWindowResidual m (Real.exp u) (Real.exp (u + L)) /
          powerGap s (Real.exp u) (Real.exp (u + L)) + cₘ +
          (μ r : ℝ) * rootSignal (r : ℝ) u) := by
  let s := orderRate m
  let cₘ := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
  let δ := ((m : ℝ) + 1)⁻¹ - ((m : ℝ) + 2)⁻¹
  let μr : ℝ := μ r
  have hμ_sq : μr ^ 2 = 1 := by
    rcases moebius_ne_zero_iff_eq_or.mp hmu with h | h <;> simp [μr, h]
  have hμ_le : |μr| ≤ 1 := by
    dsimp [μr]
    exact_mod_cast abs_moebius_le_one (n := r)
  have hr : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hq : (m : ℝ) + 1 = 2 * (r : ℝ) := by exact_mod_cast heven
  have hsr : s = 1 / 2 - (2 * (r : ℝ))⁻¹ := by dsimp [s, orderRate]; rw [hq]
  have hs : 0 < s := by
    rw [hsr, inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by linarith)).2 (by linarith)
  have hδ : 0 < δ := sub_pos.mpr (inv_strictAnti₀ (by positivity) (by linarith))
  obtain ⟨H, hH, havg⟩ := origin_average_lower hRH hr
  obtain ⟨_, _, hweighted⟩ := signed_window_even_cutoff_shrinking_width hRH
  obtain ⟨a₀, K, ha₂, hK, hexpansion⟩ := signed_window_even_cutoff_expansion hRH
  let W := K * (((m + 1 : ℕ) : ℝ) * (1 + Real.log ((m + 1 : ℕ) : ℝ)) ^ 2)
  let C := Real.exp (-s) / (8 * s)
  refine ⟨H, ⟨hH.1, hH.2.trans (by norm_num)⟩, ?_⟩
  intro d hd L hL hLH U
  have hdC : d < C := hd.2
  have hL1 : L < 1 := by linarith [hH.2]
  have hlog : 0 < Real.log (1 / L) := Real.log_pos ((lt_div_iff₀ hL).2 (by linarith))
  let T := L * Real.log (1 / L)
  have hT : 0 < T := mul_pos hL hlog
  let b := (C + d) / 2 * T
  let ε := (C - d) / 2 * T
  have hε : 0 < ε := mul_pos (half_pos (sub_pos.mpr hdC)) hT
  let Δ := fun u : ℝ =>
    (rootPrimitive (r : ℝ) (Real.exp (u + L)) - rootPrimitive (r : ℝ) (Real.exp u)) /
      powerGap s (Real.exp u) (Real.exp (u + L)) - rootSignal (r : ℝ) u
  have h0 : b < Δ 0 := by
    have h := havg L hL hLH
    rw [← hsr] at h
    have hweight := (hweighted m r hm heven).1 0 L hL
    dsimp only [Δ]
    rw [hweight]
    simp only [zero_add]
    calc
      b < C * T := mul_lt_mul_of_pos_right (by linarith) hT
      _ ≤ _ := by simpa only [C, T, mul_assoc] using h
  have hdecay_limit : Tendsto (fun u : ℝ => (W * ((s + δ) / s)) * Real.exp (-δ * u))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, id_eq, mul_zero, neg_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hδ)).const_mul (W * ((s + δ) / s))
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    (hdecay_limit.eventually (eventually_lt_nhds hε))
  let U' := max U (max (Real.log a₀) V)
  have h0' : b < (rootPrimitive (r : ℝ) (Real.exp (0 + L)) -
        rootPrimitive (r : ℝ) (Real.exp 0)) /
      powerGap (1 / 2 - (2 * (r : ℝ))⁻¹) (Real.exp 0) (Real.exp (0 + L)) -
        rootSignal (r : ℝ) 0 := by
    simpa only [Δ, hsr] using h0
  obtain ⟨u, hu, hΔ⟩ := normalized_root_error_returns hRH hr hL U' b h0'
  have hΔ' : b < Δ u := by simpa only [Δ, hsr] using hΔ
  have hU : U ≤ u := (le_max_left _ _).trans hu
  have hu₀ : Real.log a₀ ≤ u := ((le_max_left _ V).trans (le_max_right U _)).trans hu
  have huV : V ≤ u := ((le_max_right (Real.log a₀) _).trans (le_max_right U _)).trans hu
  let a := Real.exp u
  let B := Real.exp (u + L)
  let gap := powerGap s a B
  let P := rootPrimitive (r : ℝ) B - rootPrimitive (r : ℝ) a
  have ha₀ : 0 < a₀ := by linarith
  have hau : a₀ ≤ a := by rw [← Real.exp_log ha₀]; exact Real.exp_le_exp.mpr hu₀
  have haB : a < B := Real.exp_lt_exp.mpr (by linarith)
  have hg : 0 < gap :=
    sub_pos.mpr (Real.rpow_lt_rpow_of_neg (Real.exp_pos _) haB (neg_neg_of_pos hs))
  have hexp := hexpansion m r hm heven a B hau haB.le
  have harith : |signedWindowResidual m a B + cₘ * gap + μr * P| ≤
      (W * ((s + δ) / s)) * Real.exp (-δ * u) * gap := by
    simpa only [s, δ, cₘ, W, μr, P, gap, a, Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp, mul_comm u (-δ)] using hexp.1.trans hexp.2
  let E := signedWindowResidual m a B / gap + cₘ + μr * (P / gap)
  have hE : |E| < ε := by
    have heq : E = (signedWindowResidual m a B + cₘ * gap + μr * P) / gap := by
      dsimp only [E]
      field_simp [hg.ne']
    rw [heq, abs_div, abs_of_pos hg]
    exact ((div_le_iff₀ hg).2 harith).trans_lt (hV u huV)
  have hE_signed : -ε < -μr * E := by
    have hprod : |(-μr) * E| ≤ |E| := by
      rw [abs_mul, abs_neg]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hμ_le (abs_nonneg E)
    exact (abs_lt.mp (hprod.trans_lt hE)).1
  refine ⟨u, hU, ?_⟩
  change _ ≤ -μr * (signedWindowResidual m a B / gap + cₘ + μr * rootSignal (r : ℝ) u)
  have heq : signedWindowResidual m a B / gap + cₘ + μr * rootSignal (r : ℝ) u =
      E - μr * Δ u := by
    change _ = E - μr * (P / gap - rootSignal (r : ℝ) u)
    dsimp only [E]
    ring
  rw [heq, show -μr * (E - μr * Δ u) = -μr * E + μr ^ 2 * Δ u by ring, hμ_sq, one_mul]
  have hmargin : b - ε = d * L * Real.log (1 / L) := by dsimp only [b, ε, T]; ring
  linarith only [hΔ', hE_signed, hmargin]

#print axioms signed_window_even_cutoff_shrinking_lower

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
