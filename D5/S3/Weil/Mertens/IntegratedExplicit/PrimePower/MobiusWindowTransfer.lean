/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusWindowTransfer
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusWindowTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transfer of a Möbius log-density estimate to the original prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum

/-! Transfer pointwise prime-tail density bounds to actual endpoint windows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real ArithmeticFunction MeasureTheory Set
open scoped ArithmeticFunction.Moebius
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
  (windowError normalizedMass normalizedZeroSeries)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (prime_window_remainder_of_rh spectralPrimitive windowDiscrepancy)

/-- Integrate a uniform log-density estimate on the actual prime-only window. -/
theorem prime_window_of_density_bound (hRH : RiemannHypothesis)
    (factor : ℕ → ℝ) (hfactor : ∀ m : ℕ, 2 ≤ m → 0 ≤ factor m)
    (retained : ℕ → ℕ → ℝ → ℝ)
    (hterm : ∀ (m n : ℕ), 2 ≤ n → ∀ {a B : ℝ}, 0 < a → 0 < B →
      IntervalIntegrable (retained m n) volume (Real.log a) (Real.log B) ∧
      (∫ u in Real.log a..Real.log B, retained m n u) =
        (if n = 2 then 2 * (Real.log B - Real.log a) else
          -(μ n : ℝ) * (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
            (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) +
        (if 2 * n < m + 1 then
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a) else 0))
    {K : ℝ} (hK : 0 < K)
    (hD : ∀ (m : ℕ), 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retained m n u) - 2)| ≤
        K * factor m * Real.exp (-(1 / 2 - (m + 1 : ℝ)⁻¹) * u)) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * factor m *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (late_strict_prime_tail hRH)
  refine ⟨max T 2, 6 * K, le_max_right _ _, by positivity, ?_⟩
  intro m hm a B ha hab
  let rate := 1 / 2 - (m + 1 : ℝ)⁻¹
  have h_order : -rate = (m + 1 : ℝ)⁻¹ - 1 / 2 := neg_sub ..
  rw [← h_order]
  have ha₂ := (le_max_right T (2 : ℝ)).trans ha
  have ha₀ : 0 < a := by linarith
  have hB₀ := ha₀.trans_le hab
  have hlog := Real.log_le_log ha₀ hab
  have hlog₂ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ha₂
  have hr : 1 / 6 ≤ rate := by
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have h := inv_anti₀ (show (0 : ℝ) < 3 by norm_num)
      (show (3 : ℝ) ≤ (m + 1 : ℝ) by linarith)
    dsimp only [rate]
    norm_num at h
    linarith
  have hr₀ : 0 < rate := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hr
  have Hwin : (∫ u in Real.log a..Real.log B, windowError u) =
      ∫ u in Real.log a..Real.log B, rootWindowDensity u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hlog] at hu
    have hx : a ≤ Real.exp u := by simpa only [Real.exp_log ha₀] using Real.exp_le_exp.mpr hu.1
    have hpos := hT _ ((le_max_left T 2).trans (ha.trans hx))
    have hscaled := complete_scaled (x := Real.exp u) (ha₂.trans hx)
    rw [Real.log_exp] at hscaled
    rw [windowError, normalizedMass, normalizedZeroSeries, max_eq_left hpos.le,
      rootWindowDensity, Complex.re_ofReal_mul, hscaled]
    ring
  let arithmetic (n : ℕ) (x y : ℝ) := -(μ n : ℝ) *
    (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
    (x ^ ((n : ℝ)⁻¹ - 1 / 2) - y ^ ((n : ℝ)⁻¹ - 1 / 2))
  let captured (m n : ℕ) (x y : ℝ) := if 2 * n < m + 1 then
    -(μ n : ℝ) * (rootPrimitive (n : ℝ) y - rootPrimitive (n : ℝ) x) else 0
  let f (u : ℝ) := ∑ n ∈ Finset.Icc 2 m, retained m n u
  let e (u : ℝ) := rootWindowDensity u - (f u - 2)
  let w (u : ℝ) := K * factor m * Real.exp (-(rate) * u)
  have hi : IntervalIntegrable rootWindowDensity volume (Real.log a) (Real.log B) :=
    (rootWindowDensity_continuousOn.mono (by
      rw [uIcc_of_le hlog]
      exact fun _ hu => hlog₂.trans hu.1)).intervalIntegrable
  have hfi : IntervalIntegrable f volume (Real.log a) (Real.log B) := by
    have hf : f = ∑ n ∈ Finset.Icc 2 m, retained m n := by
      funext u
      simp [f, Finset.sum_apply]
    rw [hf]
    exact IntervalIntegrable.sum (f := retained m) (Finset.Icc 2 m) (fun n hn =>
      (hterm m n (Finset.mem_Icc.mp hn).1 ha₀ hB₀).1)
  have hc : IntervalIntegrable (fun _ : ℝ => (2 : ℝ)) volume (Real.log a) (Real.log B) :=
    intervalIntegrable_const
  have hei : IntervalIntegrable e volume (Real.log a) (Real.log B) := hi.sub (hfi.sub hc)
  have hwi : IntervalIntegrable w volume (Real.log a) (Real.log B) :=
    (by unfold w; fun_prop : Continuous w).intervalIntegrable _ _
  have hmono : |∫ u in Real.log a..Real.log B, e u| ≤ ∫ u in Real.log a..Real.log B, w u :=
    (intervalIntegral.abs_integral_le_integral_abs hlog).trans
      (intervalIntegral.integral_mono_on hlog hei.abs hwi
        (fun u hu => hD m hm u (hlog₂.trans hu.1)))
  have Hf : (∫ u in Real.log a..Real.log B, f u) =
      2 * (Real.log B - Real.log a) +
        (∑ n ∈ Finset.Icc 3 m, arithmetic n a B) +
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a)) := by
    unfold f
    rw [intervalIntegral.integral_finsetSum fun n hn =>
      (hterm m n (Finset.mem_Icc.mp hn).1 ha₀ hB₀).1]
    calc
      _ = ∑ n ∈ Finset.Icc 2 m,
          ((if n = 2 then 2 * (Real.log B - Real.log a) else arithmetic n a B) +
            captured m n a B) :=
        Finset.sum_congr rfl fun n hn =>
          (hterm m n (Finset.mem_Icc.mp hn).1 ha₀ hB₀).2
      _ = _ := by
        rw [Finset.sum_add_distrib]
        have hs : Finset.Icc 2 m = insert 2 (Finset.Icc 3 m) := by
          ext n
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hmain :
            (∑ n ∈ Finset.Icc 2 m,
              if n = 2 then 2 * (Real.log B - Real.log a) else arithmetic n a B) =
              2 * (Real.log B - Real.log a) + ∑ n ∈ Finset.Icc 3 m, arithmetic n a B := by
          rw [hs, Finset.sum_insert (by simp)]
          congr 1
          refine Finset.sum_congr rfl fun n hn => ite_eq_right ?_
          have hn3 := (Finset.mem_Icc.mp hn).1
          omega
        rw [hmain, Finset.sum_filter]
  have hw : (∫ u in Real.log a..Real.log B, w u) =
      K * factor m * ((a ^ (-rate) - B ^ (-rate)) / rate) := by
    unfold w
    rw [intervalIntegral.integral_const_mul, exp_decay_integral hr₀]
    have hrpow {x : ℝ} (hx : 0 < x) (r : ℝ) : Real.exp (-r * Real.log x) = x ^ (-r) := by
      rw [Real.rpow_def_of_pos hx, mul_comm]
    rw [hrpow ha₀, hrpow hB₀]
  have hgap : 0 ≤ (a ^ (-rate) - B ^ (-rate)) :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos ha₀ hab (neg_nonpos.mpr hr₀.le))
  have hdiv : (a ^ (-rate) - B ^ (-rate)) / rate ≤ 6 * (a ^ (-rate) - B ^ (-rate)) := by
    apply (div_le_iff₀ hr₀).mpr
    nlinarith only [mul_nonneg hgap (show 0 ≤ 6 * rate - 1 by linarith)]
  rw [(prime_window_remainder_of_rh hRH).2.2 a B ha₂ hab, Hwin]
  have hle : (∫ u in Real.log a..Real.log B, w u) ≤
      6 * K * factor m * (a ^ (-rate) - B ^ (-rate)) := by
    rw [hw]
    exact (mul_le_mul_of_nonneg_left hdiv (mul_nonneg hK.le (hfactor m hm))).trans_eq (by ring)
  refine (?_ : _ ≤ ∫ u in Real.log a..Real.log B, w u).trans hle
  dsimp only [e] at hmono
  rw [intervalIntegral.integral_sub hi (hfi.sub hc), intervalIntegral.integral_sub hfi hc, Hf,
    intervalIntegral.integral_const, smul_eq_mul] at hmono
  convert hmono using 1
  congr 1
  ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
