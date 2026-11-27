import D5.S3.Analytic.Oscillation.MontgomeryWindow
import D5.S3.Fourier.Concentration.CauchyPairEnergy
import D5.S3.Analytic.Asymptotics.DirichletPolynomialMeanSquare

/-! A Cauchy lower bound for the normalized Montgomery pair sum. -/

open Filter Set
open scoped Topology ComplexConjugate

namespace D5.S3.Analytic.Oscillation.MontgomeryCauchyDeficit

open OrdinateCounting MontgomeryWindow
open D5.S3.Fourier.Concentration.CauchyPairEnergy
open D5.S3.Weil.DirichletPolynomialMeanSquare (phase norm_phase)

private theorem peak_lower (S : Spectrum) {Y R : ℝ} (hY : 1 < Y) (hR : 0 < R) (t : ℝ) :
    (2 * Real.pi) / (Y + 2 * R) *
      max (‖∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) t‖ -
        (2 / (Real.pi * R)) * (S.N Y : ℝ)) 0 ^ 2 ≤
      Y * Real.log Y / (2 * Real.pi) * montgomery S (t / Real.log Y) Y := by
  let a (j : S.index) : ℂ := (S.mult j : ℂ) * phase (S.gamma j) t
  have H := lorentz_pair_lower_bound (S.cut Y) S.gamma a (R := R)
    (Y := Y) (by linarith) (fun j hj => ⟨(S.gamma_pos j).le, (S.finite_le Y).mem_toFinset.mp hj⟩)
    hR
  have hnorm : (∑ j ∈ S.cut Y, ‖a j‖) = (S.N Y : ℝ) := by
    rw [Spectrum.N, Nat.cast_sum]
    simp [a, norm_phase]
  rw [hnorm] at H
  refine H.trans_eq ?_
  rw [← montgomery_normalization S hY t]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hphase : phase (S.gamma i) t * conj (phase (S.gamma j) t) =
      phase (S.gamma i - S.gamma j) t := by
    unfold phase
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have ha : a i * conj (a j) =
      (((S.mult i : ℝ) * S.mult j : ℝ) : ℂ) * phase (S.gamma i - S.gamma j) t := by
    rw [Complex.ofReal_mul, ← hphase]
    simp only [a, map_mul, Complex.conj_natCast, Complex.ofReal_natCast]
    ring
  rw [ha, Complex.re_ofReal_mul]
  simp only [pairCos, phase]
  rw [show (↑(S.gamma i - S.gamma j : ℝ) : ℂ) * Complex.I * (t : ℂ) =
    ((S.gamma i - S.gamma j) * t : ℝ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]
  ring

/-- A fixed pair-sum cap below the Cauchy energy of full alignment enforces a phase deficit. -/
theorem fractional_deficit_of_cauchy_cap (S : Spectrum) (hN : CountAsymptotic S)
    {κ : ℝ} (hκ : 0 < κ) (hκmax : κ < 2 * Real.pi * (1 / (2 * Real.pi)) ^ 2)
    (hcap : ∀ A > (1 : ℝ), ∀ᶠ Y : ℝ in atTop,
      ∀ t : ℝ, Real.log Y ≤ |t| → |t| ≤ A * Real.log Y →
        Y * Real.log Y / (2 * Real.pi) * montgomery S (t / Real.log Y) Y ≤
          κ * Y * (Real.log Y) ^ 2) :
    ∃ d > (0 : ℝ), ∀ A > (1 : ℝ), ∀ᶠ Y : ℝ in atTop,
      ∀ t : ℝ, Real.log Y ≤ |t| → |t| ≤ A * Real.log Y →
        d * (S.N Y : ℝ) ≤ (S.N Y : ℝ) -
          ‖∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) t‖ := by
  let c : ℝ := 1 / (2 * Real.pi)
  let π₂ : ℝ := 2 * Real.pi
  have hπ₂ : 0 < π₂ := by dsimp [π₂]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  change κ < π₂ * c ^ 2 at hκmax
  let ε : ℝ := (π₂ * c ^ 2 - κ) / (4 * κ)
  have hε : 0 < ε := div_pos (sub_pos.mpr hκmax) (by positivity)
  let K : ℝ := (1 + 2 * ε) / π₂ * κ
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKc : K < c ^ 2 := by
    dsimp only [K]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hπ₂]
    have hεeq : 4 * κ * ε = π₂ * c ^ 2 - κ := by
      dsimp only [ε]
      field_simp [hκ.ne']
    nlinarith only [hεeq, hκmax]
  let q : ℝ := (1 + Real.sqrt K / c) / 2
  have hq₀ : 0 < q := by dsimp [q]; positivity
  have hroot : Real.sqrt K < c := by
    by_contra! hn
    have hh := pow_le_pow_left₀ hc.le hn 2
    rw [Real.sq_sqrt hK.le] at hh
    linarith
  have hratio : Real.sqrt K / c < 1 := (div_lt_one hc).mpr hroot
  have hq₁ : q < 1 := by dsimp only [q]; linarith
  have hqK : K < (q * c) ^ 2 := by
    have H : Real.sqrt K < q * c := by
      apply (div_lt_iff₀ hc).mp
      dsimp only [q]
      linarith
    have hh := pow_lt_pow_left₀ H (Real.sqrt_nonneg K) (by decide : 2 ≠ 0)
    rwa [Real.sq_sqrt hK.le] at hh
  let d := (1 - q) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hb : Tendsto (fun Y : ℝ => (q * ((S.N Y : ℝ) / (Y * Real.log Y))) ^ 2)
      atTop (𝓝 ((q * c) ^ 2)) := (hN.const_mul q).pow 2
  have htail : Tendsto (fun Y : ℝ => 2 / (Real.pi * (ε * Y))) atTop (𝓝 0) := by
    have H := tendsto_inv_atTop_zero.const_mul (2 / (Real.pi * ε))
    convert H using 1
    · funext Y
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · rw [mul_zero]
  refine ⟨d, hd, fun A hA => ?_⟩
  filter_upwards [hcap A hA, hb.eventually_const_lt hqK, htail.eventually_lt_const hd,
    eventually_gt_atTop (1 : ℝ)] with Y hGY hbig hloss hY
  intro t htl htu
  have hY₀ : 0 < Y := by linarith
  have hYlog : 0 < Y * Real.log Y := mul_pos hY₀ (Real.log_pos hY)
  let N : ℝ := S.N Y
  let B : ℝ := ‖∑ j ∈ S.cut Y, (S.mult j : ℂ) * phase (S.gamma j) t‖
  let e := 2 / (Real.pi * (ε * Y))
  let M := max (B - e * N) 0
  have hN₀ : 0 ≤ N := Nat.cast_nonneg _
  have hpeak : π₂ / (Y + 2 * (ε * Y)) * M ^ 2 ≤ κ * Y * (Real.log Y) ^ 2 :=
    (peak_lower S hY (mul_pos hε hY₀) t).trans (hGY t htl htu)
  have hM : M ^ 2 ≤ K * (Y * Real.log Y) ^ 2 := by
    have hv : 0 < Y + 2 * (ε * Y) := by positivity
    have hm := (div_le_iff₀ hv).mp (by simpa only [div_mul_eq_mul_div] using hpeak)
    have hbound : M ^ 2 * π₂ ≤ (K * (Y * Real.log Y) ^ 2) * π₂ := by
      calc
        M ^ 2 * π₂ ≤ (κ * Y * Real.log Y ^ 2) * (Y + 2 * (ε * Y)) := by
          simpa only [mul_comm (M ^ 2) π₂] using hm
        _ = (K * (Y * Real.log Y) ^ 2) * π₂ := by
          dsimp only [K]
          field_simp [hπ₂.ne']
          <;> ring
    apply (mul_le_mul_iff_right₀ hπ₂).mp
    simpa only [mul_comm π₂] using hbound
  have hscale : K * (Y * Real.log Y) ^ 2 ≤ (q * N) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hbig.le (sq_nonneg (Y * Real.log Y))
    change K * (Y * Real.log Y) ^ 2 ≤
      (q * (N / (Y * Real.log Y))) ^ 2 * (Y * Real.log Y) ^ 2 at hm
    simpa only [← mul_pow, mul_assoc, div_mul_cancel₀ _ hYlog.ne'] using hm
  have hB : B - e * N ≤ q * N := (le_max_left _ _).trans
    (le_of_sq_le_sq (hM.trans hscale) (mul_nonneg hq₀.le hN₀))
  have he : e * N ≤ d * N := mul_le_mul_of_nonneg_right hloss.le hN₀
  change d * N ≤ N - B
  dsimp only [d] at he ⊢
  linarith

end D5.S3.Analytic.Oscillation.MontgomeryCauchyDeficit
