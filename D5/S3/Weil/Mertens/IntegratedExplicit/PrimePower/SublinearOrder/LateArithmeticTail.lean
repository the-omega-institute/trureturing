/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/LateArithmeticTail
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/LateArithmeticTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Late-window arithmetic tail from geometric damping of the omitted degrees. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.OmittedSpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Real Finset ArithmeticFunction Chebyshev
open scoped ArithmeticFunction.Moebius
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

/-- The discarded degrees beyond twice the cutoff have a bounded exponential response. -/
theorem degree_mul_exp_neg_le_eight {q u : ℝ} (hq : 0 < q)
    (hu : q^(3/2 : ℝ) ≤ u) : q*Real.exp (-u/(2*q)) ≤ 8 := by
  have hroot : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hrad : q^(3/2 : ℝ) = q*Real.sqrt q := by
    rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add hq, Real.rpow_one]
  have hratio : Real.sqrt q/2 ≤ u/(2*q) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [hrad] at hu
    linarith only [hu]
  have hqexp : q/8 ≤ Real.exp (Real.sqrt q/2) := by
    have hs := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Real.sqrt q/2 by positivity)
    nlinarith only [hs, hroot, Real.sq_sqrt hq.le]
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith only [hqexp.trans (Real.exp_le_exp.mpr hratio)]

private theorem chebyshev_mobius_truncation_very_late :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 2 ≤ m → ∀ t ≥ (2 : ℝ),
      ((m : ℝ)+1)^(3/2 : ℝ) ≤ Real.log t →
      |theta t - psi t - ∑ n ∈ Icc 2 m, (μ n : ℝ) *
        psi (t ^ (1/(n : ℝ)))| ≤
      C*(1+((m : ℝ)+1)^2/Real.log t)*t^(1/((m : ℝ)+1)) := by
  let P := 2*(Real.log 4 + 4)
  let A := 8*(1+2/Real.log 2)
  have hP : 0 < P := by dsimp [P]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨P*(2+A), by positivity, fun m hm t ht hu => ?_⟩
  let q := m+1
  let N := 2*q-1
  let u := Real.log t
  let f (n : ℕ) := (μ n : ℝ)*psi (t^(1/(n : ℝ)))
  have hq : 0 < q := by dsimp [q]; omega
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hq' : (q : ℝ) = (m : ℝ)+1 := by simp [q]
  have hN : 2 ≤ N := by dsimp [N, q]; omega
  have hN' : (N : ℝ)+1 = 2*(q : ℝ) := by
    exact_mod_cast (show N+1 = 2*q by dsimp [N]; omega)
  have ht₀ : 0 < t := by linarith
  have hu₀ : 0 < u := Real.log_pos (by linarith)
  have hpow (p : ℝ) : t^p = Real.exp (p*u) := by
    rw [Real.rpow_def_of_pos ht₀, mul_comm]
  have hs : (∑ n ∈ Icc 2 m, f n) + (∑ n ∈ Icc q N, f n) = ∑ n ∈ Icc 2 N, f n := by
    dsimp only [q, N]
    simp only [← Ico_add_one_right_eq_Icc]
    exact sum_Ico_consecutive _ (by omega) (by omega)
  have hsplit :
      theta t - psi t - (∑ n ∈ Icc 2 m, f n) =
      (∑ n ∈ Icc q N, f n) + (theta t - psi t - ∑ n ∈ Icc 2 N, f n) := by
    rw [← hs]
    ring
  have hnear :
      (∑ n ∈ Icc q N, |f n|) ≤ P*(1+2*(q : ℝ)^2/u)*t^(1/(q : ℝ)) := by
    have hsub : Icc q N ⊆ Icc q (2*q) := Icc_subset_Icc_right (by dsimp [N]; omega)
    let w (n : ℕ) := Real.exp (-(2*(2*u)/((2*q : ℕ) : ℝ) - (2*u)/(n : ℝ))/2)
    have wnon (n : ℕ) : 0 ≤ w n := Real.exp_nonneg _
    have hsum := weighted_omitted_degree_sum_le (p := q) (q := 2*q) hq
      (by omega) (by omega) (u := 2*u) (by positivity)
    have hsum' : ∑ n ∈ Icc q (2*q), w n ≤ 1+2*(q : ℝ)^2/u := by
      exact hsum.trans_eq (by push_cast; ring)
    calc
      _ ≤ ∑ n ∈ Icc q N, (P*t^(1/(q : ℝ))) * w n := by
        apply sum_le_sum
        intro n hn
        have hn₀ : (0 : ℝ) < n := by exact_mod_cast hq.trans_le (mem_Icc.mp hn).1
        have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
        have hpsi : 0 ≤ psi (t^(1/(n : ℝ))) := psi_nonneg _
        dsimp only [f]
        rw [abs_mul, abs_of_nonneg hpsi]
        refine (mul_le_of_le_one_left hpsi hμ).trans ?_
        have htpos : 0 ≤ t^(1/(n : ℝ)) := by positivity
        refine (psi_le_const_mul_self htpos).trans ?_
        have hconst : Real.log 4 + 4 ≤ P := by dsimp only [P]; linarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
        have hw : t^(1/(n : ℝ)) = t^(1/(q : ℝ))*w n := by
          dsimp only [w]
          rw [hpow, hpow, ← Real.exp_add]
          congr 1
          push_cast
          field_simp
          ring
        exact (mul_le_mul_of_nonneg_right hconst htpos).trans_eq (by rw [hw]; ring)
      _ ≤ (P * t^(1/(q : ℝ))) * (1+2*(q : ℝ)^2/u) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left
          ((sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => wnon n)).trans hsum')
          (by positivity)
      _ = _ := by ring
  have hfar :
      |theta t - psi t - ∑ n ∈ Icc 2 N, f n| ≤ P*A*t^(1/(q : ℝ)) := by
    have h := chebyshev_mobius_truncation ht hN
    have hexp : (q : ℝ)*Real.exp (-u/(2*(q : ℝ))) ≤ 8 :=
      degree_mul_exp_neg_le_eight hqr (by simpa only [hq', u] using hu)
    have hfactor : t^(1/((N : ℝ)+1)) =
        t^(1/(q : ℝ))*Real.exp (-u/(2*(q : ℝ))) := by
      rw [hN', hpow, hpow, ← Real.exp_add]
      congr 1
      field_simp
      ring
    have hc : (1+((N : ℝ)+1)/Real.log 2) ≤ (1+2/Real.log 2)*(q : ℝ) := by
      rw [hN']
      rw [show (1+2/Real.log 2)*(q : ℝ) = q+2*(q : ℝ)/Real.log 2 by ring]
      gcongr
    change |theta t - psi t - ∑ n ∈ Icc 2 N, f n| ≤ _ at h ⊢
    refine h.trans ?_
    rw [hfactor]
    calc
      _ ≤ P*((1+2/Real.log 2)*(q : ℝ)) *
          (t^(1/(q : ℝ))*Real.exp (-u/(2*(q : ℝ)))) := by
        rw [show (Real.log 4 + 4)*2 = P by dsimp [P]; ring]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hP.le) (by positivity)
      _ = (P*(1+2/Real.log 2)*t^(1/(q : ℝ))) *
          ((q : ℝ)*Real.exp (-u/(2*(q : ℝ)))) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hexp (by positivity)).trans_eq (by dsimp [A]; ring)
  rw [← hq']
  change |theta t - psi t - (∑ n ∈ Icc 2 m, f n)| ≤ _
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ((abs_sum_le_sum_abs _ _).trans hnear) hfar) |>.trans ?_
  have hz : 0 ≤ (q : ℝ)^2/u := by positivity
  have hc : (1+2*(q : ℝ)^2/u)+A ≤ (2+A)*(1+(q : ℝ)^2/u) := by
    calc
      _ ≤ ((1+2*(q : ℝ)^2/u)+A) + (1+A*((q : ℝ)^2/u)) :=
        le_add_of_nonneg_right (add_nonneg zero_le_one (mul_nonneg hA hz))
      _ = _ := by ring
  calc
    _ = P*((1+2*(q : ℝ)^2/u)+A)*t^(1/(q : ℝ)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hP.le) (by positivity)).trans_eq
      (by dsimp only [u]; ring)

open MeasureTheory
open Set (Ioi)
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)

/-- A late logarithmic coordinate gives a geometric budget for the arithmetic tail. -/
theorem normalized_mobius_tail_of_very_late :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 2 ≤ m → ∀ u : ℝ, 2 ≤ Real.exp u → ((m : ℝ)+1)^(3/2 : ℝ) ≤ u →
      |Real.sqrt (Real.exp u) * (primeTail (Real.exp u) - Q (Real.exp u)) -
        ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (Real.sqrt (Real.exp u) *
          (∫ t in Ioi (Real.exp u), psi (t ^ (n : ℝ)⁻¹) / t ^ 2))| ≤
      C * (1+((m : ℝ)+1)^2/u) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨A, hA, htail⟩ := chebyshev_mobius_truncation_very_late
  refine ⟨2*A, by positivity, fun m hm u hx hu => ?_⟩
  let q := (m : ℝ)+1
  let x := Real.exp u
  let C := A*(1+q^2/u)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : (1 : ℝ) ≤ q := by dsimp [q]; linarith
  have hq₀ := zero_lt_one.trans_le hq
  have hu₀ : 0 < u := (Real.rpow_pos_of_pos hq₀ _).trans_le hu
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (t : ℝ) (ht : x < t) :
      |theta t - psi t - ∑ n ∈ Icc 2 m, (μ n : ℝ)*psi (t^(1/(n : ℝ)))| ≤
        C*t^(1/q) := by
    have htu : u ≤ Real.log t := by
      simpa only [x, Real.log_exp] using Real.log_le_log (Real.exp_pos u) ht.le
    have h := htail m hm t (hx.trans ht.le) (hu.trans htu)
    refine h.trans ?_
    have ht₀ : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 2) (hx.trans ht.le)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA.le)
      (Real.rpow_nonneg ht₀ _)
    exact add_le_add le_rfl (div_le_div_of_nonneg_left (sq_nonneg q) hu₀ htu)
  have h := integrated_mobius_of_pointwise hm hx hbound
  have hp : 1/2 ≤ 1-1/q := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ q by dsimp [q]; linarith)
    linarith only [hh]
  have hC' : C / (1-q⁻¹) ≤ 2*C := by
    have hp' : 1/2 ≤ 1-q⁻¹ := by simpa only [one_div] using hp
    apply (div_le_iff₀ (by linarith)).mpr
    have hm := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 2*C by positivity)
    linarith only [hm]
  rw [mul_sub, Finset.mul_sum] at h
  simp only [one_div] at h
  have hpower : x^(q⁻¹-1/2) = Real.exp (-(orderRate m)*u) := by
    dsimp only [x, q, orderRate]
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [show (2 : ℝ)⁻¹ = 1/2 by norm_num] at h
  have h' := h.trans (mul_le_mul_of_nonneg_right hC' (by positivity))
  change _ ≤ 2*C*x^(q⁻¹-1/2) at h'
  rw [hpower] at h'
  simpa only [C, q, mul_assoc, mul_left_comm (Real.sqrt (Real.exp u))] using h'

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
