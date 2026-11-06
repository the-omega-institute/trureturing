/- GID: D5/S3/Arith/Robin/ForwardKernel/MellinPolynomialGrowth
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MellinPolynomialGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Von Koch control gives a common holomorphic Mellin remainder with quadratic strip growth. -/

import D5.S3.Arith.Robin.ForwardKernel.MellinResidue
import D5.S3.Arith.Robin.ForwardKernel.StripAsymptotic

namespace D5.S3.Arith.Robin.ForwardKernel.MellinPolynomialGrowth

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology
open ForwardKernel.Asymptotic ForwardKernel.FiniteMellin ForwardKernel.MellinResidue
open ForwardKernel.MellinConvergence (forwardMellin discrepancy_measurable error_power_bound)
open ActualVonMangoldtBandCompensation (discrepancy)
open OriginalMovingWindowMoment (endpoint)

/-- Von Koch's square-root error bound with two logarithmic factors. -/
def VonKochBound : Prop :=
  ∃ C t0 : ℝ, 0 ≤ C ∧ 3 ≤ t0 ∧ ∀ t : ℝ, t0 ≤ t →
    |Chebyshev.psi t - t| ≤ C * Real.sqrt t * (Real.log t) ^ 2

lemma vonKoch_power_bound (hVK : VonKochBound) {ε : ℝ} (hε : 0 < ε) :
    ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (1 / 2 + ε) := by
  obtain ⟨C, t0, hC, ht0, hVK⟩ := hVK
  refine ⟨C / (ε / 2) ^ 2, t0, ?_⟩
  intro t ht
  have htpos : 0 < t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_rpow_div htpos.le (show 0 < ε / 2 by linarith)
  have hsq : (Real.log t) ^ 2 ≤ (t ^ (ε / 2) / (ε / 2)) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog 2
  calc
    _ ≤ C * Real.sqrt t * (t ^ (ε / 2) / (ε / 2)) ^ 2 :=
      (hVK t ht).trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    _ = _ := by
      rw [Real.sqrt_eq_rpow, div_pow, ← Real.rpow_mul_natCast htpos.le]
      norm_num only [Nat.cast_ofNat]
      rw [show ε / 2 * (2 : ℝ) = ε by ring, Real.rpow_add htpos]
      ring

private lemma cpow_strip_le_one {x : ℝ} (hx : 1 ≤ x) {w : ℂ} (hw : w.re ≤ 0) :
    ‖(x : ℂ) ^ w‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one hx hw

private lemma compact_mellin_strip_bound {a b : ℝ} (ha : 1 ≤ a) {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) {s : ℂ} (hs : -(1 / 5 : ℝ) ≤ s.re) :
    ‖∫ x in Icc a b, f x * (x : ℂ) ^ (-s - 1)‖ ≤ ∫ x in Icc a b, ‖f x‖ := by
  apply norm_integral_le_of_norm_le hf.norm
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  apply cpow_strip_le_one (ha.trans hx.1)
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  linarith

private lemma adjointKernel_strip_bound {x0 b t : ℝ} (hx0 : 4 ≤ x0)
    (hxb : x0 ≤ b) (htb : t ≤ b) {s : ℂ} (hs : -(1 / 5 : ℝ) ≤ s.re) :
    ‖ForwardKernel.Adjoint.adjointKernel x0 s t‖ ≤ volume.real (Icc x0 b) := by
  rw [adjointKernel_eq_fixed hxb htb]
  suffices ‖∫ x in Icc x0 b, (x : ℂ) ^ (-s - 1) *
      (OriginalMovingWindowMoment.kernel x t : ℂ)‖ ≤ 1 * volume.real (Icc x0 b) by
    simpa only [one_mul] using this
  apply norm_setIntegral_le_of_norm_le_const (by simp)
  intro x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (OriginalMovingCutRow.kernel_nonneg (hx0.trans hx.1))]
  have hp : ‖(x : ℂ) ^ (-s - 1)‖ ≤ 1 := by
    apply cpow_strip_le_one (by linarith [hx.1])
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  exact (mul_le_mul hp (OriginalMovingCutRow.kernel_le_one (hx0.trans hx.1))
    (OriginalMovingCutRow.kernel_nonneg (hx0.trans hx.1)) zero_le_one).trans (by norm_num)

private lemma finiteCorrection_strip_bound {x0 b : ℝ} (hx0 : 4 ≤ x0) (hxb : x0 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -(1 / 5 : ℝ) ≤ s.re → ‖finiteCorrection x0 b s‖ ≤ C := by
  let B := volume.real (Icc x0 b)
  let V := volume.real (Icc (1 : ℝ) b)
  let A := ∑ n ∈ Finset.Icc 0 ⌊b⌋₊, ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (B + 1)
  refine ⟨A + (B + 1) * V, by dsimp [A, B, V]; positivity, ?_⟩
  intro s hs
  have hpr (t : ℝ) (ht : 1 ≤ t) : ‖(1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2)‖ ≤ 1 := by
    rw [norm_mul]
    have h := cpow_strip_le_one ht (w := -s - 1 / 2) (by
      norm_num
      linarith)
    calc
      _ ≤ ‖(1 / 2 : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ ≤ 1 := by norm_num
  have hq (t : ℝ) (ht : t ≤ b) : ‖ForwardKernel.Adjoint.adjointKernel x0 s t‖ ≤ B :=
    adjointKernel_strip_bound hx0 hxb ht hs
  have hsum : ‖∑ n ∈ Finset.Icc 0 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
      (ForwardKernel.Adjoint.adjointKernel x0 s n -
        (1 / 2 : ℂ) * (n : ℂ) ^ (-s - 1 / 2))‖ ≤ A := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hnb : (n : ℝ) ≤ b := (Nat.floor_le (by linarith : 0 ≤ b)) |>.trans' (by
        exact_mod_cast (Finset.mem_Icc.mp hn).2)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
        (add_le_add (hq n hnb) (hpr n hn1))) (norm_nonneg _)
  have hqi : ‖∫ t in Icc (1 : ℝ) b, ForwardKernel.Adjoint.adjointKernel x0 s t‖ ≤ B * V :=
    norm_setIntegral_le_of_norm_le_const (by simp) (fun t ht => hq t ht.2)
  have hpi : ‖∫ t in Icc (1 : ℝ) b, (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2)‖ ≤ V := by
    simpa only [one_mul] using norm_setIntegral_le_of_norm_le_const (by simp)
      (fun t (ht : t ∈ Icc (1 : ℝ) b) => hpr t ht.1)
  exact (norm_sub_le _ _).trans (by
    have h := (norm_sub_le _ _).trans (add_le_add hqi hpi)
    change _ ≤ A + (B + 1) * V
    nlinarith)

private lemma parameter_strip_bound {s : ℂ} (hs : -(1 / 5 : ℝ) ≤ s.re)
    (hs1 : s.re ≤ 1) : 1 + ‖s‖ ≤ 2 * (1 + |s.im|) := by
  have hre : |s.re| ≤ 1 := abs_le.mpr ⟨by linarith, hs1⟩
  have hn := Complex.norm_le_abs_re_add_abs_im s
  linarith [abs_nonneg s.im]

private lemma tail_strip_bound (hVK : VonKochBound) {a : ℝ} (ha : 8 < a)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -(1 / 5 : ℝ) + δ ≤ s.re → s.re ≤ 1 →
      ‖∫ t in Ioi a, (discrepancy t : ℂ) * deriv (fun y => adjointRemainder y s) t‖ ≤
        C * (1 + |s.im|) ^ 2 := by
  obtain ⟨E, hE0, hE⟩ := error_power_bound
    (show 0 ≤ (1 / 2 : ℝ) + δ / 2 by linarith)
    (vonKoch_power_bound hVK (show 0 < δ / 2 by linarith))
  obtain ⟨B, hB, hb⟩ := ForwardKernel.StripAsymptotic.adjointRemainder_strip_C1_bounds
  let p : ℝ := -1 - δ / 2
  have hi : IntegrableOn (fun t : ℝ => t ^ p) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by dsimp [p]; linarith) (by linarith)
  let J : ℝ := ∫ t in Ioi a, t ^ p
  have hJ : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi (fun t ht => by
    have ht' : a < t := ht
    exact Real.rpow_nonneg (by linarith) p)
  refine ⟨4 * E * B * J, by positivity, ?_⟩
  intro s hs hs1
  have hs0 : -(1 / 5 : ℝ) ≤ s.re := by linarith
  have hn := parameter_strip_bound hs0 hs1
  have hnorm : (1 + ‖s‖) ^ 2 ≤ 4 * (1 + |s.im|) ^ 2 := by
    nlinarith [sq_nonneg (1 + |s.im|), norm_nonneg s]
  have hdom : ∀ᵐ t : ℝ ∂volume.restrict (Ioi a),
      ‖(discrepancy t : ℂ) * deriv (fun y => adjointRemainder y s) t‖ ≤
        (E * B * (1 + ‖s‖) ^ 2) * t ^ p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change a < t at ht
    have ht0 : 0 < t := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (E * t ^ (1 / 2 + δ / 2)) *
          (B * (1 + ‖s‖) ^ 2 * t ^ (-s.re - 17 / 10)) := by
        gcongr
        · exact hE t (by linarith [ht])
        · exact (hb s hs0 hs1 t (ha.trans ht)).2
      _ = (E * B * (1 + ‖s‖) ^ 2) * t ^ (1 / 2 + δ / 2 - s.re - 17 / 10) := by
        conv_rhs =>
          rw [show (1 / 2 : ℝ) + δ / 2 - s.re - 17 / 10 =
            (1 / 2 + δ / 2) + (-s.re - 17 / 10) by ring, Real.rpow_add ht0]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ t)
        dsimp [p]
        linarith
  have hint := norm_integral_le_of_norm_le
    (hi.const_mul (E * B * (1 + ‖s‖) ^ 2)) hdom
  rw [integral_const_mul] at hint
  change _ ≤ (E * B * (1 + ‖s‖) ^ 2) * J at hint
  apply hint.trans
  calc
    _ ≤ (E * B * (4 * (1 + |s.im|) ^ 2)) * J := by gcongr
    _ = _ := by ring

/-- One explicit remainder is holomorphic on the enlarged half-plane and has quadratic
vertical growth on every closed strip strictly inside it. -/
theorem forward_kernel_mellin_polynomial_remainder (hVK : VonKochBound) {x0 : ℝ} (hx0 : 3 ≤ x0) :
    ∃ R : ℂ → ℂ,
      DifferentiableOn ℂ R {s : ℂ | -(1 / 5 : ℝ) < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        forwardMellin x0 s =
          -(1 / 2 : ℂ) * (deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2)) -
            1 / (2 * (s - 1 / 2)) + R s) ∧
      (∀ δ : ℝ, 0 < δ → δ < 1 / 5 →
        ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(1 / 5 : ℝ) + δ ≤ s.re → s.re ≤ 1 →
          ‖R s‖ ≤ C * (1 + |s.im|) ^ 2) := by
  have hE := vonKoch_power_bound hVK (show (0 : ℝ) < 1 / 4 by norm_num)
  have hbase := forward_kernel_mellin_explicit_remainder (show 0 ≤ (1 / 2 : ℝ) + 1 / 4 by norm_num) hE hx0
  refine ⟨explicitRemainder x0, ?_, ?_, ?_⟩
  · intro s hs
    change -(1 / 5 : ℝ) < s.re at hs
    let ε : ℝ := (s.re + 1 / 5) / 2
    have hε : 0 < ε := by dsimp [ε]; change -(1 / 5 : ℝ) < s.re at hs; linarith
    have hh := (forward_kernel_mellin_explicit_remainder
      (show 0 ≤ (1 / 2 : ℝ) + ε by linarith)
      (vonKoch_power_bound hVK hε) hx0).1
    have hm : (1 / 2 : ℝ) + ε - 7 / 10 < s.re := by dsimp [ε]; linarith
    exact (hh.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hm)).differentiableWithinAt
  · intro s hs
    exact hbase.2 s (by norm_num; exact hs)
  · intro δ hδ hδ1
    let y : ℝ := max 4 x0
    let a : ℝ := max 9 (endpoint y)
    have hy : 4 ≤ y := le_max_left _ _
    have ha : 8 < a := lt_of_lt_of_le (by norm_num : (8 : ℝ) < 9) (le_max_left _ _)
    have hya : y ≤ a :=
      (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith : 0 ≤ y) _)).trans (le_max_right _ _)
    obtain ⟨F, hF0, hF⟩ := finiteCorrection_strip_bound hy hya
    obtain ⟨B, hB, hb⟩ := ForwardKernel.StripAsymptotic.adjointRemainder_strip_C1_bounds
    obtain ⟨T, hT0, hT⟩ := tail_strip_bound hVK ha hδ
    let G : ℝ := ∫ x in Icc x0 y, ‖(ForwardKernel.Transport.forwardResponse x : ℂ)‖
    have hG : 0 ≤ G := integral_nonneg (fun _ => norm_nonneg _)
    let D : ℝ := ‖(discrepancy a : ℂ)‖ * B * 2
    have hD : 0 ≤ D := by dsimp [D]; positivity
    refine ⟨G + F + D + T + 1, by positivity, ?_⟩
    intro s hs hs1
    have hs0 : -(1 / 5 : ℝ) ≤ s.re := by linarith
    have hGbound : ‖∫ x in Icc x0 y, (ForwardKernel.Transport.forwardResponse x : ℂ) *
        (x : ℂ) ^ (-s - 1)‖ ≤ G :=
      compact_mellin_strip_bound (by linarith)
        (forwardResponse_compact_integrable (show 0 ≤ (1 / 2 : ℝ) + 1 / 4 by norm_num) hE hx0) hs0
    have hendpoint : ‖(discrepancy a : ℂ) * adjointRemainder a s‖ ≤ D * (1 + |s.im|) ^ 2 := by
      rw [norm_mul]
      have hp : a ^ (-s.re - 7 / 10) ≤ 1 := by
        simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith : 1 ≤ a)
          (by linarith : -s.re - 7 / 10 ≤ 0)
      have hr := (hb s hs0 hs1 a ha).1
      have hn := parameter_strip_bound hs0 hs1
      calc
        _ ≤ ‖(discrepancy a : ℂ)‖ * (B * (1 + ‖s‖) * a ^ (-s.re - 7 / 10)) :=
          mul_le_mul_of_nonneg_left hr (norm_nonneg _)
        _ ≤ ‖(discrepancy a : ℂ)‖ * (B * (1 + ‖s‖) * 1) := by gcongr
        _ ≤ ‖(discrepancy a : ℂ)‖ * (B * (2 * (1 + |s.im|)) * 1) := by gcongr
        _ = D * (1 + |s.im|) := by dsimp [D]; ring
        _ ≤ D * (1 + |s.im|) ^ 2 := mul_le_mul_of_nonneg_left
          (by nlinarith [sq_nonneg |s.im|, abs_nonneg s.im]) hD
    have htotal := norm_add_le
      (∫ x in Icc x0 y, (ForwardKernel.Transport.forwardResponse x : ℂ) * (x : ℂ) ^ (-s - 1))
      (explicitRemainderFour y s)
    have hfour : ‖explicitRemainderFour y s‖ ≤ F + D * (1 + |s.im|) ^ 2 + T * (1 + |s.im|) ^ 2 := by
      unfold explicitRemainderFour
      change ‖finiteCorrection y a s - (discrepancy a : ℂ) * adjointRemainder a s - _‖ ≤ _
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add (hF s hs0) hendpoint)) (hT s hs hs1))
    change ‖_ + explicitRemainderFour y s‖ ≤ _
    have hw : 1 ≤ (1 + |s.im|) ^ 2 := by nlinarith [sq_nonneg |s.im|, abs_nonneg s.im]
    have hGF := mul_le_mul_of_nonneg_left hw (add_nonneg hG hF0)
    exact htotal.trans (by nlinarith)

end
end D5.S3.Arith.Robin.ForwardKernel.MellinPolynomialGrowth
