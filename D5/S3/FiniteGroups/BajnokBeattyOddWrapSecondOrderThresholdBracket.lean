/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapSecondOrderThresholdBracket
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapSecondOrderThresholdBracket
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The original unique threshold satisfies a finite K=1 bracket around an explicit second-order corrected center. -/

import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianEnvelope
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianSecondOrder
import D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket

/-! The scale is fixed by the existing order-nine Perron instance.
The continuous functions below are exponentials and rational coordinates.
The count envelope is used exclusively at integer arguments. -/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapSecondOrderThresholdBracket

open Set
open D5.S0.Tower.DBonacci.PerronRoot
open BajnokBeattyOddWrapGaussianRoot BajnokBeattyOddWrapGaussianEnvelope
open BajnokBeattyOddWrapThresholdBracket BajnokBeattyOddWrapReturnCounts
open BajnokBeattyOddWrapSingleCrossing BajnokBeattyOddWrapPositiveCone
open BajnokBeattyOddWrapGaussianUpperEnvelope BajnokBeattyOddWrapGaussianSecondOrder

noncomputable def beta_correction : ℝ :=
  -1/6 + (5*s_star/72)*
    (41*dbonacciPerronRoot 9-81)/(5*dbonacciPerronRoot 9-9)

private noncomputable def H (s : ℝ) : ℝ :=
  (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))

private noncomputable def g : ℝ := Real.exp s_star-9*Real.exp (-9*s_star)

private noncomputable def d : ℝ := beta_correction+1/6

private theorem sigma_pos : 0 < s_star := by
  linarith only [two_thirds_lt_s_star]

private theorem alpha_pos : 0 < alpha := by
  linarith only [alpha_gt_twentyfour_twentyfive]

private theorem alpha_root_identity : 3*alpha*s_star = 2 := by
  unfold alpha
  field_simp [sigma_pos.ne'] <;> ring

private theorem root_as_alpha : s_star = 2/(3*alpha) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) alpha_pos.ne')).2
  nlinarith only [alpha_root_identity]

private theorem exp_six_gt_three_hundred : (300 : ℝ) < Real.exp 6 := by
  have hh := Real.sum_le_exp_of_nonneg (x := (6 : ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  linarith only [hh]

private theorem exp_negative_small {s : ℝ} (hs : (2/3 : ℝ) ≤ s) :
    Real.exp (-9*s) < 1/300 := by
  have hh := exp_six_gt_three_hundred.trans_le
    (Real.exp_le_exp.mpr (show (6 : ℝ) ≤ 9*s by linarith only [hs]))
  rw [show -9*s = -(9*s) by ring, Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos (9*s))).2
  linarith only [hh]

private theorem alpha_lt_ninetyseven_hundred : alpha < (97/100 : ℝ) := by
  have hexp : Real.exp (200/291 : ℝ) < 199/100 := by
    have hh := Real.exp_bound' (x := (200/291 : ℝ))
      (by norm_num) (by norm_num) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hh
    linarith only [hh]
  have hneg := exp_negative_small (by norm_num : (2/3 : ℝ) ≤ 200/291)
  have hG : gaussian (200/291) < 2 := by
    unfold gaussian
    linarith only [hexp, hneg]
  have hx : (200/291 : ℝ) < s_star := by
    by_contra hh
    have hle : s_star ≤ (200/291 : ℝ) := le_of_not_gt hh
    have hsec := gaussian_secant two_thirds_lt_s_star.le hle
    rw [gaussian_s_star] at hsec
    linarith only [hG, hsec, hle]
  unfold alpha
  apply (div_lt_iff₀ (mul_pos (by norm_num) sigma_pos)).2
  linarith only [hx]

private theorem sigma_mem : s_star ∈ Icc (2/3 : ℝ) (5/7) := by
  refine ⟨two_thirds_lt_s_star.le, ?_⟩
  have hh := mul_lt_mul_of_pos_right alpha_gt_twentyfour_twentyfive sigma_pos
  nlinarith only [hh, alpha_root_identity]

private theorem exp_on_interval {s : ℝ} (hs : s ∈ Icc (2/3 : ℝ) (5/7)) :
    Real.exp s ≤ 9/4 := by
  have hh := Real.exp_bound' (x := (3/4 : ℝ))
    (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  have hm := Real.exp_le_exp.mpr (show s ≤ (3/4 : ℝ) by linarith only [hs.2])
  linarith only [hh, hm]

private theorem H_bounds {s : ℝ} (hs : s ∈ Icc (2/3 : ℝ) (5/7)) :
    0 < H s ∧ H s ≤ 1875/21952 := by
  have hs0 : 0 < s := by linarith only [hs.1]
  have he := Real.add_one_le_exp s
  have hn := exp_negative_small hs.1
  have hf : 0 < 5*Real.exp s-405*Real.exp (-9*s) := by
    linarith only [he, hn, hs.1]
  have hpow : s^3 ≤ (5/7 : ℝ)^3 := pow_le_pow_left₀ hs0.le hs.2 3
  refine ⟨mul_pos (div_pos (pow_pos hs0 3) (by norm_num)) hf, ?_⟩
  calc
    H s ≤ (s^3/48)*(5*Real.exp s) := by
      unfold H
      exact mul_le_mul_of_nonneg_left
        (by linarith only [Real.exp_pos (-9*s)]) (by positivity)
    _ ≤ (((5/7 : ℝ)^3)/48)*(5*(9/4)) := by
      exact mul_le_mul
        (div_le_div_of_nonneg_right hpow (by norm_num))
        (mul_le_mul_of_nonneg_left (exp_on_interval hs) (by norm_num))
        (by positivity) (by norm_num)
    _ = 1875/21952 := by norm_num

private theorem hasDerivAt_H (s : ℝ) :
    HasDerivAt H
      (5*s^2*(s+3)*Real.exp s/48 +
        1215*s^2*(3*s-1)*Real.exp (-9*s)/48) s := by
  have hn : HasDerivAt (fun x : ℝ => -9*x) (-9) s :=
    hasDerivAt_const_mul (x := s) (-9)
  convert (((hasDerivAt_id s).pow 3).div_const 48).mul
    (((Real.hasDerivAt_exp s).const_mul 5).sub (hn.exp.const_mul 405)) using 1 <;>
    (try funext x) <;>
      (try simp only [H, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]) <;> ring

private theorem H_deriv_bounds {s : ℝ} (hs : s ∈ Icc (2/3 : ℝ) (5/7)) :
    0 ≤ deriv H s ∧ deriv H s ≤ (1/2 : ℝ) := by
  rw [(hasDerivAt_H s).deriv]
  have hs0 : 0 ≤ s := by linarith only [hs.1]
  have hs3 : 0 ≤ s+3 := by linarith only [hs.1]
  have hs31 : 0 ≤ 3*s-1 := by linarith only [hs.1]
  have hs2 : s^2 ≤ (5/7 : ℝ)^2 := pow_le_pow_left₀ hs0 hs.2 2
  refine ⟨by positivity, ?_⟩
  have ha : 5*s^2*(s+3)*Real.exp s/48 ≤
      5*(5/7 : ℝ)^2*((5/7)+3)*(9/4)/48 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul _ (exp_on_interval hs) (Real.exp_pos s).le (by norm_num)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs2 (by norm_num))
      (by linarith only [hs.2]) hs3 (by norm_num)
  have hb : 1215*s^2*(3*s-1)*Real.exp (-9*s)/48 ≤
      1215*(5/7 : ℝ)^2*(3*(5/7)-1)*(1/300)/48 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul _ (exp_negative_small hs.1).le
      (Real.exp_pos (-9*s)).le (by norm_num)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs2 (by norm_num))
      (by linarith only [hs.2]) hs31 (by norm_num)
  linarith only [ha, hb]

private theorem H_secant {a b : ℝ}
    (ha : a ∈ Icc (2/3 : ℝ) (5/7)) (hb : b ∈ Icc (2/3 : ℝ) (5/7))
    (hab : a ≤ b) : 0 ≤ H b-H a ∧ H b-H a ≤ (b-a)/2 := by
  have hd : Differentiable ℝ H := fun s => (hasDerivAt_H s).differentiableAt
  have hlow : ∀ x ∈ interior (Icc (2/3 : ℝ) (5/7)), 0 ≤ deriv H x :=
    fun x hx => (H_deriv_bounds (interior_subset hx)).1
  have hupp : ∀ x ∈ interior (Icc (2/3 : ℝ) (5/7)), deriv H x ≤ (1/2 : ℝ) :=
    fun x hx => (H_deriv_bounds (interior_subset hx)).2
  have hl := (convex_Icc (2/3 : ℝ) (5/7)).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn hlow a ha b hb hab
  have hu := (convex_Icc (2/3 : ℝ) (5/7)).image_sub_le_mul_sub_of_deriv_le
    hd.continuous.continuousOn hd.differentiableOn hupp a ha b hb hab
  constructor <;> linarith only [hl, hu]

private theorem root_exponentials :
    Real.exp s_star = dbonacciPerronRoot 9 ∧
      Real.exp (-9*s_star) = 2-dbonacciPerronRoot 9 := by
  have hp : 0 < dbonacciPerronRoot 9 :=
    lt_trans zero_lt_one (one_lt_dbonacciPerronRoot 9 (by norm_num))
  have he : Real.exp s_star = dbonacciPerronRoot 9 := Real.exp_log hp
  refine ⟨he, ?_⟩
  have hh := gaussian_s_star
  unfold gaussian at hh
  linarith only [hh, he]

private theorem g_bounds : (98/75 : ℝ) ≤ g ∧ g ≤ 9/4 := by
  have ha := Real.add_one_le_exp s_star
  have hb := exp_negative_small sigma_mem.1
  have hc := exp_on_interval sigma_mem
  have hd := Real.exp_pos (-9*s_star)
  unfold g
  constructor <;> linarith only [ha, hb, hc, hd, sigma_mem.1]

private theorem g_pos : 0 < g := by linarith only [g_bounds.1]

private theorem cancellation_coefficient : d = 2*H s_star/(3*s_star^2*g) := by
  have hg : g = 2*(5*dbonacciPerronRoot 9-9) := by
    unfold g
    rw [root_exponentials.1, root_exponentials.2]
    ring
  have hb : 5*dbonacciPerronRoot 9-9 ≠ 0 := by
    have hh := g_pos
    rw [hg] at hh
    linarith only [hh]
  unfold d beta_correction H
  rw [root_exponentials.1, root_exponentials.2, hg]
  field_simp [sigma_pos.ne', hb] <;> ring

private theorem d_bounds : 0 < d ∧ d ≤ (1/10 : ℝ) := by
  rw [cancellation_coefficient]
  have hden : 0 < 3*s_star^2*g :=
    mul_pos (mul_pos (by norm_num) (pow_pos sigma_pos 2)) g_pos
  refine ⟨div_pos (mul_pos (by norm_num) (H_bounds sigma_mem).1) hden, ?_⟩
  have hdenlow : (392/225 : ℝ) ≤ 3*s_star^2*g := by
    calc
      (392/225 : ℝ) = 3*(2/3 : ℝ)^2*(98/75) := by norm_num
      _ ≤ 3*s_star^2*g := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by norm_num) sigma_mem.1 2) (by norm_num))
          g_bounds.1 (by norm_num) (by positivity)
  have hsharp : 2*H s_star/(3*s_star^2*g) ≤ (421875/4302592 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith only [(H_bounds sigma_mem).2, hdenlow]
  linarith only [hsharp]

private noncomputable def k : ℝ := s_star*d/alpha

private theorem k_bounds : 0 < k ∧ k ≤ (25/336 : ℝ) := by
  refine ⟨div_pos (mul_pos sigma_pos d_bounds.1) alpha_pos, ?_⟩
  unfold k
  apply (div_le_iff₀ alpha_pos).2
  have hh : s_star*d ≤ (5/7 : ℝ)*(1/10) :=
    mul_le_mul sigma_mem.2 d_bounds.2 d_bounds.1.le (by norm_num)
  nlinarith only [hh, alpha_gt_twentyfour_twentyfive]

private theorem cancellation : g*k = H s_star := by
  unfold k
  rw [cancellation_coefficient, root_as_alpha]
  field_simp [alpha_pos.ne', g_pos.ne'] <;> ring

private noncomputable def parameter (P v : ℝ) : ℝ := 2*P/(3*v)

private noncomputable def center_v (P : ℝ) : ℝ := alpha*P+d/P

private noncomputable def center_s (P : ℝ) : ℝ := parameter P (center_v P)

private noncomputable def Q (P s : ℝ) : ℝ := gaussian s+H s/P^2

private theorem Q_secant {P a b : ℝ} (hP : 0 < P)
    (ha : a ∈ Icc (2/3 : ℝ) (5/7)) (hb : b ∈ Icc (2/3 : ℝ) (5/7))
    (hab : a ≤ b) : Q P a+(98/75 : ℝ)*(b-a) ≤ Q P b := by
  have hG := gaussian_secant ha.1 hab
  have hH := div_le_div_of_nonneg_right (H_secant ha hb hab).1 (pow_nonneg hP.le 2)
  change 0/P^2 ≤ (H b-H a)/P^2 at hH
  rw [zero_div, sub_div] at hH
  unfold Q
  linarith only [hG, hH]

private theorem parameter_mem {P v : ℝ} (hP : 0 < P)
    (hvlow : (14/15 : ℝ)*P ≤ v) (hvhigh : v ≤ P) :
    parameter P v ∈ Icc (2/3 : ℝ) (5/7) := by
  have hv : 0 < v := lt_of_lt_of_le (by positivity) hvlow
  constructor
  · apply (le_div_iff₀ (show 0 < 3*v by positivity)).2
    linarith only [hvhigh]
  · apply (div_le_iff₀ (show 0 < 3*v by positivity)).2
    linarith only [hvlow]

private theorem parameter_antitone {P a b : ℝ} (hP : 0 < P)
    (ha : 0 < a) (hab : a ≤ b) : parameter P b ≤ parameter P a := by
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hab (by norm_num))

private noncomputable def v_minus (P : ℝ) : ℝ := center_v P-1/P^3

private noncomputable def v_plus (P : ℝ) : ℝ := center_v P+1/P^3

private theorem test_v_bounds {P : ℝ} (hP5 : 5 ≤ P) :
    (14/15 : ℝ)*P < v_minus P ∧ v_minus P ≤ center_v P ∧
      center_v P ≤ v_plus P ∧ v_plus P ≤ P := by
  have hP : 0 < P := by linarith only [hP5]
  have hP3 : (125 : ℝ) ≤ P^3 := by
    calc
      (125 : ℝ) = (5 : ℝ)^3 := by norm_num
      _ ≤ P^3 := pow_le_pow_left₀ (by norm_num) hP5 3
  have hi3 : 0 < 1/P^3 := by positivity
  have hi3le : 1/P^3 ≤ (1/125 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hP 3)).2
    linarith only [hP3]
  have hdP : 0 < d/P := div_pos d_bounds.1 hP
  have hdPle : d/P ≤ (1/50 : ℝ) := by
    apply (div_le_iff₀ hP).2
    linarith only [d_bounds.2, hP5]
  have ha := mul_lt_mul_of_pos_right alpha_gt_twentyfour_twentyfive hP
  have hb := mul_lt_mul_of_pos_right alpha_lt_ninetyseven_hundred hP
  dsimp only [v_minus, v_plus, center_v]
  constructor
  · linarith only [ha, hP5, hdP, hi3le]
  constructor
  · linarith only [hi3]
  constructor
  · linarith only [hi3]
  · linarith only [hb, hP5, hdPle, hi3le]

private theorem center_mem {P : ℝ} (hP5 : 5 ≤ P) :
    center_s P ∈ Icc (2/3 : ℝ) (5/7) := by
  have hh := test_v_bounds hP5
  exact parameter_mem (by linarith only [hP5])
    (hh.1.le.trans hh.2.1) (hh.2.2.1.trans hh.2.2.2)

private theorem center_shift {P : ℝ} (hP5 : 5 ≤ P) :
    0 ≤ s_star-center_s P ∧ s_star-center_s P ≤ k/P^2 ∧
      0 ≤ k/P^2-(s_star-center_s P) ∧
      k/P^2-(s_star-center_s P) ≤ 125/(16128*P^4) := by
  have hP : 0 < P := by linarith only [hP5]
  have ha0 := alpha_pos
  have hd0 := d_bounds.1
  have hk0 := k_bounds.1
  have hD : 0 < alpha*P^2+d := by positivity
  have hvc : 0 < alpha*P+d/P := by positivity
  have hδ : s_star-center_s P = k*alpha/(alpha*P^2+d) := by
    simp only [center_s, parameter, center_v, k, root_as_alpha]
    field_simp [hP.ne', alpha_pos.ne', hD.ne', hvc.ne'] <;> ring
  have hr : k/P^2-(s_star-center_s P) = k*d/(P^2*(alpha*P^2+d)) := by
    rw [hδ]
    field_simp [hP.ne', hD.ne'] <;> ring
  have hr0 : 0 ≤ k/P^2-(s_star-center_s P) := by rw [hr]; positivity
  refine ⟨?_, by linarith only [hr0], hr0, ?_⟩
  · rw [hδ]
    positivity
  · rw [hr]
    calc
      k*d/(P^2*(alpha*P^2+d)) ≤
          ((25/336 : ℝ)*(1/10))/(P^2*(alpha*P^2+d)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul k_bounds.2 d_bounds.2 d_bounds.1.le (by norm_num)
      _ ≤ ((25/336 : ℝ)*(1/10))/(P^2*((24/25)*P^2)) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh := mul_le_mul_of_nonneg_right
          alpha_gt_twentyfour_twentyfive.le (pow_nonneg hP.le 2)
        linarith only [hh, d_bounds.1]
      _ = 125/(16128*P^4) := by field_simp [hP.ne'] <;> ring

private theorem exp_positive_quadratic {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ Real.exp u-1-u ∧ Real.exp u-1-u ≤ (3/4)*u^2 := by
  have hlo := Real.add_one_le_exp u
  have hhi := Real.exp_bound' hu0 hu1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hhi
  constructor <;> linarith only [hlo, hhi]

private theorem exp_negative_quadratic {u : ℝ} (hu0 : 0 ≤ u) :
    0 ≤ Real.exp (-u)-1+u ∧ Real.exp (-u)-1+u ≤ u^2/2 := by
  have hlo := Real.add_one_le_exp (-u)
  have hQ : 0 < 1-u+u^2/2 := by nlinarith only [sq_nonneg (u-1)]
  have hquad := Real.quadratic_le_exp_of_nonneg hu0
  have hmul := mul_le_mul_of_nonneg_left hquad hQ.le
  have hid : (1-u+u^2/2)*(1+u+u^2/2) = 1+u^4/4 := by ring
  rw [hid] at hmul
  have hhi : Real.exp (-u) ≤ 1-u+u^2/2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos u)).2
    nlinarith only [hmul, pow_nonneg hu0 4]
  constructor <;> linarith only [hlo, hhi]

private theorem gaussian_center_quadratic {P : ℝ} (hP5 : 5 ≤ P) :
    0 ≤ gaussian (center_s P)-2+g*(s_star-center_s P) ∧
      gaussian (center_s P)-2+g*(s_star-center_s P) ≤
        (3/2)*(s_star-center_s P)^2 := by
  let δ : ℝ := s_star-center_s P
  have hh := center_shift hP5
  have hδ0 : 0 ≤ δ := hh.1
  have hP : 0 < P := by linarith only [hP5]
  have hP2 : (25 : ℝ) ≤ P^2 := by
    calc
      (25 : ℝ) = (5 : ℝ)^2 := by norm_num
      _ ≤ P^2 := pow_le_pow_left₀ (by norm_num) hP5 2
  have hδP : δ*P^2 ≤ k := (le_div_iff₀ (pow_pos hP 2)).mp hh.2.1
  have hδ25 := mul_le_mul_of_nonneg_left hP2 hδ0
  have hδ9 : 9*δ ≤ 1 := by nlinarith only [hδP, hδ25, k_bounds.2]
  have hm := exp_negative_quadratic hδ0
  have hp := exp_positive_quadratic (show 0 ≤ 9*δ by positivity) hδ9
  have hrepr : gaussian (center_s P) =
      Real.exp s_star*Real.exp (-δ)+Real.exp (-9*s_star)*Real.exp (9*δ) := by
    have he : center_s P = s_star-δ := by dsimp only [δ]; ring
    rw [he]
    unfold gaussian
    rw [show s_star-δ = s_star+(-δ) by ring, Real.exp_add,
      show -9*(s_star+-δ) = -9*s_star+9*δ by ring, Real.exp_add]
  have hid : gaussian (center_s P)-2+g*δ =
      Real.exp s_star*(Real.exp (-δ)-1+δ)+
        Real.exp (-9*s_star)*(Real.exp (9*δ)-1-9*δ) := by
    have hroot := gaussian_s_star
    unfold gaussian at hroot
    rw [hrepr]
    unfold g
    nlinarith only [hroot]
  change 0 ≤ gaussian (center_s P)-2+g*δ ∧
    gaussian (center_s P)-2+g*δ ≤ (3/2)*δ^2
  rw [hid]
  refine ⟨add_nonneg (mul_nonneg (Real.exp_pos _).le hm.1)
    (mul_nonneg (Real.exp_pos _).le hp.1), ?_⟩
  calc
    Real.exp s_star*(Real.exp (-δ)-1+δ)+
        Real.exp (-9*s_star)*(Real.exp (9*δ)-1-9*δ) ≤
        2*(δ^2/2)+(1/300)*((3/4)*(9*δ)^2) := by
      apply add_le_add
      · exact mul_le_mul
          (by rw [root_exponentials.1];
              exact (dbonacciPerronRoot_lt_two 9 (by norm_num)).le)
          hm.2 hm.1 (by norm_num)
      · exact mul_le_mul (exp_negative_small sigma_mem.1).le hp.2 hp.1
          (by norm_num)
    _ ≤ (3/2)*δ^2 := by nlinarith only [sq_nonneg δ]

private theorem center_error {P : ℝ} (hP5 : 5 ≤ P) :
    |Q P (center_s P)-2| ≤ 1/(10*P^4) := by
  have hP : 0 < P := by linarith only [hP5]
  let δ : ℝ := s_star-center_s P
  let r : ℝ := k/P^2-δ
  let E : ℝ := gaussian (center_s P)-2+g*δ
  have hshift := center_shift hP5
  have hδ0 : 0 ≤ δ := hshift.1
  have hr0 : 0 ≤ r := hshift.2.2.1
  have hrle : r ≤ 125/(16128*P^4) := hshift.2.2.2
  have hδle : δ ≤ (25/336 : ℝ)/P^2 :=
    hshift.2.1.trans (div_le_div_of_nonneg_right k_bounds.2 (by positivity))
  have hδsq : δ^2 ≤ (25/336 : ℝ)^2/P^4 := by
    calc
      δ^2 ≤ ((25/336 : ℝ)/P^2)^2 := pow_le_pow_left₀ hδ0 hδle 2
      _ = (25/336 : ℝ)^2/P^4 := by field_simp [hP.ne'] <;> ring
  have hE := gaussian_center_quadratic hP5
  have hE0 : 0 ≤ E := hE.1
  have hEle : E ≤ (3/2)*((25/336 : ℝ)^2/P^4) := by
    exact hE.2.trans (mul_le_mul_of_nonneg_left hδsq (by norm_num))
  have hH := H_secant (center_mem hP5) sigma_mem
    (show center_s P ≤ s_star by linarith only [hδ0])
  have hH0 : 0 ≤ H s_star-H (center_s P) := hH.1
  have hHle : H s_star-H (center_s P) ≤ ((25/336 : ℝ)/P^2)/2 :=
    hH.2.trans (by dsimp only [δ] at hδle; linarith only [hδle])
  have hid : Q P (center_s P)-2 =
      g*r+E-(H s_star-H (center_s P))/P^2 := by
    dsimp only [Q, r, E, δ]
    have hc := congrArg (fun x : ℝ => x/P^2) cancellation
    rw [mul_div_assoc] at hc
    rw [sub_div, ← hc]
    ring
  have hgr : g*r ≤ (9/4 : ℝ)*(125/(16128*P^4)) :=
    mul_le_mul g_bounds.2 hrle hr0 (by norm_num)
  have hhr : (H s_star-H (center_s P))/P^2 ≤
      (((25/336 : ℝ)/P^2)/2)/P^2 :=
    div_le_div_of_nonneg_right hHle (by positivity)
  have hnum : (9/4 : ℝ)*(125/(16128*P^4))+
      (3/2)*((25/336 : ℝ)^2/P^4)+(((25/336 : ℝ)/P^2)/2)/P^2 =
        (9475/150528 : ℝ)/P^4 := by field_simp [hP.ne'] <;> ring
  have hsmall : (9475/150528 : ℝ)/P^4 ≤ 1/(10*P^4) := by
    apply (div_le_div_iff₀ (pow_pos hP 4) (by positivity)).2
    nlinarith only [pow_nonneg hP.le 4]
  apply (abs_le).2
  constructor
  · rw [hid]
    have hgr0 : 0 ≤ g*r := mul_nonneg g_pos.le hr0
    have hrem0 : 0 ≤ (((25/336 : ℝ)/P^2)/2)/P^2 := by positivity
    have hmaj : (((25/336 : ℝ)/P^2)/2)/P^2 ≤ 1/(10*P^4) := by
      have ha : 0 ≤ (9/4 : ℝ)*(125/(16128*P^4)) := by positivity
      have hb : 0 ≤ (3/2)*((25/336 : ℝ)^2/P^4) := by positivity
      linarith only [ha, hb, hnum, hsmall]
    linarith only [hgr0, hE0, hhr, hmaj]
  · rw [hid]
    have hrem0 : 0 ≤ (H s_star-H (center_s P))/P^2 := by positivity
    have htail0 : 0 ≤ (((25/336 : ℝ)/P^2)/2)/P^2 := by positivity
    linarith only [hgr, hEle, hrem0, htail0, hnum, hsmall]

private theorem parameter_gap {P a b : ℝ} (hP : 0 < P)
    (ha : 0 < a) (hb : 0 < b) (haP : a ≤ P) (hbP : b ≤ P)
    (hgap : 1/P^3 ≤ b-a) :
    2/(3*P^4) ≤ parameter P a-parameter P b := by
  have hid : parameter P a-parameter P b = 2*P*(b-a)/(3*a*b) := by
    unfold parameter
    field_simp [ha.ne', hb.ne'] <;> ring
  rw [hid]
  apply (le_div_iff₀ (show 0 < 3*a*b by positivity)).2
  have habP : a*b ≤ P^2 := by
    simpa only [pow_two] using mul_le_mul haP hbP hb.le hP.le
  calc
    (2/(3*P^4))*(3*a*b) ≤ (2/(3*P^4))*(3*P^2) := by
      exact mul_le_mul_of_nonneg_left
        (by linarith only [habP]) (by positivity)
    _ = 2*P*(1/P^3) := by field_simp [hP.ne'] <;> ring
    _ ≤ 2*P*(b-a) := mul_le_mul_of_nonneg_left hgap (by positivity)

private theorem test_Q_bounds {P : ℝ} (hP5 : 5 ≤ P) :
    2+1/(5*P^4) < Q P (parameter P (v_minus P)) ∧
      Q P (parameter P (v_plus P)) < 2-1/(5*P^4) := by
  have hP : 0 < P := by linarith only [hP5]
  have hv := test_v_bounds hP5
  have hm0 : 0 < v_minus P := lt_trans (by positivity) hv.1
  have hc0 : 0 < center_v P := hm0.trans_le hv.2.1
  have hp0 : 0 < v_plus P := hc0.trans_le hv.2.2.1
  have hmP := hv.2.1.trans (hv.2.2.1.trans hv.2.2.2)
  have hcP := hv.2.2.1.trans hv.2.2.2
  have hmI := parameter_mem hP hv.1.le hmP
  have hpI := parameter_mem hP
    (hv.1.le.trans (hv.2.1.trans hv.2.2.1)) hv.2.2.2
  have hcI := center_mem hP5
  have hcm : center_s P ≤ parameter P (v_minus P) :=
    parameter_antitone hP hm0 hv.2.1
  have hpc : parameter P (v_plus P) ≤ center_s P :=
    parameter_antitone hP hc0 hv.2.2.1
  have hmgap := parameter_gap hP hm0 hc0 hmP hcP
    (show 1/P^3 ≤ center_v P-v_minus P by unfold v_minus; linarith)
  have hpgap := parameter_gap hP hc0 hp0 hcP hv.2.2.2
    (show 1/P^3 ≤ v_plus P-center_v P by unfold v_plus; linarith)
  have hms := Q_secant hP hcI hmI hcm
  have hps := Q_secant hP hpI hcI hpc
  have herror := abs_le.mp (center_error hP5)
  change _ ≤ parameter P (v_minus P)-center_s P at hmgap
  change _ ≤ center_s P-parameter P (v_plus P) at hpgap
  have hmm := mul_le_mul_of_nonneg_left hmgap (by norm_num : (0 : ℝ) ≤ 98/75)
  have hpm := mul_le_mul_of_nonneg_left hpgap (by norm_num : (0 : ℝ) ≤ 98/75)
  have hmargin : 1/(10*P^4)+1/(5*P^4) < (98/75 : ℝ)*(2/(3*P^4)) := by
    have hid : (98/75 : ℝ)*(2/(3*P^4))-1/(10*P^4)-1/(5*P^4) =
        (257/450 : ℝ)/P^4 := by field_simp [hP.ne'] <;> ring
    have hpos : 0 < (257/450 : ℝ)/P^4 := by positivity
    linarith only [hid, hpos]
  constructor <;> linarith only [hms, hps, herror.1, herror.2, hmm, hpm, hmargin]

private noncomputable def centered_v (P t : ℝ) : ℝ := t-1/6+1/(6*P)

private theorem centered_v_rewrite (P t : ℝ) (hP : 0 < P) :
    centered_v P t = center_v P+t-(alpha*P+1/6+beta_correction/P) := by
  unfold centered_v center_v d
  field_simp [hP.ne'] <;> ring

private theorem centered_parameter (P t : ℝ) (hP : 0 < P)
    (hv : 0 < centered_v P t) :
    4*P^2/(P*(6*t-1)+1) = parameter P (centered_v P t) := by
  have hR : P*(6*t-1)+1 = 6*P*centered_v P t := by
    unfold centered_v
    field_simp [hP.ne'] <;> ring
  rw [hR]
  unfold parameter
  field_simp [hP.ne', hv.ne'] <;> ring

private theorem band_coordinate {P t : ℝ} (hP5 : 5 ≤ P)
    (htp : t ≤ P) (hband : 24*P ≤ 25*t) :
    0 < centered_v P t ∧ parameter P (centered_v P t) ∈ Icc (2/3 : ℝ) (5/7) := by
  have hP : 0 < P := by linarith only [hP5]
  have hbase : (14/15 : ℝ)*P ≤ (24/25)*P-1/6+1/(6*P) := by
    have hf : 0 ≤ (P-5)*(4*P-5) := mul_nonneg (by linarith only [hP5])
      (by linarith only [hP5])
    have hid : P*((24/25)*P-1/6+1/(6*P)-(14/15)*P) =
        (P-5)*(4*P-5)/150 := by field_simp [hP.ne'] <;> ring
    have hm : 0 ≤ P*((24/25)*P-1/6+1/(6*P)-(14/15)*P) := by
      rw [hid]
      exact div_nonneg hf (by norm_num)
    have hh := nonneg_of_mul_nonneg_right hm hP
    linarith only [hh]
  have hvlow : (14/15 : ℝ)*P ≤ centered_v P t := by
    unfold centered_v
    linarith only [hbase, hband]
  have hi : 1/(6*P) ≤ (1/6 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 6*P by positivity)).2
    linarith only [hP5]
  have hvhigh : centered_v P t ≤ P := by
    unfold centered_v
    linarith only [htp, hi]
  exact ⟨lt_of_lt_of_le (by positivity) hvlow, parameter_mem hP hvlow hvhigh⟩

private theorem integer_envelope (p t : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (ht2 : 2 ≤ t) (htp : t ≤ p) (hband : 24*p ≤ 25*t) :
    0 < centered_v (p : ℝ) (t : ℝ) ∧
      parameter (p : ℝ) (centered_v (p : ℝ) (t : ℝ)) ∈ Icc (2/3 : ℝ) (5/7) ∧
      |2*((original_return_pair p t).1 : ℝ)/((original_return_pair p t).2 : ℝ)-
        Q (p : ℝ) (parameter (p : ℝ) (centered_v (p : ℝ) (t : ℝ)))| ≤
          1/(5*(p : ℝ)^4) := by
  have hpR5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hpR : 0 < (p : ℝ) := by linarith only [hpR5]
  have htpR : (t : ℝ) ≤ (p : ℝ) := by exact_mod_cast htp
  have hbandR : 24*(p : ℝ) ≤ 25*(t : ℝ) := by exact_mod_cast hband
  have hv := band_coordinate hpR5 htpR hbandR
  refine ⟨hv.1, hv.2, ?_⟩
  have he := actual_gaussian_second_order_envelope p t hp5 hpo ht2 htp hband
  dsimp only at he
  rw [centered_parameter (p : ℝ) (t : ℝ) hpR hv.1] at he
  have hid (s : ℝ) :
      2*((original_return_pair p t).1 : ℝ)/((original_return_pair p t).2 : ℝ)-Q (p : ℝ) s =
      2*((original_return_pair p t).1 : ℝ)/((original_return_pair p t).2 : ℝ)-
        (Real.exp s+Real.exp (-9*s))-
        (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/(p : ℝ)^2 := by
    unfold Q gaussian H
    ring
  rw [hid]
  exact he

private theorem original_second_pos (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p)
    (ht2 : 2 ≤ t) : 0 < (original_return_pair p t).2 := by
  have hp : 0 < p := by omega
  have hc := actual_odd_wrap_counts p t hp3 hpo ht2
  have hhalf3 : p*((6*t-1)+3)/2 = 3*p*t+p := by
    have hh : p*((6*t-1)+3) = 2*(3*p*t+p) := by ring
    omega
  have hW33 : (original_return_pair p t).2 =
      4*Nat.choose (p*(6*t-1)).toNat (3*p*t+p).toNat := by
    calc
      (original_return_pair p t).2 =
          4*Nat.choose (p*(6*t-1)).toNat (p*((6*t-1)+3)/2).toNat := hc.2
      _ = _ := by rw [hhalf3]
  have hindex : 3*p*t+p ≤ p*(6*t-1) := by
    have hm := mul_nonneg hp.le (show 0 ≤ 3*t-2 by omega)
    nlinarith only [hm]
  have hindexNat : (3*p*t+p).toNat ≤ (p*(6*t-1)).toNat := by omega
  rw [hW33]
  exact mul_pos (by norm_num) (Nat.choose_pos hindexNat)

private theorem original_threshold_bounds (p : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (T : ℕ)
    (hT : 2 < T ∧
      (∀ t : ℕ, 2 ≤ t → t < T →
        (original_return_pair p t).2 < (original_return_pair p t).1) ∧
      (original_return_pair p T).1 ≤ (original_return_pair p T).2 ∧
      (∀ t : ℕ, T < t →
        (original_return_pair p t).1 < (original_return_pair p t).2))
    (hcoarse : alpha*(p : ℝ)+1/6-1/(6*(p : ℝ)) < (T : ℝ)) :
    alpha*(p : ℝ)+1/6+beta_correction/(p : ℝ)-1/(p : ℝ)^3 < (T : ℝ) ∧
      (T : ℤ) ≤ Int.ceil
        (alpha*(p : ℝ)+1/6+beta_correction/(p : ℝ)+1/(p : ℝ)^3) := by
  have hp3 : 3 ≤ p := by omega
  have hpR5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hpR : 0 < (p : ℝ) := by linarith only [hpR5]
  have hTP : (T : ℤ) ≤ p := by
    let N : ℕ := p.toNat
    have hN : (N : ℤ) = p := Int.toNat_of_nonneg (by omega)
    have hN2 : 2 ≤ N := by omega
    have he := actual_positive_odd_wrap_cone p p hp5 hpo le_rfl
    have heN : (original_return_pair p (N : ℤ)).1 <
        (original_return_pair p (N : ℤ)).2 := by simpa only [hN] using he
    have hTN : T ≤ N := by
      by_contra hh
      have hb := hT.2.1 N hN2 (by omega)
      omega
    have hh : (T : ℤ) ≤ (N : ℤ) := by exact_mod_cast hTN
    simpa only [hN] using hh
  have hi6 : 1/(6*(p : ℝ)) ≤ (1/6 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 6*(p : ℝ) by positivity)).2
    linarith only [hpR5]
  have haP := mul_lt_mul_of_pos_right alpha_gt_twentyfour_twentyfive hpR
  have hTbandR : 24*(p : ℝ) ≤ 25*(T : ℝ) := by
    linarith only [haP, hcoarse, hi6]
  have hTband : 24*p ≤ 25*(T : ℤ) := by exact_mod_cast hTbandR
  have henvT := integer_envelope p (T : ℤ) hp5 hpo (by omega) hTP hTband
  simp only [Int.cast_natCast] at henvT
  have htest := test_Q_bounds hpR5
  have hvb := test_v_bounds hpR5
  have hmP := hvb.2.1.trans (hvb.2.2.1.trans hvb.2.2.2)
  have hmI := parameter_mem hpR hvb.1.le hmP
  have hpI := parameter_mem hpR
    (hvb.1.le.trans (hvb.2.1.trans hvb.2.2.1)) hvb.2.2.2
  have hlower : alpha*(p : ℝ)+1/6+beta_correction/(p : ℝ)-1/(p : ℝ)^3 <
      (T : ℝ) := by
    by_contra hh
    have hlow : (T : ℝ) ≤
        alpha*(p : ℝ)+1/6+beta_correction/(p : ℝ)-1/(p : ℝ)^3 := le_of_not_gt hh
    have hvT : centered_v (p : ℝ) (T : ℝ) ≤ v_minus (p : ℝ) := by
      rw [centered_v_rewrite (p : ℝ) (T : ℝ) hpR]
      unfold v_minus
      linarith only [hlow]
    have hsT : parameter (p : ℝ) (v_minus (p : ℝ)) ≤
        parameter (p : ℝ) (centered_v (p : ℝ) (T : ℝ)) :=
      parameter_antitone hpR henvT.1 hvT
    have hsec := Q_secant hpR hmI henvT.2.1 hsT
    have hQ : 2+1/(5*(p : ℝ)^4) <
        Q (p : ℝ) (parameter (p : ℝ) (centered_v (p : ℝ) (T : ℝ))) := by
      linarith only [htest.1, hsec, hsT]
    have hratio : (2 : ℝ) <
        2*((original_return_pair p (T : ℤ)).1 : ℝ)/
          ((original_return_pair p (T : ℤ)).2 : ℝ) := by
      have hh := (abs_le.mp henvT.2.2).1
      linarith only [hh, hQ]
    have hden : (0 : ℝ) < ((original_return_pair p (T : ℤ)).2 : ℝ) := by
      exact_mod_cast original_second_pos p (T : ℤ) hp3 hpo (by omega)
    have hat : ((original_return_pair p (T : ℤ)).1 : ℝ) ≤
        ((original_return_pair p (T : ℤ)).2 : ℝ) := by exact_mod_cast hT.2.2.1
    have hh := (lt_div_iff₀ hden).mp hratio
    linarith only [hh, hat]
  refine ⟨hlower, ?_⟩
  let q : ℝ := alpha*(p : ℝ)+1/6+beta_correction/(p : ℝ)+1/(p : ℝ)^3
  let U : ℤ := Int.ceil q
  change (T : ℤ) ≤ U
  have hqU : q ≤ (U : ℝ) := Int.le_ceil q
  have hqform : q = center_v (p : ℝ)+1/6-1/(6*(p : ℝ))+1/(p : ℝ)^3 := by
    dsimp only [q, center_v, d]
    field_simp [hpR.ne'] <;> ring
  have hqband : (24/25 : ℝ)*(p : ℝ) < q := by
    have hdP : 0 < d/(p : ℝ) := div_pos d_bounds.1 hpR
    have hi3 : 0 < 1/(p : ℝ)^3 := by positivity
    rw [hqform]
    unfold center_v
    linarith only [haP, hdP, hi6, hi3]
  have hq2 : (2 : ℝ) < q := by linarith only [hqband, hpR5]
  have hU2 : (2 : ℤ) ≤ U := by
    have hh : (2 : ℝ) ≤ (U : ℝ) := by linarith only [hq2, hqU]
    exact_mod_cast hh
  by_cases hpU : p ≤ U
  · exact hTP.trans hpU
  · have hUp : U < p := lt_of_not_ge hpU
    let u : ℕ := U.toNat
    have hu : (u : ℤ) = U := Int.toNat_of_nonneg (by omega)
    have huR : (u : ℝ) = (U : ℝ) := by exact_mod_cast hu
    have hu2 : 2 ≤ u := by omega
    have hup : (u : ℤ) ≤ p := by omega
    have hqu : q ≤ (u : ℝ) := by simpa only [huR] using hqU
    have hubandR : 24*(p : ℝ) ≤ 25*(u : ℝ) := by
      linarith only [hqband, hqu]
    have huband : 24*p ≤ 25*(u : ℤ) := by exact_mod_cast hubandR
    have henvU := integer_envelope p (u : ℤ) hp5 hpo (by omega) hup huband
    simp only [Int.cast_natCast] at henvU
    have hvU : v_plus (p : ℝ) ≤ centered_v (p : ℝ) (u : ℝ) := by
      rw [centered_v_rewrite (p : ℝ) (u : ℝ) hpR]
      dsimp only [v_plus]
      dsimp only [q] at hqu
      linarith only [hqu]
    have hvplus : 0 < v_plus (p : ℝ) :=
      lt_of_lt_of_le (by positivity) (hvb.1.le.trans (hvb.2.1.trans hvb.2.2.1))
    have hsU : parameter (p : ℝ) (centered_v (p : ℝ) (u : ℝ)) ≤
        parameter (p : ℝ) (v_plus (p : ℝ)) :=
      parameter_antitone hpR hvplus hvU
    have hsec := Q_secant hpR henvU.2.1 hpI hsU
    have hQ : Q (p : ℝ) (parameter (p : ℝ) (centered_v (p : ℝ) (u : ℝ))) <
        2-1/(5*(p : ℝ)^4) := by
      linarith only [htest.2, hsec, hsU]
    have hratio : 2*((original_return_pair p (u : ℤ)).1 : ℝ)/
        ((original_return_pair p (u : ℤ)).2 : ℝ) < 2 := by
      have hh := (abs_le.mp henvU.2.2).2
      linarith only [hh, hQ]
    have hden : (0 : ℝ) < ((original_return_pair p (u : ℤ)).2 : ℝ) := by
      exact_mod_cast original_second_pos p (u : ℤ) hp3 hpo (by omega)
    have hcountR : ((original_return_pair p (u : ℤ)).1 : ℝ) <
        ((original_return_pair p (u : ℤ)).2 : ℝ) := by
      have hh := (div_lt_iff₀ hden).mp hratio
      linarith only [hh]
    have hcount : (original_return_pair p (u : ℤ)).1 <
        (original_return_pair p (u : ℤ)).2 := by exact_mod_cast hcountR
    have hTu : T ≤ u := by
      by_contra hh
      have hb := hT.2.1 u hu2 (by omega)
      omega
    have hh : (T : ℤ) ≤ (u : ℤ) := by exact_mod_cast hTu
    simpa only [hu] using hh

/-- The complete original single-crossing criterion and a finite K=1
second-correction bracket, for all odd integers p at least five. -/
theorem actual_odd_wrap_second_order_threshold_bracket (p : ℤ) (hp5 : 5 ≤ p)
    (hpo : Odd p) :
    ∃! T : ℕ, 2 < T ∧
      (∀ t : ℕ, 2 ≤ t → t < T →
        (original_return_pair p t).2 < (original_return_pair p t).1) ∧
      (original_return_pair p T).1 ≤ (original_return_pair p T).2 ∧
      (∀ t : ℕ, T < t →
        (original_return_pair p t).1 < (original_return_pair p t).2) ∧
      alpha*(p : ℝ)+1/6+beta_correction/(p : ℝ)-1/(p : ℝ)^3 < (T : ℝ) ∧
      (T : ℤ) ≤ Int.ceil
        (alpha*(p : ℝ)+1/6+beta_correction/(p : ℝ)+1/(p : ℝ)^3) := by
  obtain ⟨T, hT, _⟩ := actual_odd_wrap_threshold_bracket p hp5 hpo
  have hsign : 2 < T ∧
      (∀ t : ℕ, 2 ≤ t → t < T →
        (original_return_pair p t).2 < (original_return_pair p t).1) ∧
      (original_return_pair p T).1 ≤ (original_return_pair p T).2 ∧
      (∀ t : ℕ, T < t →
        (original_return_pair p t).1 < (original_return_pair p t).2) :=
    ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.1⟩
  have hb := original_threshold_bounds p hp5 hpo T hsign hT.2.2.2.2.1
  refine ⟨T, ⟨hsign.1, hsign.2.1, hsign.2.2.1, hsign.2.2.2, hb.1, hb.2⟩, ?_⟩
  intro U hU
  obtain ⟨S, _, huniq⟩ := actual_odd_wrap_single_crossing p (by omega) hpo
  have hTS : T = S := huniq T hsign
  have hUS : U = S := huniq U ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1⟩
  exact hUS.trans hTS.symm

end D5.S3.FiniteGroups.BajnokBeattyOddWrapSecondOrderThresholdBracket

