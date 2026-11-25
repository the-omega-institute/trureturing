/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SeventhCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SeventhCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed sixth and seventh prime-power terms and their normalized tail. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHFifthWindow
import D5.S3.Weil.Mertens.Cryptids.Schoenfeld

/-! Signed sixth and seventh prime-power terms and their normalized tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Finset MeasureTheory Real Set
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail tail_eq diff_integrable)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff
  (coefficient psi_sub_roots_eq_sum)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

theorem abs_psi_sub_roots_add_theta_sixth_sub_seventh_le {t : ℝ} (ht : 2 ≤ t) :
    |psi t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
      psi (t ^ (1 / 5 : ℝ)) + theta (t ^ (1 / 6 : ℝ)) - theta (t ^ (1 / 7 : ℝ))| ≤
      4 * log t * t ^ (1 / 9 : ℝ) := by
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  let M : ℕ := ⌊log t / log 2⌋₊
  let N : ℕ := max M 8
  let f : ℕ → ℝ := fun k => coefficient k * theta (t ^ (1 / (k : ℝ)))
  have hN : M ≤ N := le_max_left _ _
  have hN8 : 8 ≤ N := le_max_right _ _
  have hsum : _ = ∑ k ∈ Finset.Icc 6 N, f k := psi_sub_roots_eq_sum ht hN
  have hsplit : Finset.Icc 6 N = insert 6 (Finset.Icc 7 N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hsplit₇ : Finset.Icc 7 N = insert 7 (Finset.Icc 8 N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hsplit₈ : Finset.Icc 8 N = insert 8 (Finset.Icc 9 N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hsix : f 6 = -theta (t ^ (1 / 6 : ℝ)) := by norm_num [f, coefficient]
  have hseven : f 7 = theta (t ^ (1 / 7 : ℝ)) := by norm_num [f, coefficient]
  have height : f 8 = 0 := by norm_num [f, coefficient]
  rw [hsum, hsplit, Finset.sum_insert (by simp), hsix,
    hsplit₇, Finset.sum_insert (by simp), hseven, hsplit₈, Finset.sum_insert (by simp), height, zero_add]
  have hcancel : ∀ x y z : ℝ, -x + (y + z) + x - y = z := by intros; ring
  rw [hcancel]
  have hcard : (Finset.Icc 9 N).card ≤ M := by
    rw [Nat.card_Icc]
    change max M 8 + 1 - 9 ≤ M
    omega
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    ring
  calc
    _ ≤ ∑ k ∈ Finset.Icc 9 N, |f k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 9 N, 2 * (log 4 * t ^ (1 / 9 : ℝ)) := by
      apply sum_le_sum
      intro k hk
      have hk9 : (9 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
      have hc : |coefficient k| ≤ 2 := by
        unfold coefficient
        split_ifs <;> norm_num
      have htheta := theta_le_log4_mul_x (rpow_nonneg ht0 (1 / (k : ℝ)))
      rw [show f k = coefficient k * theta (t ^ (1 / (k : ℝ))) from rfl,
        abs_mul, abs_of_nonneg (theta_nonneg _)]
      refine mul_le_mul hc (htheta.trans ?_) (theta_nonneg _) (by norm_num)
      exact mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_exponent_le ht1 (one_div_le_one_div_of_le (by norm_num) hk9))
        (log_nonneg (by norm_num))
    _ = ((Finset.Icc 9 N).card : ℝ) * (2 * (log 4 * t ^ (1 / 9 : ℝ))) := by simp
    _ ≤ (log t / log 2) * (2 * (log 4 * t ^ (1 / 9 : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (show ((Finset.Icc 9 N).card : ℝ) ≤ M by exact_mod_cast hcard).trans
        (Nat.floor_le (div_nonneg (log_nonneg ht1) hlog2.le))
    _ = _ := by
      rw [hlog4]
      field_simp
      ring

open ConjectureMachines.Semantics.Riemann
  (SchoenfeldPsiBound abs_psi_sub_self_le_seven_eighths_of_five_thousand_le)

private theorem theta_error_of_rh (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 5000 ≤ x →
      |theta x - x| ≤ C * x ^ (3 / 4 : ℝ) := by
  obtain ⟨D, hD⟩ := psi_sub_theta_le_mul_sqrt
  use |D| + 57
  refine ⟨by positivity, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hlog : log x ≤ 8 * x ^ (1 / 8 : ℝ) := by
    have h := log_le_rpow_div (ε := 1 / 8) hx0 (by norm_num)
    convert h using 1
    ring
  have hlog₂ : (log x)^2 ≤ (8 * x ^ (1 / 8 : ℝ))^2 :=
    pow_le_pow_left₀ (log_nonneg hx1) hlog 2
  have hpsi : |psi x - x| ≤ 56 * x ^ (3 / 4 : ℝ) := by
    have hs := abs_psi_sub_self_le_seven_eighths_of_five_thousand_le hRH hx
    change |psi x - x| ≤ (7 / 8 : ℝ) * sqrt x * (log x)^2 at hs
    refine hs.trans ((mul_le_mul_of_nonneg_left hlog₂ (by positivity)).trans_eq ?_)
    have hp : (x ^ (1 / 8 : ℝ)) ^ (2 : ℕ) = x ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← rpow_mul hx0]
      norm_num
    rw [sqrt_eq_rpow, mul_pow, hp,
      show (3 / 4 : ℝ) = 1 / 2 + 1 / 4 by norm_num, rpow_add (by linarith : 0 < x)]
    ring
  have htheta : |theta x - psi x| ≤ |D| * x ^ (3 / 4 : ℝ) := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (theta_le_psi _))]
    refine (hD x).trans ?_
    rw [sqrt_eq_rpow]
    exact mul_le_mul (le_abs_self _)
      (rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (rpow_nonneg hx0 _) (abs_nonneg _)
  have he : theta x - x = (theta x - psi x) + (psi x - x) := by ring
  rw [he]
  refine (abs_add_le _ _).trans ((add_le_add htheta hpsi).trans ?_)
  rw [add_mul]
  nlinarith [rpow_nonneg hx0 (3 / 4 : ℝ)]


private theorem sixth_seventh_arithmetic (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 5000 ^ (7 : ℝ) ≤ t →
      |psi t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
        psi (t ^ (1 / 5 : ℝ)) + t ^ (1 / 6 : ℝ) - t ^ (1 / 7 : ℝ)| ≤
        C * t ^ (1 / 8 : ℝ) := by
  obtain ⟨C, hC, hθ⟩ := theta_error_of_rh hRH
  refine ⟨288 + 2 * C, by positivity, fun t ht => ?_⟩
  have ht5000 : 5000 ≤ t := le_trans
    (self_le_rpow_of_one_le (by norm_num) (by norm_num : (1 : ℝ) ≤ 7)) ht
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hroot {r : ℝ} (hr : 0 < r) (hr' : r ≤ 7) : 5000 ≤ t ^ (1 / r) := by
    have hp : (5000 : ℝ) ^ r ≤ t :=
      (rpow_le_rpow_of_exponent_le (by norm_num) hr').trans ht
    have h := rpow_le_rpow (rpow_nonneg (by norm_num) _) hp (by positivity : 0 ≤ 1 / r)
    rwa [← rpow_mul (by norm_num), mul_one_div_cancel hr.ne', rpow_one] at h
  have hθroot {r : ℝ} (hr : 6 ≤ r) (hr' : r ≤ 7) :
      |theta (t ^ (1 / r)) - t ^ (1 / r)| ≤ C * t ^ (1 / 8 : ℝ) := by
    have hr0 : 0 < r := by linarith
    refine (hθ _ (hroot hr0 hr')).trans ?_
    rw [← rpow_mul ht0.le]
    apply mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le ht1 _) hC.le
    rw [mul_comm, mul_one_div]
    exact (div_le_iff₀ hr0).mpr (by linarith)
  have htail : 4 * log t * t ^ (1 / 9 : ℝ) ≤ 288 * t ^ (1 / 8 : ℝ) := by
    have h := log_le_rpow_div (ε := 1 / 72) ht0.le (by norm_num)
    calc
      _ ≤ 4 * (t ^ (1 / 72 : ℝ) / (1 / 72)) * t ^ (1 / 9 : ℝ) := by gcongr
      _ = 288 * (t ^ (1 / 72 : ℝ) * t ^ (1 / 9 : ℝ)) := by ring
      _ = _ := by rw [← rpow_add ht0, show (1 / 72 + 1 / 9 : ℝ) = 1 / 8 by norm_num]
  let residual := psi t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
      psi (t ^ (1 / 5 : ℝ))
  let θ₆ := theta (t ^ (1 / 6 : ℝ))
  let θ₇ := theta (t ^ (1 / 7 : ℝ))
  have h := abs_psi_sub_roots_add_theta_sixth_sub_seventh_le (t := t) (by linarith)
  change |residual + θ₆ - θ₇| ≤ _ at h
  change |residual + t ^ (1 / 6 : ℝ) - t ^ (1 / 7 : ℝ)| ≤ _
  rw [show residual + t ^ (1 / 6 : ℝ) - t ^ (1 / 7 : ℝ) =
    ((residual + θ₆ - θ₇) - (θ₆ - t ^ (1 / 6 : ℝ))) + (θ₇ - t ^ (1 / 7 : ℝ)) by ring]
  calc
    _ ≤ |residual + θ₆ - θ₇| + |θ₆ - t ^ (1 / 6 : ℝ)| + |θ₇ - t ^ (1 / 7 : ℝ)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 288 * t ^ (1 / 8 : ℝ) + C * t ^ (1 / 8 : ℝ) + C * t ^ (1 / 8 : ℝ) :=
      add_le_add (add_le_add (h.trans htail) (hθroot (r := 6) (by norm_num) (by norm_num)))
        (hθroot (r := 7) (by norm_num) (by norm_num))
    _ = _ := by ring

open MeasureTheory Set

private theorem normalized_power_tail {x p : ℝ} (hx : 0 < x) (hp : p < 1) :
    Real.sqrt x * (∫ t in Ioi x, t ^ p / t ^ 2) =
      (1 - p)⁻¹ * x ^ (p - 1 / 2) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => t ^ (p - 2))
    (fun t ht => by
      change _ = t ^ (p - 2)
      rw [Real.rpow_sub (hx.trans ht), Real.rpow_two]),
    integral_Ioi_rpow_of_lt (by linarith) hx, Real.sqrt_eq_rpow,
    show p - 1 / 2 = 1 / 2 + (p - 2 + 1) by ring, Real.rpow_add hx (1 / 2) (p - 2 + 1),
    show p - 2 + 1 = -(1 - p) by ring]
  simp only [div_neg]
  ring

theorem sixth_seventh_normalized (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 5000 ^ (7 : ℝ) ≤ x →
      |Real.sqrt x * (Q x - primeTail x -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2)) +
        (6 / 5) * x ^ (-(1 / 3) : ℝ) - (7 / 6) * x ^ (-(5 / 14) : ℝ)| ≤
        C * x ^ (-(3 / 8) : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := sixth_seventh_arithmetic hRH
  refine ⟨C / (1 - 1 / 8), by positivity, ?_⟩
  intro x hx
  have hx5000 : 5000 ≤ x := le_trans
    (self_le_rpow_of_one_le (by norm_num) (by norm_num : (1 : ℝ) ≤ 7)) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have h₂ := root_kernel_integrable (p := (2 : ℝ)⁻¹) (by norm_num) hx0
  have h₃ := root_kernel_integrable (p := (3 : ℝ)⁻¹) (by norm_num) hx0
  have h₅ := root_kernel_integrable (p := (5 : ℝ)⁻¹) (by norm_num) hx0
  have hpowerI (p : ℝ) (hp : p < 1) : IntegrableOn (fun t => t ^ p / t ^ 2) (Ioi x) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := p - 2) (by linarith) hx0).congr_fun ?_ measurableSet_Ioi
    intro t ht
    change t ^ (p - 2) = t ^ p / t ^ (2 : ℕ)
    rw [Real.rpow_sub (hx0.trans ht), Real.rpow_two]
  have h₆I := hpowerI (1 / 6) (by norm_num)
  have h₇I := hpowerI (1 / 7) (by norm_num)
  have hd := diff_integrable.mono_set (Ioi_subset_Ioi hx1)
  let f (t : ℝ) := Chebyshev.psi t - Chebyshev.theta t -
    Chebyshev.psi (t ^ (2 : ℝ)⁻¹) - Chebyshev.psi (t ^ (3 : ℝ)⁻¹) -
    Chebyshev.psi (t ^ (5 : ℝ)⁻¹) + t ^ (1 / 6 : ℝ) - t ^ (1 / 7 : ℝ)
  let e (t : ℝ) := (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 -
    Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2 -
    Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2 -
    Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2
  have he : IntegrableOn e (Ioi x) := ((hd.sub h₂).sub h₃).sub h₅
  have hfn (t : ℝ) : f t / t ^ 2 = e t + t ^ (1 / 6 : ℝ) / t ^ 2 - t ^ (1 / 7 : ℝ) / t ^ 2 := by
    simp only [f, e, sub_div, add_div]
  have hf : IntegrableOn (fun t => f t / t ^ 2) (Ioi x) := by
    simp_rw [hfn]
    exact (he.add h₆I).sub h₇I
  have hform : (∫ t in Ioi x, e t) = Q x - primeTail x -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2) := by
    rw [tail_eq hx1]
    exact (integral_sub ((hd.sub h₂).sub h₃) h₅).trans
      (congrArg (· - (∫ t in Ioi x, Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2))
        ((integral_sub (hd.sub h₂) h₃).trans
          (congrArg (· - (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2))
            (integral_sub hd h₂))))
  have hI : (∫ t in Ioi x, f t / t ^ 2) =
      (∫ t in Ioi x, e t) + (∫ t in Ioi x, t ^ (1 / 6 : ℝ) / t ^ 2) -
        (∫ t in Ioi x, t ^ (1 / 7 : ℝ) / t ^ 2) := by
    refine (setIntegral_congr_fun measurableSet_Ioi (fun t _ => hfn t)).trans ?_
    exact (integral_sub (he.add h₆I) h₇I).trans
      (congrArg (· - (∫ t in Ioi x, t ^ (1 / 7 : ℝ) / t ^ 2)) (integral_add he h₆I))
  have h := normalized_tail_bound (p := 1 / 8) hx0 (by norm_num)
    hf.aestronglyMeasurable (fun t ht => by simpa [f, one_div] using hbound t (hx.trans ht.le))
  rw [hI, mul_sub, mul_add, normalized_power_tail hx0 (by norm_num : (1 / 6 : ℝ) < 1),
    normalized_power_tail hx0 (by norm_num : (1 / 7 : ℝ) < 1), hform] at h
  norm_num at h ⊢
  exact h

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
