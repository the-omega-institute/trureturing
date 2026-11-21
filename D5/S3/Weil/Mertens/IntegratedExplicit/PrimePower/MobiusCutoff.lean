/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform arithmetic and integrated tails for the Mobius prime-power truncation. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHFifthWindow
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! Finite Möbius inversion and its absolutely integrable remainder. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff (psi_root_eq_sum_multiples)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

private theorem chebyshev_mobius_cutoff {t : ℝ} (ht : 2 ≤ t) {N : ℕ}
    (hN : ⌊Real.log t / Real.log 2⌋₊ ≤ N) :
    theta t - psi t =
      ∑ d ∈ Icc 2 N, (μ d : ℝ) * psi (t ^ (1 / (d : ℝ))) := by
  have ht₁ : 1 ≤ t := by linarith
  let s := Icc 2 N
  let F (k : ℕ) := theta (t ^ (1 / (k : ℝ)))
  have hcoeff (k : ℕ) (hk : k ∈ s) :
      ∑ d ∈ s.filter (fun d => d ∣ k), (μ d : ℝ) = -1 := by
    obtain ⟨hk₂, hkN⟩ := mem_Icc.mp hk
    have hk₀ : k ≠ 0 := by omega
    have hins : insert 1 (s.filter (fun d => d ∣ k)) = k.divisors := by
      ext d
      simp only [mem_insert, mem_filter, s, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro (rfl | hd)
        · exact ⟨one_dvd k, hk₀⟩
        · exact ⟨hd.2, hk₀⟩
      · rintro ⟨hd, _⟩
        by_cases hd₁ : d = 1
        · exact Or.inl hd₁
        · have hd₀ := Nat.pos_of_dvd_of_pos hd (by omega : 0 < k)
          exact Or.inr ⟨⟨by omega, (Nat.le_of_dvd (by omega : 0 < k) hd).trans hkN⟩, hd⟩
    have hsum : ∑ d ∈ k.divisors, μ d = 0 := by
      rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply_ne (by omega)]
    have hcast := congrArg (fun n : ℤ => (n : ℝ)) hsum
    push_cast at hcast
    rw [← hins, sum_insert (by simp [s]), moebius_apply_one, Int.cast_one] at hcast
    linarith
  have hgroup :
      (∑ d ∈ s, (μ d : ℝ) * psi (t ^ (1 / (d : ℝ)))) =
        -(∑ k ∈ s, F k) := by
    calc
      _ = ∑ d ∈ s, ∑ k ∈ s.filter (fun k => d ∣ k), (μ d : ℝ) * F k := by
        apply sum_congr rfl
        intro d hd
        rw [psi_root_eq_sum_multiples ht₁ (mem_Icc.mp hd).1 hN, mul_sum]
      _ = ∑ k ∈ s, (∑ d ∈ s.filter (fun d => d ∣ k), (μ d : ℝ)) * F k := by
        simp only [sum_mul, sum_filter]
        rw [sum_comm]
        simp only [ite_mul, zero_mul]
      _ = -(∑ k ∈ s, F k) := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun k hk => by rw [hcoeff k hk, neg_one_mul]
  rw [hgroup]
  linarith only [psi_eq_theta_add_sum_theta' ht hN]

private theorem psi_root_geometric {t : ℝ} (ht : 1 ≤ t) {q n : ℕ}
    (hq : 0 < q) (hn : q ≤ n) :
    psi (t ^ (1 / (n : ℝ))) ≤
      (Real.log 4 + 4) * 2 * ((2 : ℝ) ^ (-(1 / (q : ℝ)))) ^ n * t ^ (1 / (q : ℝ)) := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast hq
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hq.trans_le hn
  have hqn : (q : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : ((2 : ℝ)^n) ^ (1 / (n : ℝ)) = 2 := by
    rw [← rpow_natCast, ← rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
      mul_one_div_cancel hn₀.ne', rpow_one]
  by_cases hs : (2 : ℝ)^n ≤ t
  · let e := 1 / (n : ℝ) - 1 / (q : ℝ)
    have he : e ≤ 0 := sub_nonpos.mpr (one_div_le_one_div_of_le hq₀ hqn)
    calc
      _ ≤ (Real.log 4 + 4) * t ^ (1 / (n : ℝ)) :=
        psi_le_const_mul_self (by positivity)
      _ = (Real.log 4 + 4) * (t ^ e * t ^ (1 / (q : ℝ))) := by
        rw [← rpow_add ht₀]
        congr 2
        dsimp [e]
        ring
      _ ≤ (Real.log 4 + 4) * (((2 : ℝ)^n) ^ e * t ^ (1 / (q : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (rpow_le_rpow_of_nonpos (by positivity) hs he) (by positivity)) (by positivity)
      _ = _ := by
        have hk : ((2 : ℝ)^n) ^ e = 2 * ((2 : ℝ) ^ (-(1 / (q : ℝ)))) ^ n := by
          calc
            _ = (2 : ℝ) ^ ((n : ℝ) * e) := by
              rw [rpow_mul (by norm_num : (0 : ℝ) ≤ 2), rpow_natCast]
            _ = (2 : ℝ) ^ (1 + (-(1 / (q : ℝ))) * (n : ℝ)) := by
              congr 1
              dsimp [e]
              field_simp
              ring
            _ = _ := by
              rw [rpow_add (by norm_num : (0 : ℝ) < 2), rpow_one,
                rpow_mul (by norm_num : (0 : ℝ) ≤ 2), rpow_natCast]
        rw [hk]
        ring
  · have hr := rpow_lt_rpow ht₀.le (lt_of_not_ge hs) (one_div_pos.mpr hn₀)
    rw [hroot] at hr
    rw [psi_eq_zero_of_lt_two hr]
    positivity

private theorem geometric_root_factor {q : ℕ} (hq : 0 < q) :
    (1 - (2 : ℝ) ^ (-(1 / (q : ℝ))))⁻¹ ≤ 1 + (q : ℝ) / Real.log 2 := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 < Real.log 2 := log_pos (by norm_num)
  let v := Real.log 2 / (q : ℝ)
  have hv : 0 < v := div_pos hlog hq₀
  have hb : (2 : ℝ) ^ (-(1 / (q : ℝ))) = (Real.exp v)⁻¹ := by
    rw [← exp_neg, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [v]
    ring
  rw [hb]
  calc
    _ ≤ (1 - (v + 1)⁻¹)⁻¹ := by
      apply inv_anti₀
      · rw [sub_pos]
        exact inv_lt_one_of_one_lt₀ (by linarith)
      · exact sub_le_sub_left (inv_anti₀ (by linarith) (add_one_le_exp v)) 1
    _ = 1 + (q : ℝ) / Real.log 2 := by
      have he : (1 - (v + 1)⁻¹)⁻¹ = 1 + v⁻¹ := by
        have hs : 1 - (v + 1)⁻¹ = v / (v + 1) := by
          field_simp
          ring
        rw [hs]
        field_simp
      rw [he]
      dsimp [v]
      rw [inv_div]

/-- The Chebyshev root sum truncates with an explicit uniform geometric tail. -/
theorem chebyshev_mobius_truncation {t : ℝ} (ht : 2 ≤ t) {m : ℕ}
    (hm : 2 ≤ m) :
    |theta t - psi t - ∑ d ∈ Icc 2 m, (μ d : ℝ) * psi (t ^ (1 / (d : ℝ)))| ≤
      (Real.log 4 + 4) * 2 * (1 + (m + 1 : ℝ) / Real.log 2) * t ^ (1 / (m + 1 : ℝ)) := by
  let N := max m ⌊Real.log t / Real.log 2⌋₊
  have hmN : m ≤ N := le_max_left _ _
  let F (d : ℕ) := (μ d : ℝ) * psi (t ^ (1 / (d : ℝ)))
  let b : ℝ := (2 : ℝ) ^ (-(1 / ((m + 1 : ℕ) : ℝ)))
  have hb₀ : 0 ≤ b := by dsimp [b]; positivity
  have hb₁ : b < 1 := by
    dsimp [b]
    exact rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos (by positivity))
  have hwhole : theta t - psi t = ∑ d ∈ Icc 2 N, F d :=
    chebyshev_mobius_cutoff ht (le_max_right _ _)
  have hsplit : (∑ d ∈ Icc 2 m, F d) + (∑ d ∈ Icc (m + 1) N, F d) =
      ∑ d ∈ Icc 2 N, F d := by
    simp only [← Ico_add_one_right_eq_Icc]
    exact sum_Ico_consecutive F (by omega) (Nat.succ_le_succ hmN)
  rw [hwhole, ← hsplit, add_sub_cancel_left]
  calc
    _ ≤ ∑ d ∈ Icc (m + 1) N, |F d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc (m + 1) N,
        ((Real.log 4 + 4) * 2 * t ^ (1 / (m + 1 : ℝ))) * b ^ d := by
      apply sum_le_sum
      intro d hd
      have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
      dsimp only [F]
      rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
      refine (mul_le_of_le_one_left (psi_nonneg _) hμ).trans ?_
      convert psi_root_geometric (show 1 ≤ t by linarith)
          (Nat.succ_pos m) (mem_Icc.mp hd).1 using 1
      simp only [b, Nat.cast_succ]
      ring
    _ ≤ ((Real.log 4 + 4) * 2 * t ^ (1 / (m + 1 : ℝ))) * (1 - b)⁻¹ := by
      rw [← mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← tsum_geometric_of_lt_one hb₀ hb₁]
      exact (summable_geometric_of_lt_one hb₀ hb₁).sum_le_tsum _ (fun i _ => pow_nonneg hb₀ i)
    _ ≤ _ := by
      have h := geometric_root_factor (q := m + 1) (Nat.succ_pos m)
      rw [Nat.cast_add, Nat.cast_one] at h
      dsimp [b]
      rw [Nat.cast_add, Nat.cast_one]
      nlinarith only [mul_le_mul_of_nonneg_left h
        (show 0 ≤ (Real.log 4 + 4) * 2 * t ^ (1 / (m + 1 : ℝ)) by positivity)]

open MeasureTheory Set
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection

/-- The same truncation transfers to the normalized prime-only tail. -/
theorem integrated_mobius_truncation {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 2 ≤ x) :
    |Real.sqrt x * (primeTail x - Q x -
      ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (∫ t in Ioi x, psi (t ^ (1 / (n : ℝ))) / t ^ 2))| ≤
      ((Real.log 4 + 4) * 2 * (1 + (m + 1 : ℝ) / Real.log 2)) /
        (1 - 1 / (m + 1 : ℝ)) * x ^ (1 / (m + 1 : ℝ) - 1 / 2) := by
  let p : ℝ := 1 / (m + 1 : ℝ)
  let g (t : ℝ) := theta t - psi t - ∑ d ∈ Finset.Icc 2 m, (μ d : ℝ) * psi (t ^ (1 / (d : ℝ)))
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  have hp₀ : (1 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast (show 1 < m + 1 by omega)
  have hp : p < 1 := one_div_lt_one_div_of_lt zero_lt_one hp₀ |>.trans_eq (by norm_num)
  have hroot (n : ℕ) (hn : n ∈ Finset.Icc 2 m) :
      IntegrableOn (fun t => (μ n : ℝ) * (psi (t ^ (1 / (n : ℝ))) / t ^ 2)) (Ioi x) := by
    have hn₂ := (mem_Icc.mp hn).1
    have hn₁ : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact (root_kernel_integrable ((one_div_lt_one_div_of_lt zero_lt_one hn₁).trans_eq (by norm_num)) hx₀).const_mul _
  have hgdiv (t : ℝ) : g t / t ^ 2 =
      -((psi t - theta t) / t ^ 2) -
        ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (psi (t ^ (1 / (n : ℝ))) / t ^ 2) := by
    dsimp [g]
    simp only [sub_div, neg_sub, sum_div, mul_div_assoc]
  have hdiff : IntegrableOn (fun t : ℝ => -((psi t - theta t) / t ^ 2)) (Ioi x) :=
    (diff_integrable.mono_set (Ioi_subset_Ioi hx₁)).neg
  have hsum : IntegrableOn (fun t : ℝ => ∑ n ∈ Finset.Icc 2 m,
      (μ n : ℝ) * (psi (t ^ (1 / (n : ℝ))) / t ^ 2)) (Ioi x) :=
    integrable_finsetSum _ hroot
  have hg : IntegrableOn (fun t : ℝ => g t / t ^ 2) (Ioi x) := by
    apply (hdiff.sub hsum).congr_fun _ measurableSet_Ioi
    intro t _
    exact (hgdiv t).symm
  have hform :
      (∫ t in Ioi x, g t / t ^ 2) = primeTail x - Q x -
        ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (∫ t in Ioi x, psi (t ^ (1 / (n : ℝ))) / t ^ 2) := by
    simp_rw [hgdiv]
    have htail := tail_eq hx₁
    change Q x - primeTail x = ∫ t in Ioi x, (psi t - theta t) / t ^ 2 at htail
    rw [integral_sub hdiff hsum, integral_neg, integral_finsetSum _ hroot, ← htail]
    simp_rw [integral_const_mul]
    ring
  rw [← hform]
  exact normalized_tail_bound hx₀ hp hg.aestronglyMeasurable
    (fun t ht => chebyshev_mobius_truncation (hx.trans ht.le) hm)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
