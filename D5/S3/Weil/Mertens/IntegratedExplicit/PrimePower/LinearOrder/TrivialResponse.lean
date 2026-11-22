/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/TrivialResponse
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/TrivialResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Abel summation of the Möbius-weighted trivial-root response. -/

import D5.S3.Weil.Mertens.Cryptids.Schoenfeld
import D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHMobiusWindow
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

open Real ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt

private def logWeightedMoebius : ArithmeticFunction ℝ :=
  ⟨fun n => (μ n : ℝ) * Real.log n, by simp⟩

private theorem logWeightedMoebius_eq : logWeightedMoebius = -(ArithmeticFunction.vonMangoldt * (μ : ArithmeticFunction ℝ)) := by
  have h : logWeightedMoebius * (ζ : ArithmeticFunction ℝ) = -ArithmeticFunction.vonMangoldt := by
    ext n
    rw [coe_mul_zeta_apply]
    simpa only [logWeightedMoebius, coe_mk, ArithmeticFunction.neg_apply, ArithmeticFunction.log_apply] using
      (sum_moebius_mul_log_eq (n := n))
  have ht := congrArg (fun f : ArithmeticFunction ℝ => f * (μ : ArithmeticFunction ℝ)) h
  calc
    _ = (-ArithmeticFunction.vonMangoldt) * (μ : ArithmeticFunction ℝ) := by
      simpa only [mul_assoc, coe_zeta_mul_coe_moebius, mul_one] using ht
    _ = _ := by
      ext n
      simp only [mul_apply, ArithmeticFunction.neg_apply, _root_.neg_mul, Finset.sum_neg_distrib]

open D5.S3.Arith.MoebiusLogarithmic (reciprocalSum abs_reciprocalSum_le_one)

private theorem inverse_three_quarters_sum {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ioc 0 N, (n : ℝ) ^ (-(3/4) : ℝ)) ≤ 4 * (N : ℝ) ^ (1/4 : ℝ) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(3/4) : ℝ)) (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    have hx₁ : (1 : ℝ) ≤ x := by simpa only [Nat.cast_one] using hx.1
    exact rpow_le_rpow_of_nonpos (by linarith) hxy (by norm_num)
  have hsum := AntitoneOn.sum_le_integral_Ico hN hanti
  have hshift : (∑ n ∈ Finset.Ico 1 N, ((n + 1 : ℕ) : ℝ) ^ (-(3/4) : ℝ)) =
      ∑ n ∈ Finset.Ioc 1 N, (n : ℝ) ^ (-(3/4) : ℝ) := by
    apply Finset.sum_bij (fun n _ => n + 1)
    · intro n hn
      rw [Finset.mem_Ico] at hn
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro n hn m hm h
      omega
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      exact ⟨n - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro n hn
      rfl
  have hsplit : Finset.Ioc 0 N = insert 1 (Finset.Ioc 1 N) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hshift, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3/4)))] at hsum
  rw [hsplit, Finset.sum_insert (by simp)]
  norm_num at hsum ⊢
  linarith

private theorem scaled_inverse_power_sum {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ioc 0 N, ((N : ℝ) / n) ^ (3/4 : ℝ)) ≤ 4 * N := by
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hf (n : ℕ) : ((N : ℝ) / n) ^ (3/4 : ℝ) =
      (N : ℝ) ^ (3/4 : ℝ) * (n : ℝ) ^ (-(3/4) : ℝ) := by
    rw [div_rpow hN₀.le (by positivity), rpow_neg (by positivity), div_eq_mul_inv]
  simp_rw [hf, ← Finset.mul_sum]
  calc
    _ ≤ (N : ℝ) ^ (3/4 : ℝ) * (4 * (N : ℝ) ^ (1/4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (inverse_three_quarters_sum hN) (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← rpow_add hN₀]
      norm_num

private theorem logWeighted_sum_eq (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, logWeightedMoebius n) =
      -(∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ) * Chebyshev.psi ((N : ℝ) / n)) := by
  rw [logWeightedMoebius_eq]
  simp_rw [ArithmeticFunction.neg_apply, Finset.sum_neg_distrib]
  congr 1
  rw [mul_comm, sum_Ioc_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro n hn
  unfold Chebyshev.psi
  rw [Nat.floor_div_natCast, Nat.floor_natCast]
  rfl

private theorem moebius_log_saving_of_psi_bound {C : ℝ} (hC : 0 ≤ C)
    (hψ : ∀ y ≥ 1, |Chebyshev.psi y - y| ≤ C * y ^ (3/4 : ℝ))
    {N : ℕ} (hN : 2 ≤ N) :
    |(∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ))| * Real.log N ≤ (17 + 4 * C) * (N : ℝ) := by
  have hN₂ : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0 : ℝ) < N := by linarith
  let S := Finset.Ioc 0 N
  have harg (n : ℕ) (hn : n ∈ S) : 1 ≤ (N : ℝ) / n := by
    obtain ⟨hn₀, hnN⟩ := Finset.mem_Ioc.mp hn
    exact (one_le_div (show (0 : ℝ) < n by exact_mod_cast hn₀)).mpr (by exact_mod_cast hnN)
  have hμ (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
  have hmain : |∑ n ∈ S, (μ n : ℝ) * ((N : ℝ) / n)| ≤ N := by
    have h : (∑ n ∈ S, (μ n : ℝ) * ((N : ℝ) / n)) = N * reciprocalSum N := by
      unfold reciprocalSum
      rw [Nat.floor_natCast, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h, abs_mul, abs_of_pos hN₀]
    exact mul_le_of_le_one_right hN₀.le (abs_reciprocalSum_le_one _)
  have herror : |∑ n ∈ S, (μ n : ℝ) * (Chebyshev.psi ((N : ℝ) / n) - (N : ℝ) / n)| ≤
      4 * C * (N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ S, |(μ n : ℝ) * (Chebyshev.psi ((N : ℝ) / n) - (N : ℝ) / n)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S, C * ((N : ℝ) / n) ^ (3/4 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hμ n)).trans (hψ _ (harg n hn))
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact (mul_le_mul_of_nonneg_left (scaled_inverse_power_sum (by omega : 1 ≤ N)) hC).trans_eq (by ring)
  have hweighted : |∑ n ∈ S, logWeightedMoebius n| ≤ (1 + 4 * C) * (N : ℝ) := by
    dsimp only [S]
    rw [logWeighted_sum_eq, abs_neg]
    have heq : (∑ n ∈ S, (μ n : ℝ) * Chebyshev.psi ((N : ℝ) / n)) =
        (∑ n ∈ S, (μ n : ℝ) * ((N : ℝ) / n)) +
          (∑ n ∈ S, (μ n : ℝ) * (Chebyshev.psi ((N : ℝ) / n) - (N : ℝ) / n)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    change |∑ n ∈ S, _| ≤ _
    rw [heq]
    exact (abs_add_le _ _).trans ((add_le_add hmain herror).trans_eq (by ring))
  have hlog : |∑ n ∈ S, (μ n : ℝ) * Real.log ((N : ℝ) / n)| ≤ 16 * (N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ S, |(μ n : ℝ) * Real.log ((N : ℝ) / n)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S, 4 * ((N : ℝ) / n) ^ (3/4 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hy := harg n hn
        have hpos : 0 ≤ (N : ℝ) / n := by linarith
        rw [abs_mul, abs_of_nonneg (Real.log_nonneg hy)]
        refine (mul_le_of_le_one_left (Real.log_nonneg hy) (hμ n)).trans ?_
        have h := Real.log_le_rpow_div (ε := (1/4 : ℝ)) hpos (by norm_num)
        have hpow := rpow_le_rpow_of_exponent_le hy (show (1/4 : ℝ) ≤ 3/4 by norm_num)
        linarith
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact (mul_le_mul_of_nonneg_left (scaled_inverse_power_sum (by omega : 1 ≤ N))
          (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)
  have he : (∑ n ∈ S, (μ n : ℝ)) * Real.log N =
      (∑ n ∈ S, logWeightedMoebius n) + (∑ n ∈ S, (μ n : ℝ) * Real.log ((N : ℝ) / n)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn₀ : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.mem_Ioc.mp hn).1.ne'
    change _ = (μ n : ℝ) * Real.log n + (μ n : ℝ) * Real.log ((N : ℝ) / n)
    rw [Real.log_div hN₀.ne' hn₀]
    ring
  change |∑ n ∈ S, (μ n : ℝ)| * Real.log N ≤ _
  rw [← abs_of_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ N)), ← abs_mul, he]
  exact (abs_add_le _ _).trans ((add_le_add hweighted hlog).trans_eq (by ring))

open ConjectureMachines.Semantics.Riemann
  (SchoenfeldPsiBound abs_psi_sub_self_le_seven_eighths_of_five_thousand_le)

private theorem psi_three_quarters_of_rh (hRH : RiemannHypothesis) :
    ∀ y ≥ 1, |Chebyshev.psi y - y| ≤ ((Real.log 4 + 5) * 5000 + 56) * y ^ (3/4 : ℝ) := by
  intro y hy
  have hy₀ : 0 < y := by linarith
  have hcoef : 0 ≤ (Real.log 4 + 5) * 5000 := by positivity
  by_cases h : 5000 ≤ y
  · have hψ := abs_psi_sub_self_le_seven_eighths_of_five_thousand_le hRH h
    unfold SchoenfeldPsiBound at hψ
    have hlog : Real.log y ≤ 8 * y ^ (1/8 : ℝ) := by
      have h := Real.log_le_rpow_div (ε := (1/8 : ℝ)) hy₀.le (by norm_num)
      convert h using 1
      ring
    calc
      _ ≤ (7/8 : ℝ) * Real.sqrt y * (Real.log y)^2 := hψ
      _ ≤ (7/8 : ℝ) * Real.sqrt y * (8 * y ^ (1/8 : ℝ))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_nonneg hy) hlog 2) (by positivity)
      _ = 56 * y ^ (3/4 : ℝ) := by
        have hquarter : (y ^ (1/8 : ℝ)) ^ (2 : ℕ) = y ^ (1/4 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hy₀.le]
          norm_num
        rw [Real.sqrt_eq_rpow, mul_pow, hquarter]
        calc
          _ = 56 * (y ^ (1/2 : ℝ) * y ^ (1/4 : ℝ)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hy₀, show (1/2 : ℝ) + 1/4 = 3/4 by norm_num]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hψ := Chebyshev.psi_le_const_mul_self hy₀.le
    have hp := Chebyshev.psi_nonneg y
    have hpower : 1 ≤ y ^ (3/4 : ℝ) := Real.one_le_rpow hy (by norm_num)
    calc
      _ ≤ Chebyshev.psi y + y := by
        simpa only [abs_of_nonneg hp, abs_of_nonneg hy₀.le] using abs_sub (Chebyshev.psi y) y
      _ ≤ (Real.log 4 + 5) * y := by linarith
      _ ≤ (Real.log 4 + 5) * 5000 :=
        mul_le_mul_of_nonneg_left (le_of_not_ge h) (by positivity)
      _ ≤ ((Real.log 4 + 5) * 5000 + 56) * y ^ (3/4 : ℝ) :=
        (le_mul_of_one_le_right hcoef hpower).trans
          (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

theorem moebius_log_saving_of_rh (hRH : RiemannHypothesis) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 2 ≤ N →
      |(∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ))| * Real.log N ≤ D * (N : ℝ) := by
  let C : ℝ := (Real.log 4 + 5) * 5000 + 56
  exact ⟨17 + 4 * C, by dsimp [C]; positivity, fun N hN =>
    moebius_log_saving_of_psi_bound (C := C) (by dsimp [C]; positivity) (psi_three_quarters_of_rh hRH) hN⟩

private theorem abs_moebius_prefix_le_card (k : ℕ) :
    |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ (k : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 k, |(μ n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ioc 0 k, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
      exact_mod_cast abs_moebius_le_one (n := i)
    _ = _ := by simp [Nat.card_Ioc, nsmul_eq_mul]

theorem moebius_uniform_prefix_log_saving (hRH : RiemannHypothesis) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 2 ≤ N → ∀ k ≤ N,
      |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| * Real.log N ≤ D * N := by
  obtain ⟨C, hC, hM⟩ := moebius_log_saving_of_rh hRH
  refine ⟨2*C+2, by positivity, fun N hN k hk => ?_⟩
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  by_cases hcase : Real.sqrt (N : ℝ) < k
  · have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr (by linarith)
    have hk1 : (1 : ℝ) < k := hsqrt.trans_lt hcase
    have hk2 : 2 ≤ k := by exact_mod_cast hk1
    have hl := Real.log_le_log (Real.sqrt_pos_of_pos hN0) hcase.le
    rw [Real.log_sqrt hN0.le] at hl
    calc
      _ ≤ |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| * (2 * Real.log k) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ ≤ (2*C)*(N : ℝ) := by
        have ht := mul_le_mul_of_nonneg_left (hM k hk2) (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith only [ht, mul_le_mul_of_nonneg_left hk' hC.le]
      _ ≤ _ := by nlinarith only [hN0.le]
  · have hl := Real.log_le_rpow_div hN0.le (show (0 : ℝ) < 1/2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hl
    calc
      _ ≤ Real.sqrt (N : ℝ) * (Real.sqrt (N : ℝ)/(1/2)) :=
        mul_le_mul ((abs_moebius_prefix_le_card k).trans (le_of_not_gt hcase)) hl hlog
          (Real.sqrt_nonneg _)
      _ ≤ _ := by
        nlinarith only [Real.sq_sqrt hN0.le, mul_nonneg hC.le hN0.le]

private theorem abs_sum_mul_antitone_Ioc_le {a w : ℕ → ℝ} {B : ℝ} {m N : ℕ}
    (hmN : m < N)
    (hprefix : ∀ k ≤ N, |∑ i ∈ range (k + 1), a i| ≤ B)
    (hw0 : ∀ i ∈ Ioc m N, 0 ≤ w i)
    (hw : AntitoneOn w (Set.Ioc m N)) :
    |∑ i ∈ Ioc m N, a i * w i| ≤ 2 * B * w (m + 1) := by
  let A : ℕ → ℝ := fun k => ∑ i ∈ range (k + 1), a i
  have hN0 := hw0 N (mem_Ioc.mpr ⟨hmN, le_rfl⟩)
  have hm0 := hw0 (m + 1) (mem_Ioc.mpr ⟨by omega, hmN⟩)
  have hd (i : ℕ) (hi : i ∈ Ico (m + 1) N) : 0 ≤ w i - w (i + 1) := by
    obtain ⟨hi₁, hi₂⟩ := mem_Ico.mp hi
    exact sub_nonneg.mpr (hw ⟨by omega, hi₂.le⟩ ⟨by omega, hi₂⟩ (Nat.le_succ i))
  have heq : (∑ i ∈ Ioc m N, a i * w i) =
      w N * A N - w (m + 1) * A m +
        ∑ i ∈ Ico (m + 1) N, (w i - w (i + 1)) * A i := by
    rw [← Ico_add_one_add_one_eq_Ioc]
    have h := sum_Ico_by_parts w a (m := m + 1) (n := N + 1) (by omega)
    simp only [Nat.add_sub_cancel, smul_eq_mul] at h
    simp_rw [mul_comm (a _) (w _)]
    rw [h, sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    ring
  have htel : (∑ i ∈ Ico (m + 1) N, (w i - w (i + 1))) = w (m + 1) - w N := by
    rw [sum_Ico_eq_sub _ hmN, sum_range_sub', sum_range_sub']
    ring
  rw [heq]
  calc
    _ ≤ |w N * A N - w (m + 1) * A m| +
        |∑ i ∈ Ico (m + 1) N, (w i - w (i + 1)) * A i| := abs_add_le _ _
    _ ≤ (w N * B + w (m + 1) * B) +
        ∑ i ∈ Ico (m + 1) N, (w i - w (i + 1)) * B := by
      apply add_le_add
      · apply (abs_sub _ _).trans
        rw [abs_mul, abs_mul, abs_of_nonneg hN0, abs_of_nonneg hm0]
        exact add_le_add (mul_le_mul_of_nonneg_left (hprefix N le_rfl) hN0)
          (mul_le_mul_of_nonneg_left (hprefix m hmN.le) hm0)
      · apply (abs_sum_le_sum_abs _ _).trans
        refine sum_le_sum fun i hi => ?_
        rw [abs_mul, abs_of_nonneg (hd i hi)]
        exact mul_le_mul_of_nonneg_left (hprefix i (mem_Ico.mp hi).2.le) (hd i hi)
    _ = _ := by rw [← sum_mul, htel]; ring

private def mertensWeight (y : ℝ) : ℝ :=
  (⌊y⌋₊ : ℝ) - Chebyshev.psi y + Real.log y

private theorem moebius_log_eq_weight {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Ioc 0 N, (μ n : ℝ)) * Real.log N =
      -1 + ∑ n ∈ Ioc 0 N, (μ n : ℝ) * mertensWeight ((N : ℝ) / n) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hfloor := D5.S3.Arith.MoebiusLogarithmic.floor_cancellation hN'
  rw [Nat.floor_natCast] at hfloor
  have hlog : (∑ n ∈ Ioc 0 N, (μ n : ℝ)) * Real.log N =
      (∑ n ∈ Ioc 0 N, logWeightedMoebius n) +
        ∑ n ∈ Ioc 0 N, (μ n : ℝ) * Real.log ((N : ℝ) / n) := by
    rw [sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.mp hn).1.ne'
    change _ = (μ n : ℝ) * Real.log n + (μ n : ℝ) * Real.log ((N : ℝ) / n)
    rw [Real.log_div hN0 hn0]
    ring
  rw [hlog, logWeighted_sum_eq]
  simp only [mertensWeight, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, hfloor]
  ring

private theorem abs_mertensWeight_le {C : ℝ}
    (hψ : ∀ y ≥ 1, |Chebyshev.psi y - y| ≤ C * y ^ (3/4 : ℝ))
    {y : ℝ} (hy : 1 ≤ y) :
    |mertensWeight y| ≤ (C + 5) * y ^ (3/4 : ℝ) := by
  have hy0 : 0 ≤ y := by linarith
  have hfloor : |(⌊y⌋₊ : ℝ) - y| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le hy0))]
    linarith [Nat.lt_floor_add_one y]
  have hlog : |Real.log y| ≤ 4 * y ^ (3/4 : ℝ) := by
    rw [abs_of_nonneg (Real.log_nonneg hy)]
    have h := Real.log_le_rpow_div (ε := (1/4 : ℝ)) hy0 (by norm_num)
    have hpow := Real.rpow_le_rpow_of_exponent_le hy (show (1/4 : ℝ) ≤ 3/4 by norm_num)
    linarith
  have hp : 1 ≤ y ^ (3/4 : ℝ) := Real.one_le_rpow hy (by norm_num)
  rw [show mertensWeight y = ((⌊y⌋₊ : ℝ) - y) - (Chebyshev.psi y - y) + Real.log y by
    unfold mertensWeight
    ring]
  calc
    _ ≤ (|(⌊y⌋₊ : ℝ) - y| + |Chebyshev.psi y - y|) + |Real.log y| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ (C + 5) * y ^ (3/4 : ℝ) := by linarith [hψ y hy]

private theorem abs_mertensWeight_head_le {C L : ℝ} (hC : 0 ≤ C)
    (hψ : ∀ y ≥ 1, |Chebyshev.psi y - y| ≤ C * y ^ (3/4 : ℝ))
    {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) (hL : 0 < L) (hmL : (m : ℝ) ≤ N / L) :
    |∑ n ∈ Ioc 0 m, (μ n : ℝ) * mertensWeight ((N : ℝ) / n)| ≤
      4 * (C + 5) * (N / L ^ (1/4 : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp (n : ℕ) : ((N : ℝ) / n) ^ (3/4 : ℝ) =
      (N : ℝ) ^ (3/4 : ℝ) * (n : ℝ) ^ (-(3/4) : ℝ) := by
    rw [div_rpow hN.le (by positivity), rpow_neg (by positivity), div_eq_mul_inv]
  calc
    _ ≤ ∑ n ∈ Ioc 0 m, |(μ n : ℝ) * mertensWeight ((N : ℝ) / n)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 m, (C + 5) * ((N : ℝ) / n) ^ (3/4 : ℝ) := by
      refine sum_le_sum fun n hn => ?_
      obtain ⟨hn0, hnm⟩ := mem_Ioc.mp hn
      have harg : 1 ≤ (N : ℝ) / n :=
        (one_le_div (by exact_mod_cast hn0)).mpr (by exact_mod_cast hnm.trans hmN)
      rw [abs_mul]
      refine (mul_le_of_le_one_left (abs_nonneg _) ?_).trans (abs_mertensWeight_le hψ harg)
      exact_mod_cast abs_moebius_le_one (n := n)
    _ ≤ (C + 5) * (N : ℝ) ^ (3/4 : ℝ) * (4 * (m : ℝ) ^ (1/4 : ℝ)) := by
      conv_lhs => simp only [hp, ← mul_assoc, ← mul_sum]
      apply mul_le_mul_of_nonneg_left (inverse_three_quarters_sum hm)
      positivity
    _ ≤ (C + 5) * (N : ℝ) ^ (3/4 : ℝ) * (4 * ((N : ℝ) / L) ^ (1/4 : ℝ)) := by
      gcongr
    _ = _ := by
      rw [Real.div_rpow hN.le hL.le]
      calc
        _ = 4 * (C + 5) * (((N : ℝ) ^ (3/4 : ℝ) * (N : ℝ) ^ (1/4 : ℝ)) / L ^ (1/4 : ℝ)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hN]
          norm_num

private theorem abs_mertensWeight_tail_le {B L : ℝ} {m N : ℕ}
    (hB : 0 ≤ B) (hL : 1 ≤ L) (hmL : (N : ℝ) / L < (m : ℝ) + 1)
    (hprefix : ∀ k ≤ N, |∑ n ∈ Ioc 0 k, (μ n : ℝ)| ≤ B) :
    |∑ n ∈ Ioc m N, (μ n : ℝ) * mertensWeight ((N : ℝ) / n)| ≤
      2 * B * (L + Chebyshev.psi L + Real.log L) := by
  have hL0 : 0 < L := by linarith
  by_cases hm : m < N
  swap
  · rw [Ioc_eq_empty_of_le (le_of_not_gt hm), sum_empty, abs_zero]
    exact mul_nonneg (by positivity) (by
      have := Chebyshev.psi_nonneg L
      have := Real.log_nonneg hL
      linarith)
  have hrange (k : ℕ) : range (k + 1) = insert 0 (Ioc 0 k) := by
    ext i
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  have hpref (k : ℕ) (hk : k ≤ N) : |∑ n ∈ range (k + 1), (μ n : ℝ)| ≤ B := by
    rw [hrange, sum_insert (by simp)]
    simpa using hprefix k hk
  let q : ℕ → ℝ := fun n => N / (n : ℝ)
  have harg (n : ℕ) (hn : n ∈ Set.Ioc m N) : 1 ≤ q n := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le m).trans_lt hn.1
    exact (one_le_div hn0).mpr (by exact_mod_cast hn.2)
  have hq : AntitoneOn q (Set.Ioc m N) := by
    intro i hi j _ hij
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (Nat.zero_le m).trans_lt hi.1
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) hi0 (by exact_mod_cast hij)
  have hmax : q (m + 1) ≤ L := by
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    dsimp [q]
    rw [Nat.cast_add, Nat.cast_one]
    exact (div_le_iff₀ hm0).mpr (by linarith [(div_lt_iff₀ hL0).mp hmL])
  have hbound (w : ℝ → ℝ) (hw : MonotoneOn w (Set.Ici 1))
      (hw0 : ∀ y ≥ 1, 0 ≤ w y) :
      |∑ n ∈ Ioc m N, (μ n : ℝ) * w (q n)| ≤ 2 * B * w L := by
    have hfirst := harg (m + 1) ⟨by omega, hm⟩
    refine (abs_sum_mul_antitone_Ioc_le hm hpref (w := fun n => w (q n)) ?_ ?_).trans ?_
    · intro n hn
      exact hw0 _ (harg n (mem_Ioc.mp hn))
    · intro i hi j hj hij
      exact hw (harg j hj) (harg i hi) (hq hi hj hij)
    · exact mul_le_mul_of_nonneg_left (hw hfirst hL hmax) (by positivity)
  have hf := hbound (fun y => (⌊y⌋₊ : ℝ))
    ((Nat.mono_cast.comp Nat.floor_mono).monotoneOn _) (fun y _ => Nat.cast_nonneg _)
  have hψ := hbound Chebyshev.psi (Chebyshev.psi_mono.monotoneOn _) (fun y _ => Chebyshev.psi_nonneg y)
  have hlog := hbound Real.log
    (fun _ hx _ _ hxy => Real.log_le_log (lt_of_lt_of_le zero_lt_one hx) hxy)
    (fun _ hy => Real.log_nonneg hy)
  have hf' : |∑ n ∈ Ioc m N, (μ n : ℝ) * (⌊q n⌋₊ : ℝ)| ≤ 2 * B * L :=
    hf.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hL0.le) (by positivity))
  unfold mertensWeight
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  change |(∑ n ∈ Ioc m N, (μ n : ℝ) * (⌊q n⌋₊ : ℝ)) -
    (∑ n ∈ Ioc m N, (μ n : ℝ) * Chebyshev.psi (q n)) +
    (∑ n ∈ Ioc m N, (μ n : ℝ) * Real.log (q n))| ≤ _
  exact (abs_add_le _ _).trans ((add_le_add ((abs_sub _ _).trans (add_le_add hf' hψ)) hlog).trans_eq
    (by ring))

private theorem moebius_log_sublinear_of_rh (hRH : RiemannHypothesis) :
    ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ N ≥ K,
      |∑ n ∈ Ioc 0 N, (μ n : ℝ)| * Real.log N ≤ ε * (N : ℝ) := by
  intro ε hε
  let C : ℝ := (Real.log 4 + 5) * 5000 + 56
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨D, hD, hprefix⟩ := moebius_uniform_prefix_log_saving hRH
  -- Fix the quotient cutoff before choosing the threshold for N.
  let T : ℝ := 1 + 16 * (C + 5) / ε
  have hT : 1 ≤ T := le_add_of_nonneg_right (by positivity)
  let L : ℝ := T ^ (4 : ℕ)
  have hL : 1 ≤ L := one_le_pow₀ hT
  have hL0 : 0 < L := by linarith
  have hLroot : L ^ (1/4 : ℝ) = T := by
    dsimp [L]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ T)]
    norm_num
  let W := L + Chebyshev.psi L + Real.log L
  have hW : 0 ≤ W := by
    dsimp [W]
    linarith [Chebyshev.psi_nonneg L, Real.log_nonneg hL]
  let H := 8 * D * W / ε
  obtain ⟨K, hK⟩ := exists_nat_ge (max L (max 2 (max (4 / ε) (Real.exp H))))
  refine ⟨K, fun N hKN => ?_⟩
  have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hN : max L (max 2 (max (4 / ε) (Real.exp H))) ≤ (N : ℝ) := hK.trans hKN'
  obtain ⟨hLN, hN₂, hNε, hNH⟩ := by simpa only [max_le_iff] using hN
  have hN₂' : 2 ≤ N := by exact_mod_cast hN₂
  have hN0 : (0 : ℝ) < N := by positivity
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlogH : H ≤ Real.log (N : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos H) hNH
  let m := ⌊(N : ℝ) / L⌋₊
  have hm1 : 1 ≤ m := Nat.le_floor (by simpa using (one_le_div hL0).mpr hLN)
  have hmL : (m : ℝ) ≤ (N : ℝ) / L := Nat.floor_le (by positivity)
  have hmN : m ≤ N := by
    exact_mod_cast hmL.trans (div_le_self hN0.le hL)
  have hmL' : (N : ℝ) / L < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsmall : 4 * (C + 5) * ((N : ℝ) / L ^ (1/4 : ℝ)) ≤ ε / 4 * (N : ℝ) := by
    have hT0 : 0 < T := by linarith
    have hTε : 16 * (C + 5) / ε ≤ T := by dsimp [T]; linarith
    have hcoef : 4 * (C + 5) / T ≤ ε / 4 := by
      apply (div_le_iff₀ hT0).mpr
      linarith only [(div_le_iff₀ hε).mp hTε]
    rw [hLroot]
    calc
      _ = (4 * (C + 5) / T) * (N : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hN0.le
  let B := D * (N : ℝ) / Real.log N
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpref (k : ℕ) (hk : k ≤ N) : |∑ n ∈ Ioc 0 k, (μ n : ℝ)| ≤ B :=
    (le_div_iff₀ hlog).mpr (hprefix N hN₂' k hk)
  have hlarge : 2 * B * W ≤ ε / 4 * (N : ℝ) := by
    have hcoef : 2 * D * W / Real.log N ≤ ε / 4 := by
      apply (div_le_iff₀ hlog).mpr
      linarith only [(div_le_iff₀ hε).mp hlogH]
    calc
      _ = (2 * D * W / Real.log N) * (N : ℝ) := by dsimp [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hN0.le
  have hone : 1 ≤ ε / 4 * (N : ℝ) := by linarith only [(div_le_iff₀ hε).mp hNε]
  have hhead := (abs_mertensWeight_head_le hC (psi_three_quarters_of_rh hRH) hm1 hmN hL0 hmL).trans hsmall
  have htail := (abs_mertensWeight_tail_le hB hL hmL' hpref).trans hlarge
  rw [← abs_of_pos hlog, ← abs_mul, moebius_log_eq_weight (by omega : 1 ≤ N),
    ← Ioc_union_Ioc_eq_Ioc (Nat.zero_le m) hmN,
    sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  calc
    _ ≤ |(-1 : ℝ)| + (|∑ n ∈ Ioc 0 m, (μ n : ℝ) * mertensWeight ((N : ℝ) / n)| +
        |∑ n ∈ Ioc m N, (μ n : ℝ) * mertensWeight ((N : ℝ) / n)|) :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ _ := by
      rw [abs_neg, abs_one]
      linarith only [hone, hhead, htail, mul_nonneg hε.le hN0.le]

/-- Under RH, the Möbius prefixes are uniformly little-o of `N / log N` up to `N`. -/
theorem moebius_uniform_prefix_log_sublinear_of_rh (hRH : RiemannHypothesis) :
    ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ N ≥ K, ∀ k ≤ N,
      |∑ n ∈ Ioc 0 k, (μ n : ℝ)| * Real.log N ≤ ε * (N : ℝ) := by
  intro ε hε
  obtain ⟨J, hJ⟩ := moebius_log_sublinear_of_rh hRH (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_ge (max 2 (max ((J : ℝ) ^ 2) ((4 / ε) ^ 4)))
  refine ⟨K, fun N hKN k hkN => ?_⟩
  have hN := hK.trans (show (K : ℝ) ≤ N by exact_mod_cast hKN)
  obtain ⟨hN₂, hNJ, hNε⟩ := by simpa only [max_le_iff] using hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
  -- Above the square-root cutoff, log N is at most twice log k.
  by_cases hk : Real.sqrt (N : ℝ) < k
  · have hJsqrt : (J : ℝ) ≤ Real.sqrt (N : ℝ) := by
      simpa only [Real.sqrt_sq (Nat.cast_nonneg J)] using Real.sqrt_le_sqrt hNJ
    have hJk : J ≤ k := by exact_mod_cast hJsqrt.trans hk.le
    have hlog := Real.log_le_log (Real.sqrt_pos_of_pos hN0) hk.le
    rw [Real.log_sqrt hN0.le] at hlog
    calc
      _ ≤ |∑ n ∈ Ioc 0 k, (μ n : ℝ)| * (2 * Real.log k) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ ≤ ε * (k : ℝ) := by
        have h := mul_le_mul_of_nonneg_left (hJ k hJk) (by norm_num : (0 : ℝ) ≤ 2)
        linarith only [h]
      _ ≤ _ := mul_le_mul_of_nonneg_left hkN' hε.le
  · have hlog := Real.log_le_rpow_div (ε := (1/4 : ℝ)) hN0.le (by norm_num)
    have hquarter : 4 / ε ≤ (N : ℝ) ^ (1/4 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity : 0 ≤ (4 / ε) ^ 4) hNε
        (by norm_num : (0 : ℝ) ≤ 1/4)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 4 / ε),
        show (↑(4 : ℕ) : ℝ) * (1/4 : ℝ) = 1 by norm_num, Real.rpow_one] at h
    have hcoef : 4 ≤ ε * (N : ℝ) ^ (1/4 : ℝ) := by
      linarith only [(div_le_iff₀ hε).mp hquarter]
    have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
    calc
      _ ≤ Real.sqrt (N : ℝ) * (4 * (N : ℝ) ^ (1/4 : ℝ)) :=
        mul_le_mul ((abs_moebius_prefix_le_card k).trans (le_of_not_gt hk))
          (by linarith) hlog0 (Real.sqrt_nonneg _)
      _ = 4 * (N : ℝ) ^ (3/4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, mul_left_comm, ← Real.rpow_add hN0]
        norm_num
      _ ≤ (ε * (N : ℝ) ^ (1/4 : ℝ)) * (N : ℝ) ^ (3/4 : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hN0]
        norm_num

private theorem monotone_finite_abel_bound {N : ℕ} {a g : ℕ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hg0 : 0 ≤ g 0) (hg : Monotone g)
    (ha : ∀ n ≤ N+1, |∑ i ∈ Finset.range n, a i| ≤ L) :
    |∑ i ∈ Finset.range (N+1), a i * g i| ≤ 2*L*g N := by
  have hvar (M : ℕ) : ∑ i ∈ Finset.range M, (g (i+1)-g i) = g M-g 0 := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hlast : 0 ≤ g N := hg0.trans (hg (Nat.zero_le _))
  rw [show (∑ i ∈ Finset.range (N+1), a i * g i) =
      (∑ i ∈ Finset.range (N+1), a i) * g N -
        ∑ i ∈ Finset.range N, (∑ j ∈ Finset.range (i+1), a j) * (g (i+1) - g i) from
      by simpa only [Nat.add_sub_cancel, smul_eq_mul] using Finset.sum_range_by_parts' a g (N+1)]
  calc
    _ ≤ |(∑ i ∈ Finset.range (N+1), a i) * g N| +
        |∑ i ∈ Finset.range N, (∑ j ∈ Finset.range (i+1), a j) * (g (i+1) - g i)| := abs_sub _ _
    _ ≤ L * g N + L * (g N-g 0) := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hlast]
        exact mul_le_mul_of_nonneg_right (ha _ le_rfl) hlast
      · rw [← hvar, Finset.mul_sum]
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        have hd : 0 ≤ g (i+1)-g i := sub_nonneg.mpr (hg (Nat.le_succ _))
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (ha _ (by have := Finset.mem_range.mp hi; omega)) hd
    _ ≤ _ := by nlinarith only [mul_nonneg hL hg0]

private def activeMoebius (i : ℕ) : ℝ := if 2 ≤ i then (μ i : ℝ) else 0

private theorem active_moebius_range (n : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (n+1), activeMoebius i * f i =
      ∑ i ∈ Finset.Icc 2 n, (μ i : ℝ) * f i := by
  unfold activeMoebius
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

private theorem active_moebius_prefix_log (hRH : RiemannHypothesis) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 2 ≤ N → ∀ n ≤ N+1,
      |∑ i ∈ Finset.range n, activeMoebius i| * Real.log N ≤ D*N := by
  obtain ⟨C, hC, hM⟩ := moebius_uniform_prefix_log_saving hRH
  refine ⟨C+1, by positivity, fun N hN n hn => ?_⟩
  have hN₂ : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero, zero_mul]
    positivity
  | succ k =>
    have hk : k ≤ N := by omega
    rcases lt_or_ge k 2 with hl | hl
    · have hzero : ∀ i ∈ Finset.range (k+1), activeMoebius i = 0 := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact ite_eq_right (by omega)
      rw [Finset.sum_eq_zero hzero, abs_zero, zero_mul]
      positivity
    · have hI : insert 1 (Finset.Icc 2 k) = Finset.Ioc 0 k := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      have he : (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ)) =
          1 + ∑ i ∈ Finset.Icc 2 k, (μ i : ℝ) := by
        rw [← hI, Finset.sum_insert (by simp)]
        simp
      have hs := active_moebius_range k (fun _ => 1)
      simp only [mul_one] at hs
      rw [hs, show (∑ i ∈ Finset.Icc 2 k, (μ i : ℝ)) =
        (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ))-1 by linarith only [he]]
      calc
        _ ≤ (|(∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ))| + 1) * Real.log N := by
          apply mul_le_mul_of_nonneg_right _ hlog
          simpa using abs_sub (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ)) 1
        _ ≤ _ := by
          rw [add_mul, one_mul, add_mul, one_mul]
          exact add_le_add (hM N hN k hk) (Real.log_le_self (by linarith))

private theorem moebius_monotone_log_weight_bound (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 2 ≤ N → ∀ g : ℕ → ℝ,
      0 ≤ g 0 → Monotone g → g N ≤ (1 + Real.log N) / 2 →
      |∑ i ∈ Finset.Icc 2 N, (μ i : ℝ) * g i| ≤ K*N := by
  obtain ⟨D, hD, hpre⟩ := active_moebius_prefix_log hRH
  let d := Real.log 2
  have hd : 0 < d := Real.log_pos (by norm_num)
  refine ⟨D*(1+1/d), by positivity, fun N hN g hg0 hg hgn => ?_⟩
  have hN₂ : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hld : d ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hN₂
  have hl : 0 < Real.log (N : ℝ) := hd.trans_le hld
  let L := D * (N : ℝ) / Real.log N
  have hL : 0 ≤ L := by
    dsimp [L]
    exact div_nonneg (by positivity) hl.le
  have hP : ∀ n ≤ N+1, |∑ i ∈ Finset.range n, activeMoebius i| ≤ L :=
    fun n hn => (le_div_iff₀ hl).mpr (hpre N hN n hn)
  rw [← active_moebius_range]
  calc
    _ ≤ 2 * L * g N := monotone_finite_abel_bound hL hg0 hg hP
    _ ≤ 2 * L * ((1 + Real.log N) / 2) :=
      mul_le_mul_of_nonneg_left hgn (by positivity)
    _ = D * (N : ℝ) * (1+1/Real.log N) := by
      dsimp [L]
      field_simp
      ring
    _ ≤ _ := by
      have ht := add_le_add_right (one_div_le_one_div_of_le hd hld) (1 : ℝ)
      exact (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ D * (N : ℝ))).trans_eq (by ring)

open D5.S3.Weil.Mertens.IntegratedExplicit

private def trivialRootResponse (u : ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, (n : ℝ) / (trivialHeight k * ((n : ℝ)+trivialHeight k)) *
    Real.exp (-(trivialHeight k) * (u / (n : ℝ)))

private theorem trivialRootResponse_nonneg (u : ℝ) (n : ℕ) : 0 ≤ trivialRootResponse u n := by
  unfold trivialRootResponse
  exact tsum_nonneg fun k => by unfold trivialHeight; positivity

private theorem trivialRootMass_summable (n : ℕ) :
    Summable (fun k : ℕ => (n : ℝ) / (trivialHeight k * ((n : ℝ)+trivialHeight k))) := by
  cases n with
  | zero => simp
  | succ n =>
    have hnonneg (k : ℕ) : 0 ≤ ((n.succ : ℕ) : ℝ) /
        (trivialHeight k * (((n.succ : ℕ) : ℝ) + trivialHeight k)) := by
      unfold trivialHeight
      positivity
    apply Summable.of_nonneg_of_le hnonneg _
      (trivialCoeff_hasSum.summable.mul_left ((n.succ : ℕ) : ℝ))
    intro k
    have hn : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast Nat.succ_pos n
    have hk : 0 < trivialHeight k := by unfold trivialHeight; positivity
    change _ ≤ _ * (1 / (trivialHeight k * (trivialHeight k + 1)))
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith) hk.le)

private theorem trivialRootResponse_monotone {u : ℝ} (hu : 0 ≤ u) :
    Monotone (trivialRootResponse u) := by
  let term (n k : ℕ) := (n : ℝ) / (trivialHeight k * ((n : ℝ)+trivialHeight k)) *
    Real.exp (-(trivialHeight k) * (u / (n : ℝ)))
  have ht (n k : ℕ) : 0 ≤ term n k := by dsimp [term]; unfold trivialHeight; positivity
  have hs (n : ℕ) : Summable (term n) := by
    apply Summable.of_nonneg_of_le (ht _) _ (trivialRootMass_summable n)
    intro k
    have hk : 0 < trivialHeight k := by unfold trivialHeight; positivity
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hk.le) (div_nonneg hu (by positivity))))
  intro n m hnm
  apply (hs n).tsum_le_tsum _ (hs m)
  intro k
  by_cases hn : n = 0
  · simpa [term, hn] using ht m k
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have ht0 : 0 < trivialHeight k := by unfold trivialHeight; positivity
  dsimp only [term]
  apply mul_le_mul _ _ (Real.exp_nonneg _) (by positivity)
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_nonneg ht0.le
      (mul_nonneg ht0.le (sub_nonneg.mpr hnm'))]
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (div_le_div_of_nonneg_left hu hn0 hnm') (neg_nonpos.mpr ht0.le)

private theorem trivialRootResponse_upper {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    trivialRootResponse u n ≤ (1+Real.log n)/2 := by
  unfold trivialRootResponse
  apply (Real.tsum_le_of_sum_range_le (fun k => by unfold trivialHeight; positivity) _)
  intro N
  have hheight (k : ℕ) : 0 < trivialHeight k := by unfold trivialHeight; positivity
  have hpos (k : ℕ) : 0 ≤ (n : ℝ) / (trivialHeight k * ((n : ℝ)+trivialHeight k)) := by
    unfold trivialHeight
    positivity
  calc
    _ ≤ ∑ k ∈ Finset.range N, (n : ℝ) / (trivialHeight k * ((n : ℝ)+trivialHeight k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_of_le_one_right (hpos k) (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith [hheight k])
          (div_nonneg hu (by positivity))))
    _ ≤ _ := ((trivialRootMass_summable n).sum_le_tsum _ (fun k _ => hpos k)).trans (trivial_mode_bound n)


open MeasureTheory Set
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity (finite_error_integral normalized_error_integral)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (G_split_nonneg)

private theorem root_centered_response {n : ℕ} (hn : 2 ≤ n)
    {v : ℝ} (hv : 0 ≤ v) :
    centered (n : ℝ) (Real.exp ((n : ℝ) * v)) - rootDensity (n : ℝ) ((n : ℝ) * v) =
      Real.exp (-((n : ℝ)*v)/2) * (trivialRootResponse ((n : ℝ)*v) n - Real.log (2*Real.pi)) := by
  let r := (n : ℝ)
  have hr : 1 < r := by dsimp [r]; exact_mod_cast (show 1 < n by omega)
  let y := Real.exp v
  let x := Real.exp (r * v)
  let s := Real.exp ((1 - r / 2) * v)
  let w := Real.exp ((r - 1) * v)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : 1 ≤ x := (Real.exp_zero : Real.exp (0 : ℝ) = 1) ▸
    Real.exp_le_exp.mpr (mul_nonneg hr0.le hv)
  have hroot : x ^ r⁻¹ = y := by
    dsimp only [x, y]
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hscale₁ : Real.sqrt x * y ^ (1 - r) = s := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [x, y, s]
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hscale₂ : s * w = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [s, w, x]
    rw [← Real.exp_add, ← Real.exp_mul]
    congr 1
    ring
  have hcut := centered_root_tail (r := r) hr.le (zero_lt_one.trans_le hx1)
  dsimp only at hcut
  change centered r x = _ at hcut
  rw [hroot] at hcut
  have h := root_spectral_transform hr v
  dsimp only at h
  change r * s * (-(zeroTail (Real.log y)).re + (r - 1) * w *
      (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) = _ at h
  have he := (q_weighted_transport hr hv).1
  have hZ := (weighted_zero_tail hr v).1
  have hz : IntegrableOn (fun t => t ^ (-r) * (zeroTail (Real.log t)).re) (Ioi y) := by
    have hRe := hZ.re
    change IntegrableOn (fun t : ℝ => ((t ^ (-r)) • zeroTail (Real.log t)).re) (Ioi y) at hRe
    simpa only [Complex.real_smul, Complex.re_ofReal_mul] using hRe
  have hsplit : (∫ t in Ioi y, t ^ (-r) * Q t) =
      (∫ t in Ioi y, t ^ (-r) * qError t) -
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re) := by
    rw [← integral_sub (f := fun t => t ^ (-r) * qError t)
      (g := fun t => t ^ (-r) * (zeroTail (Real.log t)).re) he hz]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by unfold qError; ring)
  have hdiff : centered r x - rootDensity r (r * v) =
      r * s * (qError y - (r - 1) * w * (∫ t in Ioi y, t ^ (-r) * qError t)) := by
    rw [hcut, ← h, hsplit]
    change _ = r * s * (Q y + (zeroTail (Real.log y)).re - (r - 1) * w *
      (∫ t in Ioi y, t ^ (-r) * qError t))
    linear_combination r * Q y * hscale₁ + r * (r - 1) *
      ((∫ t in Ioi y, t ^ (-r) * qError t) -
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) * hscale₂
  have hscale : s = Real.exp (-(r * v) / 2) * Real.exp v := by
    dsimp only [s]
    rw [← Real.exp_add]
    congr 1
    ring
  change centered r x - rootDensity r (r * v) = _
  rw [hdiff, hscale, show r * (Real.exp (-(r * v) / 2) * Real.exp v) =
    Real.exp (-(r * v) / 2) * (r * Real.exp v) by ring, mul_assoc]
  rw [(q_weighted_transport hr hv).2]
  unfold trivialRootResponse
  rw [mul_div_cancel_left₀ _ hr0.ne']

private theorem trivial_response_split {m : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    (∑ n ∈ Finset.Icc 2 m, -(μ n : ℝ) *
      (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)) =
      -Real.exp (-u/2) * (∑ n ∈ Finset.Icc 2 m, (μ n : ℝ)*trivialRootResponse u n) +
        Real.exp (-u/2)*Real.log (2*Real.pi)*∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) := by
  let E := Real.exp (-u/2)
  let g := trivialRootResponse u
  let l := Real.log (2*Real.pi)
  have hcase (n : ℕ) (hn : n ∈ Finset.Icc 2 m) :
      centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u = E*(g n-l) := by
    have hn₂ := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h := root_centered_response hn₂ (v := u/(n : ℝ)) (div_nonneg hu hn0.le)
    rwa [mul_div_cancel₀ _ hn0.ne'] at h
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hcase n hn]
  ring

theorem trivial_response_signed_bound (hRH : RiemannHypothesis) :
    ∃ D : ℝ, 0 < D ∧ ∀ (m : ℕ) (u : ℝ), 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m, -(μ n : ℝ) *
        (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)| ≤
      D*(m : ℝ)*Real.exp (-u/2) := by
  obtain ⟨C, hC, hM⟩ := moebius_monotone_log_weight_bound hRH
  let l := Real.log (2*Real.pi)
  refine ⟨C + |l|, by positivity, fun m u hu => ?_⟩
  by_cases hm : 2 ≤ m
  · let E := Real.exp (-u/2)
    let g := trivialRootResponse u
    have hsum := trivial_response_split (m := m) hu
    have habs : |∑ n ∈ Finset.Icc 2 m, (μ n : ℝ)| ≤ m := by
      calc
        _ ≤ ∑ n ∈ Finset.Icc 2 m, |(μ n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.Icc 2 m, (1 : ℝ) := Finset.sum_le_sum fun n _ => by
          exact_mod_cast abs_moebius_le_one (n := n)
        _ ≤ _ := by simp [Nat.card_Icc, nsmul_eq_mul]
    have hE : 0 ≤ E := Real.exp_nonneg _
    have hG := hM m hm g (trivialRootResponse_nonneg _ _) (trivialRootResponse_monotone hu)
      (trivialRootResponse_upper hu _)
    rw [hsum]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hE]
    exact (add_le_add (mul_le_mul_of_nonneg_left hG hE)
      (mul_le_mul_of_nonneg_left habs (mul_nonneg hE (abs_nonneg _)))).trans_eq (by
      change _ = (C+|l|)*(m : ℝ)*E
      ring)
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hm), Finset.sum_empty, abs_zero]
    positivity

private theorem active_moebius_prefix_sublinear (hRH : RiemannHypothesis) :
    ∀ δ > (0 : ℝ), ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ n ≤ m+1,
      |∑ i ∈ Finset.range n, activeMoebius i| ≤ δ * (m : ℝ) / Real.log m := by
  intro δ hδ
  obtain ⟨J, hJ⟩ := moebius_uniform_prefix_log_sublinear_of_rh hRH (δ/2) (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_ge ((4/δ)^2)
  let M := max 2 (max J K)
  refine ⟨M, le_max_left _ _, fun m hm n hn => ?_⟩
  have hm₂ : 2 ≤ m := (le_max_left 2 _).trans hm
  have hm₂' : (2 : ℝ) ≤ m := by exact_mod_cast hm₂
  have hm0 : (0 : ℝ) < m := by linarith
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hJm : J ≤ m := (le_max_left _ K).trans ((le_max_right 2 _).trans hm)
  have hKm : K ≤ m := (le_max_right J _).trans ((le_max_right 2 _).trans hm)
  have hsmall : Real.log (m : ℝ) ≤ (δ/2) * m := by
    have hroot : 4/δ ≤ Real.sqrt (m : ℝ) := by
      have hx : (4/δ)^2 ≤ (m : ℝ) := hK.trans (by exact_mod_cast hKm)
      simpa only [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4/δ)] using Real.sqrt_le_sqrt hx
    have hcoef : 2 ≤ (δ/2)*Real.sqrt (m : ℝ) := by
      linarith only [(div_le_iff₀ hδ).mp hroot]
    have hl := Real.log_le_rpow_div hm0.le (show (0 : ℝ) < 1/2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hl
    refine hl.trans ?_
    have h := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (m : ℝ))
    calc
      _ = 2 * Real.sqrt (m : ℝ) := by ring
      _ ≤ _ := h.trans_eq (by rw [mul_assoc, ← pow_two, Real.sq_sqrt hm0.le])
  apply (le_div_iff₀ hmlog).mpr
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero, zero_mul]
    positivity
  | succ k =>
    have hk : k ≤ m := by omega
    by_cases hk₂ : 2 ≤ k
    · have hI : insert 1 (Finset.Icc 2 k) = Finset.Ioc 0 k := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      have hs := active_moebius_range k (fun _ => 1)
      simp only [mul_one] at hs
      have he : (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ)) =
          1 + ∑ i ∈ Finset.Icc 2 k, (μ i : ℝ) := by
        rw [← hI, Finset.sum_insert (by simp)]
        simp
      rw [hs, show (∑ i ∈ Finset.Icc 2 k, (μ i : ℝ)) =
        (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ))-1 by linarith only [he]]
      calc
        _ ≤ (|∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ)| + 1) * Real.log (m : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hmlog.le
          simpa only [abs_one] using abs_sub (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ)) 1
        _ ≤ δ * (m : ℝ) := by rw [add_mul, one_mul]; linarith only [hJ m hJm k hk, hsmall]
    · have hzero : ∀ i ∈ Finset.range (k+1), activeMoebius i = 0 := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact ite_eq_right (by omega)
      rw [Finset.sum_eq_zero hzero, abs_zero, zero_mul]
      positivity

/-- For large truncation orders, the signed trivial-root response is uniformly sublinear. -/
theorem trivial_response_signed_sublinear (hRH : RiemannHypothesis) :
    ∀ ε > (0 : ℝ), ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m, -(μ n : ℝ) *
        (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)| ≤
      ε * (m : ℝ) * Real.exp (-u/2) := by
  intro ε hε
  let l := Real.log (2*Real.pi)
  let d := Real.log 2
  let C := 1 + (1 + |l|) / d
  have hd : 0 < d := Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (by positivity) hd.le)
  let δ := ε / C
  have hδ : 0 < δ := div_pos hε hC
  obtain ⟨M, hM₂, hM⟩ := active_moebius_prefix_sublinear hRH δ hδ
  refine ⟨M, hM₂, fun m hm u hu => ?_⟩
  let E := Real.exp (-u/2)
  let g := trivialRootResponse u
  let B := δ * (m : ℝ) / Real.log m
  have hm₂ := hM₂.trans hm
  have hm₂' : (2 : ℝ) ≤ m := by exact_mod_cast hm₂
  have hdlog : d ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hm₂'
  have hlog : 0 < Real.log (m : ℝ) := hd.trans_le hdlog
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hδ.le (Nat.cast_nonneg m)) hlog.le
  have hpref := hM m hm
  have hG : |∑ n ∈ Finset.Icc 2 m, (μ n : ℝ)*g n| ≤ 2*B*g m := by
    rw [← active_moebius_range]
    exact monotone_finite_abel_bound hB (trivialRootResponse_nonneg _ _)
      (trivialRootResponse_monotone hu) hpref
  have hμ : |∑ n ∈ Finset.Icc 2 m, (μ n : ℝ)| ≤ B := by
    have hsum := active_moebius_range m (fun _ => 1)
    simp only [mul_one] at hsum
    rw [← hsum]
    exact hpref (m+1) le_rfl
  have hsum := trivial_response_split (m := m) hu
  rw [hsum]
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hcoef : 2 * B * g m + |l| * B ≤ ε * (m : ℝ) := by
    have hg := trivialRootResponse_upper hu m
    have hratio := one_div_le_one_div_of_le hd hdlog
    have hmain : 1 + (1 + |l|)/Real.log (m : ℝ) ≤ C := by
      dsimp only [C]
      simp_rw [div_eq_mul_inv, one_mul] at hratio ⊢
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hratio (by positivity))
    calc
      _ ≤ B*(1+Real.log (m : ℝ)+|l|) := by
        change g m ≤ (1+Real.log (m : ℝ))/2 at hg
        nlinarith only [mul_le_mul_of_nonneg_left hg hB]
      _ = (δ*(m : ℝ)) * (1 + (1+|l|)/Real.log (m : ℝ)) := by
        dsimp only [B]
        field_simp
        ring
      _ ≤ (δ*(m : ℝ)) * C := mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = ε*(m : ℝ) := by dsimp only [δ]; field_simp
  refine (abs_add_le _ _).trans ?_
  change |-E * (∑ n ∈ Finset.Icc 2 m, (μ n : ℝ)*g n)| +
    |E*l*(∑ n ∈ Finset.Icc 2 m, (μ n : ℝ))| ≤ _
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hE]
  exact (add_le_add (mul_le_mul_of_nonneg_left hG hE)
    (mul_le_mul_of_nonneg_left hμ (mul_nonneg hE (abs_nonneg _)))).trans
    (by nlinarith only [mul_le_mul_of_nonneg_left hcoef hE])

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
