/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/MoebiusPrefixes
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/MoebiusPrefixes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform logarithmic bounds for signed Möbius prefixes under RH. -/

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

theorem abs_sum_mul_antitone_Ioc_le {a w : ℕ → ℝ} {B : ℝ} {m N : ℕ}
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

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
