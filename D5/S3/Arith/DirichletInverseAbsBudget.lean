/- GID: D5/S3/Arith/DirichletInverseAbsBudget
   generality: G
   mirror-B: D5/B/S3/Arith/DirichletInverseAbsBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: A dominant absolute head bounds every Dirichlet inverse in absolute sum. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S3.Arith.DirichletInverseAbsBudget

open scoped BigOperators

/-- A real Dirichlet inverse is absolutely summable when the absolute head
strictly dominates every finite absolute tail. The head may be negative.
This is the classical ℓ¹ convolution inversion estimate, proved here by
finite absorption before invoking the nonnegative-series summability APIs. -/
theorem dirichletInverse_absolute_budget
    (b g : ArithmeticFunction ℝ) (T : ℝ)
    (htail : ∀ N : ℕ, (∑ d ∈ Finset.Ioc 1 N, |b d|) ≤ T)
    (hgap : T < |b 1|) (hinverse : b * g = 1) :
    Summable (fun n : ℕ => |g n|) ∧
      (∑' n : ℕ, |g n|) ≤ 1 / (|b 1| - T) := by
  classical
  have hden : 0 < |b 1| - T := sub_pos.mpr hgap
  let r : ArithmeticFunction ℝ := b - b 1 • (1 : ArithmeticFunction ℝ)
  let B : ArithmeticFunction ℝ := ⟨fun n => |r n|, by simp⟩
  let G : ArithmeticFunction ℝ := ⟨fun n => |g n|, by simp⟩
  let S : ℕ → ℝ := fun N => ∑ n ∈ Finset.Ioc 0 N, |g n|
  have hr : r * g = 1 - b 1 • g := by
    dsimp [r]
    rw [sub_mul, hinverse, smul_mul_assoc, one_mul]
  have hcoeff (n : ℕ) : |b 1| * |g n| ≤ (1 : ArithmeticFunction ℝ) n + (B * G) n := by
    have heq : b 1 * g n = (1 : ArithmeticFunction ℝ) n - (r * g) n := by
      have h := congrArg (fun f : ArithmeticFunction ℝ => f n) hr
      change (r * g) n = (1 : ArithmeticFunction ℝ) n - b 1 * g n at h
      linarith
    have hconv : |(r * g) n| ≤ (B * G) n := by
      rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
      change |∑ p ∈ n.divisorsAntidiagonal, r p.1 * g p.2| ≤
        ∑ p ∈ n.divisorsAntidiagonal, |r p.1| * |g p.2|
      simpa only [abs_mul] using
        Finset.abs_sum_le_sum_abs (fun p : ℕ × ℕ => r p.1 * g p.2)
          n.divisorsAntidiagonal
    have hunit : |(1 : ArithmeticFunction ℝ) n| = (1 : ArithmeticFunction ℝ) n := by
      rw [ArithmeticFunction.one_apply]
      split <;> norm_num
    calc
      _ = |b 1 * g n| := (abs_mul _ _).symm
      _ = |(1 : ArithmeticFunction ℝ) n - (r * g) n| := by rw [heq]
      _ ≤ |(1 : ArithmeticFunction ℝ) n| + |(r * g) n| := abs_sub _ _
      _ ≤ (1 : ArithmeticFunction ℝ) n + (B * G) n := by
        rw [hunit]
        exact add_le_add_right hconv _
  have hSnonneg (N : ℕ) : 0 ≤ S N := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSmono {M N : ℕ} (hMN : M ≤ N) : S M ≤ S N := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
        (Finset.mem_Ioc.mp hn).2.trans hMN⟩
    · intro n _ _
      exact abs_nonneg _
  have hfinite (N : ℕ) : S N ≤ 1 / (|b 1| - T) := by
    by_cases hN : N = 0
    · simp [S, hN, hden.le]
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hBtail : (∑ d ∈ Finset.Ioc 0 N, B d) = ∑ d ∈ Finset.Ioc 1 N, |b d| := by
      have hsplit := Finset.sum_Ioc_consecutive (fun d => B d)
        (by omega : 0 ≤ (1 : ℕ)) (by omega : 1 ≤ N)
      have hB1 : B 1 = 0 := by
        change |b 1 - b 1 * (1 : ArithmeticFunction ℝ) 1| = 0
        simp
      have heq : (∑ d ∈ Finset.Ioc 1 N, B d) = ∑ d ∈ Finset.Ioc 1 N, |b d| := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd1 : d ≠ 1 := ne_of_gt (Finset.mem_Ioc.mp hd).1
        change |b d - b 1 * (1 : ArithmeticFunction ℝ) d| = |b d|
        simp [hd1]
      simpa [hB1, heq] using hsplit.symm
    have hconvsum : (∑ n ∈ Finset.Ioc 0 N, (B * G) n) ≤ T * S N := by
      calc
        _ = ∑ d ∈ Finset.Ioc 0 N, B d * S (N / d) := by
          rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
          rfl
        _ ≤ ∑ d ∈ Finset.Ioc 0 N, B d * S N := by
          apply Finset.sum_le_sum
          intro d _
          exact mul_le_mul_of_nonneg_left (hSmono (Nat.div_le_self N d)) (abs_nonneg _)
        _ = (∑ d ∈ Finset.Ioc 0 N, B d) * S N := (Finset.sum_mul ..).symm
        _ ≤ T * S N := by
          rw [hBtail]
          exact mul_le_mul_of_nonneg_right (htail N) (hSnonneg N)
    have hsum : |b 1| * S N ≤ 1 + T * S N := by
      calc
        _ = ∑ n ∈ Finset.Ioc 0 N, |b 1| * |g n| := Finset.mul_sum ..
        _ ≤ ∑ n ∈ Finset.Ioc 0 N, ((1 : ArithmeticFunction ℝ) n + (B * G) n) :=
          Finset.sum_le_sum fun n _ => hcoeff n
        _ = 1 + ∑ n ∈ Finset.Ioc 0 N, (B * G) n := by
          rw [Finset.sum_add_distrib]
          simp [ArithmeticFunction.one_apply, Finset.mem_Ioc, hN]
        _ ≤ 1 + T * S N := add_le_add_right hconvsum 1
    have habsorb : (|b 1| - T) * S N ≤ 1 := by nlinarith [hsum]
    exact (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using habsorb)
  have hrange (N : ℕ) : (∑ n ∈ Finset.range N, |g n|) ≤ 1 / (|b 1| - T) := by
    calc
      _ ≤ ∑ n ∈ insert 0 (Finset.Ioc 0 N), |g n| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          by_cases hn0 : n = 0
          · simp [hn0]
          · exact Finset.mem_insert_of_mem (Finset.mem_Ioc.mpr
              ⟨Nat.pos_of_ne_zero hn0, (Finset.mem_range.mp hn).le⟩)
        · intro n _ _
          exact abs_nonneg _
      _ = S N := by
        rw [Finset.sum_insert (by simp)]
        simp only [ArithmeticFunction.map_zero, abs_zero, zero_add]
        rfl
      _ ≤ 1 / (|b 1| - T) := hfinite N
  exact ⟨summable_of_sum_range_le (fun _ => abs_nonneg _) hrange,
    Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) hrange⟩

end D5.S3.Arith.DirichletInverseAbsBudget
