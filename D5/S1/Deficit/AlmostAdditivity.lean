/- GID: D5/S1/Deficit/AlmostAdditivity
   generality: I
   mirror-B: D5/B/S1/Deficit/AlmostAdditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The contraction reading is almost additive over prime exponents. -/

import D5.S1.Deficit.DeficitThreeValued
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace D5.S1.Deficit.AlmostAdditivity

open scoped BigOperators
open D5.S1.Deficit

/-- The product of the distinct prime factors of a natural number. -/
def primeRadical (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

/-- The contraction-face reading, assembled independently over prime exponents. -/
noncomputable def lambdaMinus (n : ℕ) : ℝ :=
  n.factorization.sum fun p exponent ↦ betaContraction exponent * Real.log p

private theorem betaContraction_zero : betaContraction 0 = 0 := by
  simp [betaContraction, betaGolden, betaDigits,
    D5.S1.Digit.Z, D5.S1.Digit.toRaw,
    D5.S0.Conventions.wEncoding, Nat.zeckendorfEquiv,
    D5.S1.Digit.rawOfZeckendorf]

private noncomputable def axisDefect (a b : ℕ) : ℝ :=
  betaContraction (a + b) - betaContraction a - betaContraction b

private theorem axisDefect_eq_neg_deficit (a b : ℕ) :
    axisDefect a b = -deficit a b := by
  rw [(deficit_integer a b).1, deficitContraction]
  simp only [axisDefect]
  ring

private theorem abs_axisDefect_le_one (a b : ℕ) : |axisDefect a b| ≤ 1 := by
  rcases deficit_three_valued a b with h | h | h
  · rw [axisDefect_eq_neg_deficit, h]
    norm_num
  · rw [axisDefect_eq_neg_deficit, h]
    norm_num
  · rw [axisDefect_eq_neg_deficit, h]
    norm_num

private theorem local_defect_mul_log (a b p : ℕ) :
    (betaContraction (a + b) * Real.log p - betaContraction a * Real.log p) -
        betaContraction b * Real.log p = axisDefect a b * Real.log p := by
  simp only [axisDefect]
  ring

@[simp] private theorem axisDefect_zero_left (b : ℕ) : axisDefect 0 b = 0 := by
  simp [axisDefect, betaContraction_zero]

@[simp] private theorem axisDefect_zero_right (a : ℕ) : axisDefect a 0 = 0 := by
  simp [axisDefect, betaContraction_zero]

private theorem lambdaMinus_mul_sub (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    lambdaMinus (m * n) - lambdaMinus m - lambdaMinus n =
      ∑ p ∈ m.factorization.support ∩ n.factorization.support,
        axisDefect (m.factorization p) (n.factorization p) * Real.log p := by
  classical
  rw [lambdaMinus, lambdaMinus, lambdaMinus, Nat.factorization_mul hm hn]
  change
    (∑ p ∈ (m.factorization + n.factorization).support,
      betaContraction ((m.factorization + n.factorization) p) * Real.log p) -
        (∑ p ∈ m.factorization.support,
          betaContraction (m.factorization p) * Real.log p) -
        (∑ p ∈ n.factorization.support,
          betaContraction (n.factorization p) * Real.log p) = _
  rw [Finsupp.support_add_eq_union]
  simp only [Finsupp.add_apply]
  let supportUnion := m.factorization.support ∪ n.factorization.support
  have hm_extend :
      (∑ p ∈ m.factorization.support,
          betaContraction (m.factorization p) * Real.log p) =
        ∑ p ∈ supportUnion, betaContraction (m.factorization p) * Real.log p := by
    apply Finset.sum_subset Finset.subset_union_left
    intro p hp hpm
    rw [Finsupp.notMem_support_iff.mp hpm, betaContraction_zero, zero_mul]
  have hn_extend :
      (∑ p ∈ n.factorization.support,
          betaContraction (n.factorization p) * Real.log p) =
        ∑ p ∈ supportUnion, betaContraction (n.factorization p) * Real.log p := by
    apply Finset.sum_subset Finset.subset_union_right
    intro p hp hpn
    rw [Finsupp.notMem_support_iff.mp hpn, betaContraction_zero, zero_mul]
  rw [hm_extend, hn_extend]
  change
    (∑ p ∈ supportUnion,
      betaContraction (m.factorization p + n.factorization p) * Real.log p) -
        (∑ p ∈ supportUnion, betaContraction (m.factorization p) * Real.log p) -
        (∑ p ∈ supportUnion, betaContraction (n.factorization p) * Real.log p) = _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  simp_rw [local_defect_mul_log]
  symm
  apply Finset.sum_subset Finset.inter_subset_union
  intro p hp hpi
  rcases Finset.mem_union.mp hp with hpm | hpn
  · have hpn' : p ∉ n.factorization.support := by
      intro h
      exact hpi (Finset.mem_inter.mpr ⟨hpm, h⟩)
    rw [Finsupp.notMem_support_iff.mp hpn', axisDefect_zero_right, zero_mul]
  · have hpm' : p ∉ m.factorization.support := by
      intro h
      exact hpi (Finset.mem_inter.mpr ⟨h, hpn⟩)
    rw [Finsupp.notMem_support_iff.mp hpm', axisDefect_zero_left, zero_mul]

/-- For positive inputs, the failure of additivity of the contraction reading is
bounded by the logarithm of the product of their common prime factors. -/
theorem lambdaMinus_almost_additive {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    |lambdaMinus (m * n) - lambdaMinus m - lambdaMinus n| ≤
      Real.log (primeRadical (Nat.gcd m n)) := by
  classical
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [lambdaMinus_mul_sub m n hm0 hn0]
  calc
    |∑ p ∈ m.factorization.support ∩ n.factorization.support,
        axisDefect (m.factorization p) (n.factorization p) * Real.log p| ≤
        ∑ p ∈ m.factorization.support ∩ n.factorization.support,
          |axisDefect (m.factorization p) (n.factorization p) * Real.log p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ m.factorization.support ∩ n.factorization.support, Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : Nat.Prime p := by
        apply Nat.prime_of_mem_primeFactors
        exact Finset.mem_inter.mp hp |>.1
      have hlog : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
      rw [abs_mul, abs_of_nonneg hlog]
      exact mul_le_of_le_one_left hlog (abs_axisDefect_le_one _ _)
    _ = Real.log (primeRadical (Nat.gcd m n)) := by
      rw [primeRadical, Nat.primeFactors_gcd hm0 hn0]
      push_cast
      rw [Real.log_prod]
      · simp only [Nat.support_factorization]
      · intro p hp
        exact_mod_cast
          (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1).ne_zero

end D5.S1.Deficit.AlmostAdditivity
