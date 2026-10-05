/- GID: D5/S3/Arith/FibonacciAtomic/WeightedInghamRate
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/WeightedInghamRate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Weighted Fibonacci fractional-part sums converge at a half-exponential rate. -/

import D5.S3.Axis.AxisConvergence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.WeightedInghamRate

noncomputable def weightedSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (Nat.fib (k + 1) : ℝ) * Int.fract ((Nat.fib n : ℝ) / Nat.fib (k + 1))

noncomputable def inghamKernel (x : ℝ) : ℝ := x * (⌊1 / x⌋ : ℝ)

local notation "F" => (fun z : ℤ => (Int.fib z : ℝ))
local notation "φ" => Real.goldenRatio

/-- Both Fibonacci row sums have the same half-exponential error bound. -/
theorem result : ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    |weightedSum n / Nat.fib n - 2 / Real.sqrt 5| ≤ C * φ ^ (-(n : ℝ) / 2) ∧
    |(∑ k ∈ Finset.range n, inghamKernel ((Nat.fib (k + 1) : ℝ) / Nat.fib n)) -
      ((n : ℝ) - 2 / Real.sqrt 5)| ≤ C * φ ^ (-(n : ℝ) / 2) := by
  have mainTerm (n j : ℕ) (hj : 1 ≤ j) (hn : 2 * j + 3 ≤ n) :
      (Nat.fib (n - j) : ℝ) * Int.fract ((Nat.fib n : ℝ) / Nat.fib (n - j)) =
        if Even j then (Nat.fib (n - j) : ℝ) - Nat.fib (n - 2 * j)
        else (Nat.fib (n - 2 * j) : ℝ) := by
    have addition (a : ℤ) (j : ℕ) :
        Int.fib (a + j) + (-1 : ℤ) ^ j * Int.fib (a - j) =
          (Int.fib ((j : ℤ) - 1) + Int.fib ((j : ℤ) + 1)) * Int.fib a := by
      have hp := Int.fib_add (j : ℤ) a
      have hm := Int.fib_add (-(j : ℤ)) a
      rw [show -(j : ℤ) - 1 = -((j + 1 : ℕ) : ℤ) by omega,
        Int.fib_neg_natCast, Int.fib_neg_natCast] at hm
      rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega, Int.fib_natCast]
      simp only [pow_add, pow_one, Int.fib_natCast] at hp hm
      rw [add_comm] at hp
      rw [show -(j : ℤ) + a = a - j by ring] at hm
      rcases Nat.even_or_odd j with he | ho
      · rw [he.neg_one_pow] at hm ⊢
        rw [hp, hm]
        ring
      · rw [ho.neg_one_pow] at hm ⊢
        rw [hp, hm]
        ring
    have heq := addition ((n : ℤ) - j) j
    rw [sub_add_cancel,
      show (n : ℤ) - j - j = ((n - 2 * j : ℕ) : ℤ) by omega,
      show (n : ℤ) - j = ((n - j : ℕ) : ℤ) by omega] at heq
    simp only [Int.fib_natCast] at heq
    let L : ℤ := Int.fib ((j : ℤ) - 1) + Int.fib ((j : ℤ) + 1)
    have eqR : (Nat.fib n : ℝ) + (-1 : ℝ) ^ j * Nat.fib (n - 2 * j) =
        (L : ℝ) * Nat.fib (n - j) := by
      dsimp only [L]
      exact_mod_cast heq
    have hb : 0 < (Nat.fib (n - j) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < n - j)
    have hr : 0 < (Nat.fib (n - 2 * j) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < n - 2 * j)
    have hrb : (Nat.fib (n - 2 * j) : ℝ) < Nat.fib (n - j) := by
      exact_mod_cast (Nat.fib_lt_fib (by omega : 2 ≤ n - 2 * j)).mpr (by omega)
    by_cases he : Even j
    · rw [if_pos he, he.neg_one_pow] at *
      have hf : Int.fract ((Nat.fib n : ℝ) / Nat.fib (n - j)) =
          1 - (Nat.fib (n - 2 * j) : ℝ) / Nat.fib (n - j) := by
        apply Int.fract_eq_iff.mpr
        refine ⟨?_, ?_, L - 1, ?_⟩
        · have h := (div_lt_one hb).mpr hrb
          linarith
        · have h := div_pos hr hb
          linarith
        · push_cast
          field_simp [hb.ne']
          nlinarith
      rw [hf]
      field_simp
    · rw [if_neg he]
      have ho := Nat.not_even_iff_odd.mp he
      rw [ho.neg_one_pow] at eqR
      have hf : Int.fract ((Nat.fib n : ℝ) / Nat.fib (n - j)) =
          (Nat.fib (n - 2 * j) : ℝ) / Nat.fib (n - j) := by
        apply Int.fract_eq_iff.mpr
        refine ⟨(div_pos hr hb).le, (div_lt_one hb).mpr hrb, L, ?_⟩
        field_simp
        nlinarith
      rw [hf]
      field_simp
  have pairedSum (n : ℤ) (m : ℕ) :
      5 * (∑ t ∈ Finset.range m, (F (n - 2 * t - 2) + F (n - 4 * t - 3))) =
        4 * F (n + 1) - 2 * F n - 5 * F (n - 2 * m - 1) -
          3 * F (n - 4 * m + 2) + 4 * F (n - 4 * m + 1) := by
    have fibRecurrence (t : ℤ) : F (t + 2) = F t + F (t + 1) := by
      change (Int.fib (t + 2) : ℝ) = (Int.fib t : ℝ) + Int.fib (t + 1)
      exact_mod_cast Int.fib_add_two t
    have step (t : ℤ) : F t = F (t - 2) + F (t - 1) := by
      simpa only [show t - 2 + 2 = t by omega,
        show t - 2 + 1 = t - 1 by omega] using fibRecurrence (t - 2)
    have gstep (t : ℤ) :
        3 * F (t + 2) - 4 * F (t + 1) -
          (3 * F (t - 2) - 4 * F (t - 3)) = 5 * F (t - 3) := by
      have h1 := fibRecurrence (t - 3)
      have h2 := fibRecurrence (t - 2)
      have h3 := fibRecurrence (t - 1)
      have h4 := fibRecurrence t
      have e1 : t - 3 + 2 = t - 1 := by omega
      have e2 : t - 3 + 1 = t - 2 := by omega
      have e3 : t - 2 + 2 = t := by omega
      have e4 : t - 2 + 1 = t - 1 := by omega
      have e5 : t - 1 + 2 = t + 1 := by omega
      have e6 : t - 1 + 1 = t := by omega
      rw [e1, e2] at h1
      rw [e3, e4] at h2
      rw [e5, e6] at h3
      linarith
    induction m with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Nat.cast_zero, sub_zero]
      have h1 := fibRecurrence (n - 1)
      have h2 := fibRecurrence n
      rw [show n - 1 + 2 = n + 1 by omega, show n - 1 + 1 = n by omega] at h1
      linarith
    | succ m ih =>
      rw [Finset.sum_range_succ]
      push_cast
      have hs := step (n - 2 * m - 1)
      have hg := gstep (n - 4 * m)
      have e1 : n - 2 * m - 1 - 2 = n - 2 * (m + 1) - 1 := by omega
      have e2 : n - 2 * m - 1 - 1 = n - 2 * m - 2 := by omega
      have e3 : n - 4 * m - 2 = n - 4 * (m + 1) + 2 := by omega
      have e4 : n - 4 * m - 3 = n - 4 * (m + 1) + 1 := by omega
      rw [← e1, ← e3, ← e4]
      rw [e2] at hs
      dsimp only at ih hs hg ⊢
      linarith
  have fibUpper (t : ℕ) : (Nat.fib t : ℝ) ≤ φ ^ (t + 1) := by
    have h := Real.goldenRatio_mul_fib_succ_add_fib t
    nlinarith [Real.goldenRatio_pos, Nat.cast_nonneg (α := ℝ) (Nat.fib (t + 1))]
  refine ⟨4096, by norm_num, 16, ?_⟩
  intro n hn
  let m := (n - 4) / 4
  have hm : 4 * m + 4 ≤ n ∧ n ≤ 4 * m + 7 := by
    dsimp [m]
    omega
  have hm1 : 1 ≤ m := by dsimp [m]; omega
  have hfn : 0 < (Nat.fib n : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < n)
  let R : ℕ → ℝ := fun j =>
    (Nat.fib (n - j) : ℝ) * Int.fract ((Nat.fib n : ℝ) / Nat.fib (n - j))
  have row : weightedSum n = ∑ j ∈ Finset.range n, R j := by
    unfold weightedSum
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    dsimp [R]
    rw [show n - 1 - j + 1 = n - j by omega]
  have rzero : R 0 = 0 := by
    dsimp [R]
    rw [div_self hfn.ne', Int.fract_one, mul_zero]
  have main : (∑ j ∈ Finset.range (2 * m + 1), R j) =
      ∑ t ∈ Finset.range m,
        ((Nat.fib (n - 2 * t - 2) : ℝ) + Nat.fib (n - 4 * t - 3)) := by
    have inductionStep : ∀ a : ℕ, a ≤ m →
        (∑ j ∈ Finset.range (2 * a + 1), R j) =
          ∑ t ∈ Finset.range a,
            ((Nat.fib (n - 2 * t - 2) : ℝ) + Nat.fib (n - 4 * t - 3)) := by
      intro a
      induction a with
      | zero => intro _; simpa using rzero
      | succ a ih =>
        intro ha
        have hodd := mainTerm n (2 * a + 1) (by omega) (by omega)
        have heven := mainTerm n (2 * a + 2) (by omega) (by omega)
        rw [if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one a))] at hodd
        rw [if_pos (by exact ⟨a + 1, by omega⟩ : Even (2 * a + 2))] at heven
        change R (2 * a + 1) = _ at hodd
        change R (2 * a + 2) = _ at heven
        have hf := Nat.fib_add_two (n := n - 4 * a - 4)
        rw [show n - 4 * a - 4 + 2 = n - 4 * a - 2 by omega,
          show n - 4 * a - 4 + 1 = n - 4 * a - 3 by omega] at hf
        have hfR : (Nat.fib (n - 4 * a - 2) : ℝ) =
            Nat.fib (n - 4 * a - 4) + (Nat.fib (n - 4 * a - 3) : ℝ) := by
          exact_mod_cast hf
        rw [show 2 * (a + 1) + 1 = (2 * a + 1) + 1 + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, ih (by omega),
          Finset.sum_range_succ, hodd,
          show 2 * a + 1 + 1 = 2 * a + 2 by omega, heven]
        rw [show n - 2 * (2 * a + 1) = n - 4 * a - 2 by omega,
          show n - (2 * a + 2) = n - 2 * a - 2 by omega,
          show n - 2 * (2 * a + 2) = n - 4 * a - 4 by omega]
        linarith
    exact inductionStep m le_rfl
  let L := n - (2 * m + 1)
  let T : ℝ := ∑ i ∈ Finset.range L, R (2 * m + 1 + i)
  have splitRow : weightedSum n =
      (∑ j ∈ Finset.range (2 * m + 1), R j) + T := by
    rw [row, show n = (2 * m + 1) + L by dsimp [L]; omega,
      Finset.sum_range_add]
  have tailNonneg : 0 ≤ T := by
    apply Finset.sum_nonneg
    intro i _
    dsimp [R]
    positivity
  have tailUpper : T ≤ (Nat.fib (L + 2) : ℝ) := by
    calc
      T ≤ ∑ i ∈ Finset.range L, (Nat.fib (n - (2 * m + 1 + i)) : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [R]
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) (Int.fract_lt_one _).le
      _ = ∑ i ∈ Finset.range L, (Nat.fib (i + 1) : ℝ) := by
        rw [← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl
        intro i hi
        have hiL := Finset.mem_range.mp hi
        congr 2
        dsimp [L] at *
        omega
      _ ≤ (Nat.fib (L + 2) : ℝ) := by
        have h := Nat.fib_succ_eq_succ_sum (L + 1)
        rw [Finset.sum_range_succ'] at h
        simp only [Nat.fib_zero, add_zero] at h
        have hR : (Nat.fib (L + 2) : ℝ) =
            (∑ i ∈ Finset.range L, (Nat.fib (i + 1) : ℝ)) + 1 := by
          exact_mod_cast h
        linarith
  have finiteIdentity :
      5 * weightedSum n - (4 * (Nat.fib (n + 1) : ℝ) - 2 * Nat.fib n) =
        5 * T - 5 * (Nat.fib (n - 2 * m - 1) : ℝ) -
          3 * (Nat.fib (n - 4 * m + 2) : ℝ) + 4 * Nat.fib (n - 4 * m + 1) := by
    have hs := pairedSum (n : ℤ) m
    have hcast (a b : ℕ) (hab : b ≤ a) :
        F ((a : ℤ) - b) = (Nat.fib (a - b) : ℝ) := by
      rw [← Nat.cast_sub hab]
      simp only [Int.fib_natCast, Int.cast_natCast]
    have hsum : (∑ t ∈ Finset.range m, (F ((n : ℤ) - 2 * t - 2) +
        F ((n : ℤ) - 4 * t - 3))) =
        ∑ t ∈ Finset.range m,
          ((Nat.fib (n - 2 * t - 2) : ℝ) + Nat.fib (n - 4 * t - 3)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_range.mp ht
      rw [show (n : ℤ) - 2 * t - 2 = (n : ℤ) - (2 * t + 2 : ℕ) by push_cast; ring,
        show (n : ℤ) - 4 * t - 3 = (n : ℤ) - (4 * t + 3 : ℕ) by push_cast; ring,
        hcast n (2 * t + 2) (by omega), hcast n (4 * t + 3) (by omega)]
      simp only [Nat.sub_add_eq]
    rw [hsum] at hs
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega,
      show (n : ℤ) - 2 * m - 1 = (n : ℤ) - (2 * m + 1 : ℕ) by push_cast; ring,
      show (n : ℤ) - 4 * m + 2 = ((n + 2 : ℕ) : ℤ) - (4 * m : ℕ) by push_cast; ring,
      show (n : ℤ) - 4 * m + 1 = ((n + 1 : ℕ) : ℤ) - (4 * m : ℕ) by push_cast; ring,
      hcast n (2 * m + 1) (by omega),
      hcast (n + 2) (4 * m) (by omega), hcast (n + 1) (4 * m) (by omega)] at hs
    simp only [Int.fib_natCast, Int.cast_natCast, Nat.sub_add_eq] at hs
    rw [show n + 2 - 4 * m = n - 4 * m + 2 by omega,
      show n + 1 - 4 * m = n - 4 * m + 1 by omega] at hs
    rw [splitRow, main]
    linarith
  have hφ : 0 < φ := Real.goldenRatio_pos
  have hφ1 : 1 ≤ φ := Real.one_lt_goldenRatio.le
  let B : ℝ := φ ^ (n - 2 * m + 2)
  have hB : 1 ≤ B := one_le_pow₀ hφ1
  have bounded (i : ℕ) (hi : i ≤ n - 2 * m + 1) : (Nat.fib i : ℝ) ≤ B := by
    exact (fibUpper i).trans (pow_le_pow_right₀ hφ1 (by omega))
  have tBound : T ≤ B := by
    exact tailUpper.trans (bounded (L + 2) (by dsimp [L]; omega))
  have f1 := bounded (n - 2 * m - 1) (by omega)
  have f2 := bounded (n - 4 * m + 2) (by omega)
  have f3 := bounded (n - 4 * m + 1) (by omega)
  have f10 : 0 ≤ (Nat.fib (n - 2 * m - 1) : ℝ) := Nat.cast_nonneg _
  have f20 : 0 ≤ (Nat.fib (n - 4 * m + 2) : ℝ) := Nat.cast_nonneg _
  have f30 : 0 ≤ (Nat.fib (n - 4 * m + 1) : ℝ) := Nat.cast_nonneg _
  have truncBound : |weightedSum n -
      (4 * (Nat.fib (n + 1) : ℝ) - 2 * Nat.fib n) / 5| ≤ 4 * B := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have constantIdentity : 2 / Real.sqrt 5 = (4 * φ - 2) / 5 := by
    have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
    have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    rw [Real.goldenRatio]
    field_simp
    nlinarith
  have conjBound : |Real.goldenConj ^ n| ≤ 1 := by
    rw [abs_pow]
    apply pow_le_one₀ (abs_nonneg _)
    rw [abs_of_neg Real.goldenConj_neg]
    linarith [Real.neg_one_lt_goldenConj]
  have residualBound : |(4 * (Nat.fib (n + 1) : ℝ) - 2 * Nat.fib n) / 5 -
      (2 / Real.sqrt 5) * Nat.fib n| ≤ 1 := by
    have heq : (4 * (Nat.fib (n + 1) : ℝ) - 2 * Nat.fib n) / 5 -
        (2 / Real.sqrt 5) * Nat.fib n =
        (4 / 5 : ℝ) * ((Nat.fib (n + 1) : ℝ) - φ * Nat.fib n) := by
      rw [constantIdentity]
      ring
    rw [heq, Real.fib_succ_sub_goldenRatio_mul_fib, abs_mul]
    norm_num
    rw [abs_pow] at conjBound
    nlinarith
  have rawBound : |weightedSum n - (2 / Real.sqrt 5) * Nat.fib n| ≤ 5 * B := by
    have ht := abs_sub_le (weightedSum n)
      ((4 * (Nat.fib (n + 1) : ℝ) - 2 * Nat.fib n) / 5)
      ((2 / Real.sqrt 5) * Nat.fib n)
    linarith
  have fibLower : φ ^ (n - 2) ≤ (Nat.fib n : ℝ) := by
    have h := D5.S3.Axis.AxisConvergence.goldenRatio_pow_div_le_fib_succ (n - 1)
    rw [show n - 1 + 1 = n by omega] at h
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ, mul_div_cancel_right₀ _ hφ.ne'] at h
    exact h
  have rateBound : |weightedSum n / Nat.fib n - 2 / Real.sqrt 5| ≤
      4096 * φ ^ (-(n : ℝ) / 2) := by
    have heq : weightedSum n / Nat.fib n - 2 / Real.sqrt 5 =
        (weightedSum n - (2 / Real.sqrt 5) * Nat.fib n) / Nat.fib n := by
      field_simp
    rw [heq, abs_div, abs_of_pos hfn]
    calc
      |weightedSum n - (2 / Real.sqrt 5) * Nat.fib n| / Nat.fib n ≤
          5 * B / Nat.fib n := div_le_div_of_nonneg_right rawBound hfn.le
      _ ≤ 5 * B / φ ^ (n - 2) :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hφ _) fibLower
      _ = 5 * φ ^ ((n - 2 * m + 2 : ℕ) - (n - 2 : ℕ) : ℝ) := by
        dsimp [B]
        rw [← Real.rpow_natCast φ (n - 2 * m + 2),
          ← Real.rpow_natCast φ (n - 2), mul_div_assoc,
          ← Real.rpow_sub hφ]
      _ ≤ 5 * φ ^ (8 - (n : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.rpow_le_rpow_of_exponent_le hφ1
        have h1 : ((n - 2 * m + 2 : ℕ) : ℝ) = (n : ℝ) - 2 * m + 2 := by
          rw [Nat.cast_add, Nat.cast_sub (by omega)]
          push_cast
          ring
        have h2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        rw [h1, h2]
        have hnm : (n : ℝ) ≤ 4 * m + 7 := by exact_mod_cast hm.2
        linarith
      _ = (5 * φ ^ 8) * φ ^ (-(n : ℝ) / 2) := by
        rw [sub_eq_add_neg, Real.rpow_add hφ]
        norm_num only [Real.rpow_ofNat]
        ring
      _ ≤ 4096 * φ ^ (-(n : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos hφ _).le
        have hp : φ ^ 8 ≤ (2 : ℝ) ^ 8 := pow_le_pow_left₀ hφ.le Real.goldenRatio_lt_two.le 8
        norm_num at hp
        linarith
  refine ⟨rateBound, ?_⟩
  have rowKernel : (∑ k ∈ Finset.range n,
      inghamKernel ((Nat.fib (k + 1) : ℝ) / Nat.fib n)) =
      (n : ℝ) - weightedSum n / Nat.fib n := by
    have term (k : ℕ) : inghamKernel ((Nat.fib (k + 1) : ℝ) / Nat.fib n) =
        1 - ((Nat.fib (k + 1) : ℝ) * Int.fract ((Nat.fib n : ℝ) / Nat.fib (k + 1))) /
          Nat.fib n := by
      have hk : 0 < (Nat.fib (k + 1) : ℝ) := by
        exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < k + 1)
      unfold inghamKernel
      rw [one_div_div, Int.fract]
      field_simp
      ring
    simp_rw [term]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, weightedSum]
  rw [rowKernel]
  convert rateBound using 1
  rw [show (n : ℝ) - weightedSum n / Nat.fib n - ((n : ℝ) - 2 / Real.sqrt 5) =
    -(weightedSum n / Nat.fib n - 2 / Real.sqrt 5) by ring, abs_neg]

end D5.S3.Arith.FibonacciAtomic.WeightedInghamRate
