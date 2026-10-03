/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelBranches
   mirror-E: none(waiver:formal-motzkin-branches)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Inverse]
   utility: none
   digest: Coefficient recursion constructs the two formal branches of the orthogonal sequence. -/

import Mathlib.RingTheory.PowerSeries.Inverse
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelNegative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelBranches

open Polynomial Finset CiglerMotzkinHankelDefs CiglerMotzkinHankelOrthogonal
  CiglerMotzkinHankelNegative

/-- The formal root is constructed over any field with distinct reciprocal roots. -/
theorem formal_branches {K : Type*} [Field K] (φ : Base →+* K) (α : K)
    (α_ne : α ≠ 0) (separated : α - α⁻¹ ≠ 0) (parameter : φ tVar = α + α⁻¹) :
    ∃ z : PowerSeries K,
      PowerSeries.constantCoeff z = α ∧
      z + z⁻¹ = PowerSeries.C (φ tVar) - PowerSeries.X ∧
      PowerSeries.constantCoeff (z - z⁻¹) ≠ 0 ∧
      (∀ w : PowerSeries K, PowerSeries.constantCoeff w = α →
        w * w - (PowerSeries.C (φ tVar) - PowerSeries.X) * w + 1 = 0 → w = z) ∧
      let a := (PowerSeries.C (φ sVar) - PowerSeries.X - z⁻¹) * (z - z⁻¹)⁻¹
      let b := (z - PowerSeries.C (φ sVar) + PowerSeries.X) * (z - z⁻¹)⁻¹
      (∀ r : ℕ, (-1 : PowerSeries K) ^ r * (Polynomial.map φ (orthogonal r)) =
        a * z ^ r + b * (z⁻¹) ^ r) ∧
      (∀ r : ℕ, (-1 : PowerSeries K) ^ (r + 1) * (Polynomial.map φ (backward r)) =
        a * (z⁻¹) ^ (r + 1) + b * z ^ (r + 1)) := by
  classical
  let δ := α - α⁻¹
  let c : ℕ → K := Nat.strongRec fun n previous =>
    if hz : n = 0 then α else
      -δ⁻¹ * (previous (n - 1) (by omega) +
        ∑ i : Fin n, if hi : i.val = 0 then 0 else
          previous i.val i.isLt * previous (n - i.val) (by omega))
  have c_zero : c 0 = α := by
    dsimp only [c]
    rw [Nat.strongRec_eq]
    simp
  have c_step (n : ℕ) : c (n + 1) =
      -δ⁻¹ * (c n + ∑ i : Fin (n + 1),
        if i.val = 0 then 0 else c i.val * c (n + 1 - i.val)) := by
    conv_lhs => dsimp only [c]; rw [Nat.strongRec_eq]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      Nat.add_sub_cancel]
    rfl
  let z := PowerSeries.mk c
  have z_constant : PowerSeries.constantCoeff z = α := c_zero
  have convolution (n : ℕ) :
      PowerSeries.coeff (n + 1) (z * z) =
        2 * α * c (n + 1) +
          ∑ i : Fin (n + 1), if i.val = 0 then 0 else c i.val * c (n + 1 - i.val) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i z * PowerSeries.coeff j z) (n + 1)]
    simp only [z, PowerSeries.coeff_mk]
    rw [sum_range_succ]
    have interior :
        (∑ i ∈ range (n + 1), c i * c (n + 1 - i)) =
          α * c (n + 1) +
            ∑ i : Fin (n + 1), if i.val = 0 then 0 else c i.val * c (n + 1 - i.val) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun i => if i = 0 then 0 else c i * c (n + 1 - i)) (n + 1)]
      have remove_zero :
          (∑ i ∈ range (n + 1), if i = 0 then 0 else c i * c (n + 1 - i)) =
          (∑ i ∈ range (n + 1), c i * c (n + 1 - i)) - α * c (n + 1) := by
        rw [sum_range_succ', sum_range_succ']
        simp [c_zero]
      rw [remove_zero]
      ring
    rw [interior, Nat.sub_self, c_zero]
    ring
  have quadratic : z * z - (PowerSeries.C (φ tVar) - PowerSeries.X) * z + 1 = 0 := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
      simp only [map_add, map_sub, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_mul, z_constant, PowerSeries.constantCoeff_C,
        PowerSeries.constantCoeff_X, sub_zero, map_one, map_zero, parameter]
      field_simp
      ring
    | succ n =>
      simp only [map_add, map_sub, sub_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, if_false, add_zero, map_zero]
      rw [convolution]
      simp only [z, PowerSeries.coeff_mk]
      change 2 * α * c (n + 1) + _ - (φ tVar * c (n + 1) - c n) = 0
      calc
        _ = δ * c (n + 1) + (c n + ∑ i : Fin (n + 1),
            if i.val = 0 then 0 else c i.val * c (n + 1 - i.val)) := by
          rw [parameter]
          dsimp only [δ]
          ring
        _ = 0 := by
          rw [c_step, ← mul_assoc, mul_neg, mul_inv_cancel₀ separated]
          ring
  have z_inv : z * z⁻¹ = 1 := PowerSeries.mul_inv_cancel z (by rwa [z_constant])
  have root : z + z⁻¹ = PowerSeries.C (φ tVar) - PowerSeries.X := by
    have multiplied := congrArg (fun f : PowerSeries K => f * z⁻¹) quadratic
    simp only [zero_mul, add_mul, sub_mul, one_mul, mul_assoc, z_inv, mul_one] at multiplied
    exact sub_eq_zero.mp (by convert multiplied using 1; ring)
  have difference : PowerSeries.constantCoeff (z - z⁻¹) ≠ 0 := by
    simpa [z_constant] using separated
  refine ⟨z, z_constant, root, difference, ?_, ?_⟩
  · intro w w_constant w_quadratic
    have factorization : (w - z) * (w - z⁻¹) = 0 := by
      calc
        _ = w * w - (z + z⁻¹) * w + z * z⁻¹ := by ring
        _ = 0 := by rw [root, z_inv]; exact w_quadratic
    rcases mul_eq_zero.mp factorization with left | right
    · exact sub_eq_zero.mp left
    · have inverse_constant := congrArg PowerSeries.constantCoeff (sub_eq_zero.mp right)
      have equal_roots : α = α⁻¹ := by simpa [w_constant, z_constant] using inverse_constant
      exact False.elim (separated (sub_eq_zero.mpr equal_roots))
  · dsimp only
    let a := (PowerSeries.C (φ sVar) - PowerSeries.X - z⁻¹) * (z - z⁻¹)⁻¹
    let b := (z - PowerSeries.C (φ sVar) + PowerSeries.X) * (z - z⁻¹)⁻¹
    have difference_inv : (z - z⁻¹) * (z - z⁻¹)⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel _ difference
    have sum_branches : a + b = 1 := by
      calc
        _ = (z - z⁻¹) * (z - z⁻¹)⁻¹ := by dsimp only [a, b]; ring
        _ = 1 := difference_inv
    have first : a * z + b * z⁻¹ = PowerSeries.C (φ sVar) - PowerSeries.X := by
      calc
        _ = (PowerSeries.C (φ sVar) - PowerSeries.X) *
            ((z - z⁻¹) * (z - z⁻¹)⁻¹) := by dsimp only [a, b]; ring
        _ = _ := by rw [difference_inv, mul_one]
    have recurrence (r : ℕ) :
        a * z ^ (r + 2) + b * (z⁻¹) ^ (r + 2) =
          (PowerSeries.C (φ tVar) - PowerSeries.X) *
            (a * z ^ (r + 1) + b * (z⁻¹) ^ (r + 1)) -
              (a * z ^ r + b * (z⁻¹) ^ r) := by
      rw [← root]
      simp only [pow_succ]
      linear_combination -(a * z ^ r + b * (z⁻¹) ^ r) * z_inv
    have forward : ∀ r : ℕ,
        (-1 : PowerSeries K) ^ r * (Polynomial.map φ (orthogonal r)) =
          a * z ^ r + b * (z⁻¹) ^ r := by
      apply Nat.twoStepInduction
      · simpa [orthogonal] using sum_branches.symm
      · simp only [orthogonal, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.map_C, Polynomial.coe_sub, Polynomial.coe_X,
          Polynomial.coe_C, pow_one]
        rw [first]
        ring
      · intro r previous current
        rw [recurrence r]
        rw [← current, ← previous]
        simp only [orthogonal, Polynomial.map_sub, Polynomial.map_mul,
          Polynomial.map_X, Polynomial.map_C, Polynomial.coe_sub,
          Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C, pow_succ]
        ring
    have negative_first : a * z⁻¹ + b * z = PowerSeries.C (φ tVar - φ sVar) := by
      calc
        _ = (z + z⁻¹) * (a + b) - (a * z + b * z⁻¹) := by ring
        _ = _ := by rw [root, sum_branches, first]; simp only [mul_one, map_sub]; ring
    have reverse_recurrence (r : ℕ) :
        a * (z⁻¹) ^ (r + 2) + b * z ^ (r + 2) =
          (PowerSeries.C (φ tVar) - PowerSeries.X) *
            (a * (z⁻¹) ^ (r + 1) + b * z ^ (r + 1)) -
              (a * (z⁻¹) ^ r + b * z ^ r) := by
      rw [← root]
      simp only [pow_succ]
      linear_combination -(a * (z⁻¹) ^ r + b * z ^ r) * z_inv
    refine ⟨forward, ?_⟩
    apply Nat.twoStepInduction
    · simp only [backward, Polynomial.map_sub, Polynomial.map_C, map_sub,
        Polynomial.coe_sub, Polynomial.coe_C,
        Nat.zero_add, pow_one]
      rw [negative_first, map_sub]
      ring
    · rw [reverse_recurrence 0]
      simp only [Nat.zero_add, pow_zero, pow_one, mul_one]
      rw [sum_branches, negative_first]
      simp only [backward, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X, map_sub, Polynomial.map_one,
        Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C,
        Polynomial.coe_X, Polynomial.coe_one, pow_succ, pow_zero]
      ring
    · intro r previous current
      rw [show r + 2 + 1 = (r + 1) + 2 by omega, reverse_recurrence (r + 1),
        ← current, ← previous]
      simp only [backward, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, Polynomial.coe_sub,
        Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C, pow_succ]
      ring


/-- Extracting a fixed coefficient of an integral unit power gives a polynomial in the exponent. -/
theorem unit_power_coefficients {K : Type*} [Field K] [CharZero K]
    (u : (PowerSeries K)ˣ) (constant : PowerSeries.constantCoeff (u : PowerSeries K) = 1)
    (H : PowerSeries K) (height : ℕ) :
    ∃ P : K[X], P.natDegree ≤ height ∧ ∀ n : ℤ,
      P.eval (n : K) =
        PowerSeries.coeff height (H * ((u ^ n : (PowerSeries K)ˣ) : PowerSeries K)) := by
  classical
  let V : PowerSeries K := (u : PowerSeries K) - 1
  let P (h : ℕ) : K[X] := ∑ k ∈ range (h + 1),
    Polynomial.C (PowerSeries.coeff h (V ^ k) / (k.factorial : K)) * descPochhammer K k
  have degree_bound (h : ℕ) : (P h).natDegree ≤ h := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k member
    apply (Polynomial.natDegree_mul_le ..).trans
    simp only [Polynomial.natDegree_C, zero_add, descPochhammer_natDegree]
    exact Nat.le_of_lt_succ (mem_range.mp member)
  have high_power (h k : ℕ) (above : h < k) : PowerSeries.coeff h (V ^ k) = 0 := by
    have vanishing : PowerSeries.constantCoeff V = 0 := by simp [V, constant]
    have divisible := pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr vanishing) k
    exact (PowerSeries.X_pow_dvd_iff.mp divisible) h above
  have natural (h n : ℕ) : (P h).eval (n : K) =
      PowerSeries.coeff h ((u : PowerSeries K) ^ n) := by
    have binomial : (u : PowerSeries K) ^ n = ∑ k ∈ range (n + 1),
        PowerSeries.C (n.choose k : K) * V ^ k := by
      rw [show (u : PowerSeries K) = V + 1 by dsimp only [V]; ring, add_pow]
      apply sum_congr rfl
      intro k _
      simp only [one_pow, mul_one, map_natCast]
      ring
    have truncation : (∑ k ∈ range (n + 1),
        (n.choose k : K) * PowerSeries.coeff h (V ^ k)) =
        ∑ k ∈ range (h + 1), (n.choose k : K) * PowerSeries.coeff h (V ^ k) := by
      rcases le_total (n + 1) (h + 1) with before | after
      · apply sum_subset (range_mono before)
        intro k _ outside
        have above : n < k := by simpa using outside
        rw [Nat.choose_eq_zero_of_lt above, Nat.cast_zero, zero_mul]
      · symm
        apply sum_subset (range_mono after)
        intro k _ outside
        rw [high_power h k (by simpa using outside), mul_zero]
    rw [binomial, map_sum]
    simp only [PowerSeries.coeff_C_mul]
    rw [truncation]
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    apply sum_congr rfl
    intro k _
    rw [Nat.cast_choose_eq_descPochhammer_div K n k]
    ring
  have polynomial_step (h : ℕ) :
      (P h).comp (Polynomial.X + 1) =
        ∑ i ∈ range (h + 1), Polynomial.C (PowerSeries.coeff i (u : PowerSeries K)) *
          P (h - i) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := K))).mono
    rintro x ⟨n, rfl⟩
    simp only [Set.mem_ofPred_eq, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
    rw [← Nat.cast_add_one, natural]
    simp_rw [natural]
    rw [pow_succ', PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (u : PowerSeries K) *
          PowerSeries.coeff j ((u : PowerSeries K) ^ n)) h]
  have step (h : ℕ) (x : K) : (P h).eval (x + 1) =
      ∑ i ∈ range (h + 1), PowerSeries.coeff i (u : PowerSeries K) *
        (P (h - i)).eval x := by
    have evaluated := congrArg (fun Q : K[X] => Q.eval x) (polynomial_step h)
    simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C] using evaluated
  have integral (n : ℤ) : ∀ h : ℕ, (P h).eval (n : K) =
      PowerSeries.coeff h (u ^ n : (PowerSeries K)ˣ) := by
    refine Int.induction_on (motive := fun n => ∀ h : ℕ, (P h).eval (n : K) =
      PowerSeries.coeff h (u ^ n : (PowerSeries K)ˣ)) n ?_ ?_ ?_
    · intro h
      simpa using natural h 0
    · intro n _ h
      rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega]
      simpa only [Int.cast_natCast, zpow_natCast, Units.val_pow_eq_pow_val] using natural h (n + 1)
    · intro n previous h
      induction h using Nat.strong_induction_on with
      | h h lower =>
        have power_step :
            (u : PowerSeries K) * ((u ^ (-(n : ℤ) - 1) : (PowerSeries K)ˣ) : PowerSeries K) =
              (u ^ (-(n : ℤ)) : (PowerSeries K)ˣ) := by
          rw [← Units.val_mul]
          congr 1
          calc
            _ = u ^ (1 : ℤ) * u ^ (-(n : ℤ) - 1) := by rw [zpow_one]
            _ = u ^ (1 + (-(n : ℤ) - 1)) := (zpow_add ..).symm
            _ = _ := by congr 1; omega
        have actual := congrArg (PowerSeries.coeff h) power_step
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (u : PowerSeries K) *
              PowerSeries.coeff j (u ^ (-(n : ℤ) - 1) : (PowerSeries K)ˣ)) h] at actual
        have expected := step h ((-(n : ℤ) - 1 : ℤ) : K)
        have index : (((-(n : ℤ) - 1 : ℤ) : K) + 1) = ((-(n : ℤ) : ℤ) : K) := by
          push_cast
          ring
        rw [index, previous h] at expected
        rw [sum_range_succ'] at actual expected
        have tail :
            (∑ i ∈ range h, PowerSeries.coeff (i + 1) (u : PowerSeries K) *
              PowerSeries.coeff (h - (i + 1))
                (u ^ (-(n : ℤ) - 1) : (PowerSeries K)ˣ)) =
            ∑ i ∈ range h, PowerSeries.coeff (i + 1) (u : PowerSeries K) *
              (P (h - (i + 1))).eval ((-(n : ℤ) - 1 : ℤ) : K) := by
          apply sum_congr rfl
          intro i member
          rw [lower (h - (i + 1)) (by have := mem_range.mp member; omega)]
        rw [tail] at actual
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constant, one_mul,
          Nat.sub_zero] at actual expected
        exact (add_left_cancel (actual.trans expected)).symm
  let Q : K[X] := ∑ i ∈ range (height + 1),
    Polynomial.C (PowerSeries.coeff i H) * P (height - i)
  refine ⟨Q, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    apply (Polynomial.natDegree_mul_le ..).trans
    simp only [Polynomial.natDegree_C, zero_add]
    exact (degree_bound (height - i)).trans (Nat.sub_le _ _)
  · intro n
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    simp_rw [integral]
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i H *
          PowerSeries.coeff j (u ^ n : (PowerSeries K)ˣ)) height]

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelBranches
