/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterMoments
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact joint binomial and falling factorial moments of the BMV compositions. -/

import D5.S3.Quantum.Analysis.RefinedBMVUniformCorner
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic.FieldSimp

/-! # Joint binomial moments of weak three-part compositions -/

namespace RefinedBMV.PositiveCenter

open DimThree (gaps)

private theorem sum_choose_prefix (r t : ℕ) :
    (∑ j ∈ Finset.range (t + 1), j.choose r) = (t + 1).choose (r + 1) := by
  induction t with
  | zero =>
    cases r <;> simp [Nat.choose_succ_succ]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
    exact Nat.add_comm _ _

private def chooseConvolution (r s t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (t + 1), j.choose r * (t - j).choose s

private theorem chooseConvolution_succ (r s t : ℕ) :
    chooseConvolution r (s + 1) (t + 1) =
      chooseConvolution r (s + 1) t + chooseConvolution r s t := by
  unfold chooseConvolution
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, Nat.choose_zero_succ, Nat.mul_zero, Nat.add_zero]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [show t + 1 - j = (t - j) + 1 by omega, Nat.choose_succ_succ, Nat.mul_add]
  exact Nat.add_comm _ _

private theorem chooseConvolution_eq (r s t : ℕ) :
    chooseConvolution r s t = (t + 1).choose (r + s + 1) := by
  induction s generalizing t with
  | zero =>
    simpa [chooseConvolution] using sum_choose_prefix r t
  | succ s hs =>
    induction t with
    | zero =>
      have h : 1 < r + (s + 1) + 1 := by omega
      simp [chooseConvolution, Nat.choose_eq_zero_of_lt h]
    | succ t ht =>
      rw [chooseConvolution_succ, ht, hs]
      rw [show r + (s + 1) + 1 = (r + s + 1) + 1 by omega,
        Nat.choose_succ_succ]
      exact Nat.add_comm _ _

private theorem list_sum_range_nat (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  simp only [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range,
    Multiset.map_coe, Multiset.sum_coe]

private theorem list_sum_flatMap_nat {α : Type*} (l : List α) (g : α → List ℕ) :
    (l.flatMap g).sum = (l.map fun i => (g i).sum).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- The unnormalized joint binomial moment of the last two gap lengths. -/
theorem sum_gaps_mul_choose (p r s : ℕ) :
    ((gaps p).map fun g => g.2.1.choose r * g.2.2.choose s).sum =
      (p + 2).choose (r + s + 2) := by
  rw [gaps, List.map_flatMap, list_sum_flatMap_nat, list_sum_range_nat]
  simp only [List.map_map, Function.comp_apply, list_sum_range_nat]
  calc
    _ = ∑ i ∈ Finset.range (p + 1), (p - i + 1).choose (r + s + 1) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [show p + 1 - i = p - i + 1 by omega]
      exact chooseConvolution_eq r s (p - i)
    _ = ∑ i ∈ Finset.range (p + 1), (i + 1).choose (r + s + 1) := by
      rw [← Finset.sum_range_reflect (fun i : ℕ => (i + 1).choose (r + s + 1)) (p + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [show p + 1 - 1 - i = p - i by omega]
    _ = _ := by
      have h := sum_choose_prefix (r + s + 1) (p + 1)
      rw [Finset.sum_range_succ'] at h
      have hz : Nat.choose 0 (r + s + 1) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simpa only [hz, Nat.add_zero] using h

/-- The unnormalized joint falling factorial moment of the last two gap lengths. -/
theorem sum_gaps_mul_descFactorial (p r s : ℕ) :
    ((gaps p).map fun g => g.2.1.descFactorial r * g.2.2.descFactorial s).sum =
      r.factorial * s.factorial * (p + 2).choose (r + s + 2) := by
  rw [← sum_gaps_mul_choose, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g _
  simp only [Function.comp_apply, Nat.descFactorial_eq_factorial_mul_choose]
  ac_rfl

theorem real_choose_next (p n : ℕ) :
    ((p + 2).choose (n + 3) : ℝ) * ((n : ℝ) + 3) =
      ((p + 2).choose (n + 2) : ℝ) * ((p : ℝ) - (n : ℝ)) := by
  by_cases hnp : n ≤ p
  · have h := Nat.choose_succ_right_eq (p + 2) (n + 2)
    rw [Nat.add_sub_add_right,
      show n + 2 + 1 = n + 3 by omega] at h
    have h' := congrArg (fun k : ℕ ↦ (k : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub hnp] using h'
  · have h0 : (p + 2).choose (n + 2) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have h1 : (p + 2).choose (n + 3) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp only [h0, h1, Nat.cast_zero, zero_mul]

private theorem marginal_square (n : ℕ) : n ^ 2 = 2 * n.choose 2 + n := by
  cases n with
  | zero => simp
  | succ n =>
    have h := Nat.choose_succ_right_eq (n + 1) 1
    simp only [Nat.choose_one_right, Nat.add_sub_cancel] at h
    calc
      (n + 1) ^ 2 = (n + 1) * n + (n + 1) := by ring
      _ = 2 * (n + 1).choose 2 + (n + 1) := by rw [Nat.mul_comm 2, h]

private theorem marginal_first_nat (p : ℕ) :
    ((gaps p).map fun g ↦ g.2.2).sum = (p + 2).choose 3 := by
  simpa only [Nat.choose_zero_right, Nat.choose_one_right, one_mul] using
    sum_gaps_mul_choose p 0 1

private theorem marginal_second_nat (p : ℕ) :
    ((gaps p).map fun g ↦ g.2.2 ^ 2).sum =
      2 * (p + 2).choose 4 + (p + 2).choose 3 := by
  simp only [marginal_square, List.sum_map_add, List.sum_map_mul_left, marginal_first_nat]
  have h := sum_gaps_mul_choose p 0 2
  simp only [Nat.choose_zero_right, one_mul] at h
  rw [h]

/-- The first two moments of a centered exponent used in the log kernel. -/
theorem centered_marginal_sums {p : ℕ} (hp : 0 < p) :
    let N : ℝ := (gaps p).length
    let y (g : ℕ × ℕ × ℕ) := 3 * (g.2.2 : ℝ) / p - 1
    ((gaps p).map y).sum = 0 ∧ ((gaps p).map fun g ↦ y g ^ 2).sum =
      N * ((p : ℝ) + 3) / (2 * p) := by
  dsimp only
  let N : ℝ := (gaps p).length
  let C3 : ℝ := (p + 2).choose 3
  let C4 : ℝ := (p + 2).choose 4
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have h3 : C3 * 3 = N * p := by
    have h := Nat.choose_succ_right_eq (p + 2) 2
    rw [Nat.add_sub_cancel, ← DimThree.gaps_length_eq_choose] at h
    norm_num at h
    change ((p + 2).choose 3 : ℝ) * 3 = ((gaps p).length : ℝ) * p
    exact_mod_cast h
  have h4 : C4 * 4 = C3 * ((p : ℝ) - 1) := by
    have h := Nat.choose_succ_right_eq (p + 2) 3
    rw [show p + 2 - 3 = p - 1 by omega] at h
    have h' := congrArg (fun n : ℕ ↦ (n : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (show 1 ≤ p by omega)] at h'
    norm_num at h'
    exact h'
  have hC3 : C3 = N * p / 3 := by linarith only [h3]
  have hC4 : C4 = C3 * ((p : ℝ) - 1) / 4 := by linarith only [h4]
  have h1 : ((gaps p).map fun g ↦ (g.2.2 : ℝ)).sum = C3 := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) (marginal_first_nat p)
    simpa only [C3, Nat.cast_list_sum, List.map_map, Function.comp_def] using h
  have h2 : ((gaps p).map fun g ↦ (g.2.2 : ℝ) ^ 2).sum = 2 * C4 + C3 := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) (marginal_second_nat p)
    simpa only [C3, C4, Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_pow,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
  have hconst : ((gaps p).map fun _ ↦ (1 : ℝ)).sum = N := by
    simp [N]
  have hsum {f : ℕ × ℕ × ℕ → ℝ} (a b : ℝ) :
      ((gaps p).map fun g ↦ a * f g + b).sum =
        a * ((gaps p).map f).sum + b * N := by
    rw [List.sum_map_add, List.sum_map_mul_left]
    have h : ((gaps p).map fun _ ↦ b).sum = b * N := by
      rw [← hconst, ← List.sum_map_mul_left]
      simp only [mul_one]
    rw [h]
  constructor
  · have hfun (g : ℕ × ℕ × ℕ) :
        3 * (g.2.2 : ℝ) / p - 1 = (3 / (p : ℝ)) * g.2.2 + (-1) := by ring
    simp only [hfun, hsum, h1, hC3]
    field_simp [hpR]
    <;> ring
  · have hfun (g : ℕ × ℕ × ℕ) :
        (3 * (g.2.2 : ℝ) / p - 1) ^ 2 =
          (3 / (p : ℝ)) ^ 2 * (g.2.2 : ℝ) ^ 2 + (-(6 / (p : ℝ)) * g.2.2 + 1) := by
      ring
    simp only [hfun, List.sum_map_add, List.sum_map_mul_left, hsum, h1, h2, hC4, hC3, one_mul]
    field_simp [hpR]
    <;> ring

private theorem marginal_cubic_nat (p : ℕ) :
    ((gaps p).map fun g ↦ g.2.2 ^ 3).sum =
      6 * (p + 2).choose 5 + 6 * (p + 2).choose 4 + (p + 2).choose 3 := by
  have h₁ : ((gaps p).map fun g ↦ g.2.2.descFactorial 1).sum = (p + 2).choose 3 := by
    simpa only [Nat.descFactorial_one] using marginal_first_nat p
  have h₂ : ((gaps p).map fun g ↦ g.2.2.descFactorial 2).sum = 2 * (p + 2).choose 4 := by
    simpa only [Nat.descFactorial_zero, one_mul, Nat.factorial_zero,
      show (2 : ℕ).factorial = 2 by decide] using sum_gaps_mul_descFactorial p 0 2
  have h₃ : ((gaps p).map fun g ↦ g.2.2.descFactorial 3).sum = 6 * (p + 2).choose 5 := by
    simpa only [Nat.descFactorial_zero, one_mul, Nat.factorial_zero,
      show (3 : ℕ).factorial = 6 by decide] using sum_gaps_mul_descFactorial p 0 3
  have hpow (l : ℕ) : l ^ 3 = l.descFactorial 3 + 3 * l.descFactorial 2 +
      l.descFactorial 1 := by
    rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial l 3]
    norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.descFactorial_zero]
    <;> ring
  simp only [hpow, List.sum_map_add, List.sum_map_mul_left, h₁, h₂, h₃]
  ring

/-- The centered third moment is strictly positive and has a closed degree formula. -/
theorem centered_marginal_cubic_sum {p : ℕ} (hp : 0 < p) :
    let N : ℝ := (gaps p).length
    let y (g : ℕ × ℕ × ℕ) := 3 * (g.2.2 : ℝ) / p - 1
    ((gaps p).map fun g ↦ y g ^ 3).sum =
      N * ((p : ℝ) + 3) * (2 * (p : ℝ) + 3) / (10 * (p : ℝ) ^ 2) := by
  dsimp only
  let N : ℝ := (gaps p).length
  let C3 : ℝ := (p + 2).choose 3
  let C4 : ℝ := (p + 2).choose 4
  let C5 : ℝ := (p + 2).choose 5
  have h3 : C3 * 3 = N * p := by
    simpa [C3, N, DimThree.gaps_length_eq_choose] using real_choose_next p 0
  have h4 : C4 * 4 = C3 * ((p : ℝ) - 1) := by
    have h := real_choose_next p 1
    norm_num only [Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num [C3, C4]
  have h5 : C5 * 5 = C4 * ((p : ℝ) - 2) := by
    have h := real_choose_next p 2
    norm_num only [Nat.cast_ofNat] at h
    convert h using 1 <;> norm_num [C4, C5]
  have hC3 : C3 = N * p / 3 := by linarith only [h3]
  have hC4 : C4 = C3 * ((p : ℝ) - 1) / 4 := by linarith only [h4]
  have hC5 : C5 = C4 * ((p : ℝ) - 2) / 5 := by linarith only [h5]
  have h₁ : ((gaps p).map fun g ↦ (g.2.2 : ℝ)).sum = C3 := by
    simpa only [C3, Nat.cast_list_sum, List.map_map, Function.comp_def] using
      congrArg (fun a : ℕ ↦ (a : ℝ)) (marginal_first_nat p)
  have h₂ : ((gaps p).map fun g ↦ (g.2.2 : ℝ) ^ 2).sum = 2 * C4 + C3 := by
    simpa only [C3, C4, Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_pow,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun a : ℕ ↦ (a : ℝ)) (marginal_second_nat p)
  have h₃ : ((gaps p).map fun g ↦ (g.2.2 : ℝ) ^ 3).sum = 6 * C5 + 6 * C4 + C3 := by
    simpa only [C3, C4, C5, Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_pow,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun a : ℕ ↦ (a : ℝ)) (marginal_cubic_nat p)
  have hconst : ((gaps p).map fun _ ↦ (-1 : ℝ)).sum = -N := by
    have h : ((gaps p).map fun _ ↦ (1 : ℝ)).sum = N := by simp [N]
    calc
      _ = ((gaps p).map fun _ ↦ (-1 : ℝ) * 1).sum := by simp only [mul_one]
      _ = _ := by rw [List.sum_map_mul_left, h, neg_one_mul]
  have hfun (g : ℕ × ℕ × ℕ) :
      (3 * (g.2.2 : ℝ) / p - 1) ^ 3 =
        (3 / (p : ℝ)) ^ 3 * (g.2.2 : ℝ) ^ 3 +
        (-3 * (3 / (p : ℝ)) ^ 2) * (g.2.2 : ℝ) ^ 2 +
        (9 / (p : ℝ)) * (g.2.2 : ℝ) + (-1) := by ring
  simp only [hfun, List.sum_map_add, List.sum_map_mul_left, hconst,
    h₁, h₂, h₃, hC5, hC4, hC3]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  <;> ring

#print axioms centered_marginal_cubic_sum
#print axioms sum_gaps_mul_descFactorial

end RefinedBMV.PositiveCenter
