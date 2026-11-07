/- GID: D5/S3/Combinatorics/Delannoy/GrauOllerMarcenVaronaFactorialBorderGrowth
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Delannoy/GrauOllerMarcenVaronaFactorialBorderGrowth
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Factorial-border Delannoy diagonal ratios have additive error tending to zero. -/

/-
admission_basis: open-problem-resolution (#19938; Proved)
escape_witness: none (admission is the external named problem settlement)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22168
Direct frozen dependencies: D5/S3/Combinatorics/Matroids/SpeyerUniformNormality.qAB.
qAB declaration statement_id: sha256:29896652822aaa7119e8470a97a0a75560731fffc4cbfc489026fab990c39f29.
The recurrence and additive-limit statements use the conventions of #19938 and #19939.
The literal recurrence defines the unit-border array; proofs use qAB evaluated at one.
All declarations have utility none: unbounded identities, estimates and limits.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.diagonal_convolution: proof_shape: content; escape_witness: none; Direct frozen dependencies: none.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.Q_of_gt: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: qAB.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.Q_nonneg: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: qAB.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.W_le_M: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.Q_scaled_bound: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: qAB.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.Q_scaled_limit: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: qAB.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.summable_M: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.summable_succ_M: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.tendsto_of_scaled: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.P_scaled_bound: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: qAB.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.P_scaled_limit: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: qAB.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.diagonal_Q_scaled_limit: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: qAB.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.Q_factorial: proof_shape: content; escape_witness: none; Direct frozen dependencies: qAB.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.ratio_transfer: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.result: proof_shape: content; escape_witness: none; Direct frozen dependencies: qAB.
-/

import D5.S3.Combinatorics.Matroids.SpeyerUniformNormality
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.Normed.Group.Tannery



namespace D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth

open Filter Topology

/-- The weighted Delannoy array with `α = β = γ = 1` and borders `f(n,0) = f(0,n) = b n`. -/
def f (b : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => b n
  | m + 1, 0 => b (m + 1)
  | m + 1, n + 1 => f b m (n + 1) + f b (m + 1) n + f b m n

/-- The factorial-border conjecture: `f_{n+1,n+1}/f_{n,n} − (n + 1) → 0` for `b(n) = n!` (OEIS A346374). -/
def claimFactorial : Prop :=
  Tendsto (fun n : ℕ => (f Nat.factorial (n + 1) (n + 1) : ℝ) / f Nat.factorial n n - ((n : ℝ) + 1))
    atTop (𝓝 0)


end D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth

namespace D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth
open Finset Filter Topology Asymptotics
open scoped BigOperators
open D5.S3.Combinatorics.Matroids.SpeyerUniformNormality (qAB)

@[simp] private theorem f_zero (b : ℕ → ℕ) (n : ℕ) : f b 0 n = b n := by simp [f]
@[simp] private theorem f_zero_right (b : ℕ → ℕ) (m : ℕ) : f b m 0 = b m := by
  cases m <;> simp [f]

private theorem f_succ (b : ℕ → ℕ) (m n : ℕ) :
    f b (m+1) (n+1) = f b m (n+1) + f b (m+1) n + f b m n := by simp [f]


@[simp] private theorem d_zero (n : ℕ) : (f (fun _ => 1) 0 n : ℝ) = 1 := by simp
@[simp] private theorem d_zero_right (m : ℕ) : (f (fun _ => 1) m 0 : ℝ) = 1 := by simp
private theorem d_succ (m n : ℕ) :
    (f (fun _ => 1) (m+1) (n+1) : ℝ) = (f (fun _ => 1) m (n+1) : ℝ) + (f (fun _ => 1) (m+1) n : ℝ) + (f (fun _ => 1) m n : ℝ) := by
  simp only [f_succ, Nat.cast_add]

def delta (b : ℕ → ℕ) : ℕ → ℝ
  | 0 => b 0
  | n+1 => (b (n+1) : ℝ) - b n

private theorem sum_delta (b : ℕ → ℕ) (m : ℕ) :
    ∑ j ∈ range (m+1), delta b j = b m := by
  rw [sum_range_succ']
  simp only [delta]
  rw [sum_range_sub (fun j => (b j:ℝ)) m]
  ring

noncomputable def conv (a : ℕ → ℝ) (m n : ℕ) : ℝ :=
  ∑ j ∈ range (m+1), a j * (f (fun _ => 1) (m-j) n : ℝ)

@[simp] private theorem conv_zero (a : ℕ → ℝ) (n : ℕ) : conv a 0 n = a 0 := by
  simp [conv]
@[simp] private theorem conv_zero_right (a : ℕ → ℝ) (m : ℕ) :
    conv a m 0 = ∑ j ∈ range (m+1), a j := by simp [conv]

private theorem conv_succ (a : ℕ → ℝ) (m n : ℕ) :
    conv a (m+1) (n+1) = conv a m (n+1) + conv a (m+1) n + conv a m n := by
  have hs (r : ℕ) : conv a (m+1) r =
      (∑ j ∈ range (m+1), a j * (f (fun _ => 1) (m+1-j) r : ℝ)) + a (m+1) := by
    unfold conv
    rw [sum_range_succ]
    simp
  rw [hs, hs]
  simp only [conv]
  have h : ∀ j ∈ range (m+1),
      a j * (f (fun _ => 1) (m+1-j) (n+1) : ℝ) =
        a j * (f (fun _ => 1) (m-j) (n+1) : ℝ) + a j * (f (fun _ => 1) (m+1-j) n : ℝ) + a j * (f (fun _ => 1) (m-j) n : ℝ) := by
    intro j hj
    have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.mp hj)
    rw [show m+1-j = (m-j)+1 by omega, d_succ]
    ring
  rw [sum_congr rfl h]
  simp only [sum_add_distrib]
  ring

private theorem border_convolution (b : ℕ → ℕ) (m n : ℕ) :
    (f b m n : ℝ) = conv (delta b) m n + conv (delta b) n m - (b 0 : ℝ) * (f (fun _ => 1) m n : ℝ) := by
  induction m generalizing n
  case zero =>
    rw [f_zero, conv_zero, conv_zero_right, sum_delta, d_zero]
    simp [delta]
  case succ m ih =>
    induction n
    case zero =>
      rw [f_zero_right, conv_zero, conv_zero_right, sum_delta, d_zero_right]
      simp [delta]
    case succ n ihn =>
      rw [f_succ]
      simp only [Nat.cast_add]
      rw [ih, ih, ihn, conv_succ, conv_succ, d_succ]
      ring

theorem diagonal_convolution (b : ℕ → ℕ) (n : ℕ) :
    (f b n n : ℝ) = 2 * conv (delta b) n n - (b 0 : ℝ) * (f (fun _ => 1) n n : ℝ) := by
  rw [border_convolution]
  ring


@[simp] private theorem H_zero (n : ℕ) : (qAB 0 n).eval 1 = 1 := by simp [qAB]

private theorem H_expand (m n : ℕ) :
    (qAB m n).eval 1 = 1 + ∑ i ∈ range (m+1), (2:ℝ)^(i+1) * m.choose (i+1) * n.choose (i+1) := by
  have hs : (qAB m n).eval 1 = ∑ i ∈ range (m+2), (2:ℝ)^i * m.choose i * n.choose i := by
    rw [show m+2 = (m+1)+1 by omega, sum_range_succ]
    simp [qAB, Polynomial.eval_finsetSum, one_add_one_eq_two, mul_comm, mul_left_comm,
      mul_assoc]
  rw [hs, sum_range_succ']
  simp [add_comm]

private theorem H_succ_left (m n : ℕ) : (qAB (m+1) n).eval 1 = (qAB m n).eval 1 +
    2 * ∑ i ∈ range (m+1), (2:ℝ)^i * m.choose i * n.choose (i+1) := by
  rw [H_expand (m+1) n, sum_range_succ]
  simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  rw [H_expand m n]
  have hs : (∑ i ∈ range (m+1), (2:ℝ)^(i+1) * (m+1).choose (i+1) * n.choose (i+1)) =
      (∑ i ∈ range (m+1), (2:ℝ)^(i+1) * m.choose (i+1) * n.choose (i+1)) +
      2 * ∑ i ∈ range (m+1), (2:ℝ)^i * m.choose i * n.choose (i+1) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
    ring
  rw [hs]
  ring

private theorem H_succ (m n : ℕ) :
    (qAB (m+1) (n+1)).eval 1 = (qAB m (n+1)).eval 1 + (qAB (m+1) n).eval 1 + (qAB m n).eval 1 := by
  rw [H_succ_left, H_succ_left m n]
  simp_rw [Nat.choose_succ_succ, Nat.cast_add, mul_add]
  rw [sum_add_distrib]
  simp only [qAB, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    one_add_one_eq_two, Nat.cast_mul, mul_comm _ ((2:ℝ)^_), ← mul_assoc]
  ring

@[simp] private theorem H_zero_right (m : ℕ) : (qAB m 0).eval 1 = 1 := by
  induction m
  case zero => simp
  case succ m ih => rw [H_succ_left]; simp [ih]

private theorem d_eq_binomial (m n : ℕ) : (f (fun _ => 1) m n : ℝ) = (qAB m n).eval 1 := by
  induction m generalizing n
  case zero => simp
  case succ m ih =>
    induction n
    case zero => simp
    case succ n ihn => rw [d_succ, H_succ, ih, ih, ihn]

-- A uniform bound valid on the whole factorial convolution, without a cutoff.
private theorem choose_ratio_bound (n k i : ℕ) (hkn : k ≤ n) (hik : i ≤ k) :
    (n.choose i : ℝ) ≤ n.choose k * (k.choose i : ℝ) := by
  have hp := Nat.choose_pos (show k-i ≤ n-i by omega)
  have h := Nat.choose_mul (n := n) hik
  have hle : n.choose i ≤ n.choose i * (n-i).choose (k-i) := by exact Nat.le_mul_of_pos_right (n.choose i) hp
  rw [← h] at hle
  exact_mod_cast hle

private theorem H_le_choose_mul_six_pow (n k : ℕ) (hkn : k ≤ n) :
    (qAB k n).eval 1 ≤ (n.choose k : ℝ) * 6^k := by
  simp only [qAB, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    one_add_one_eq_two, Nat.cast_mul, mul_comm _ ((2:ℝ)^_), ← mul_assoc]
  calc
    _ ≤ ∑ i ∈ range (k+1), (n.choose k : ℝ) * (2:ℝ)^k * ((2:ℝ)^i * k.choose i) := by
      apply sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (mem_range.mp hi)
      have h1 := choose_ratio_bound n k i hkn hik
      have h2 : (k.choose i : ℝ) ≤ (2:ℝ)^k := by exact_mod_cast Nat.choose_le_two_pow k i
      have h3 : 0 ≤ (2:ℝ)^i * (k.choose i : ℝ) := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) h3,
        mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ (n.choose k : ℝ) * (2:ℝ)^i * k.choose i by positivity)]
    _ = (n.choose k : ℝ) * 6^k := by
      rw [← mul_sum]
      have hs : ∑ i ∈ range (k+1), (2:ℝ)^i * k.choose i = 3^k := by
        simpa only [one_pow, mul_one, two_add_one_eq_three] using (add_pow (2:ℝ) 1 k).symm
      rw [hs]
      rw [mul_assoc, ← mul_pow]
      norm_num


private theorem choose_scaled_ratio_bound (n k i : ℕ) (hkn : k ≤ n) (hik : i < k) :
    (n:ℝ) * (n.choose i : ℝ) ≤ (k:ℝ) * (n.choose k : ℝ) * (k.choose i : ℝ) := by
  have hi : i ≤ k := Nat.le_of_lt hik
  have hin : i ≤ n := hi.trans hkn
  have h1 := choose_ratio_bound n k i hkn hi
  have h2 := choose_ratio_bound n k (i+1) hkn hik
  have hn : (n.choose (i+1) : ℝ) * ((i:ℝ)+1) = (n.choose i : ℝ) * ((n:ℝ)-i) := by
    have ht := congrArg (fun x : ℕ => (x:ℝ)) (Nat.choose_succ_right_eq n i)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hin] using ht
  have hk : (k.choose (i+1) : ℝ) * ((i:ℝ)+1) = (k.choose i : ℝ) * ((k:ℝ)-i) := by
    have ht := congrArg (fun x : ℕ => (x:ℝ)) (Nat.choose_succ_right_eq k i)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hi] using ht
  have hk' := congrArg (fun x : ℝ => (n.choose k:ℝ) * x) hk
  have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (i:ℝ) by positivity)
  have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (i:ℝ)+1 by positivity)
  nlinarith

private theorem H_leading (k n : ℕ) : (qAB k n).eval 1 - (2:ℝ)^k * n.choose k =
    ∑ i ∈ range k, (2:ℝ)^i * k.choose i * n.choose i := by
  simp only [qAB, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    one_add_one_eq_two, Nat.cast_mul, mul_comm _ ((2:ℝ)^_), ← mul_assoc]
  rw [sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, mul_one]
  ring

private theorem H_scaled_error_bound (n k : ℕ) (hkn : k ≤ n) :
    0 ≤ (n:ℝ) * ((qAB k n).eval 1 - (2:ℝ)^k * n.choose k) ∧
    (n:ℝ) * ((qAB k n).eval 1 - (2:ℝ)^k * n.choose k) ≤
      (k:ℝ) * n.choose k * 6^k := by
  rw [H_leading]
  constructor
  · positivity
  calc
    _ = ∑ i ∈ range k, (2:ℝ)^i * k.choose i * ((n:ℝ) * n.choose i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ range k, ((k:ℝ) * n.choose k) * ((2:ℝ)^i * k.choose i * k.choose i) := by
      apply sum_le_sum
      intro i hi
      have h := choose_scaled_ratio_bound n k i hkn (mem_range.mp hi)
      have hp : 0 ≤ (2:ℝ)^i * (k.choose i:ℝ) := by positivity
      nlinarith [mul_nonneg hp (sub_nonneg.mpr h)]
    _ = ((k:ℝ) * n.choose k) * ∑ i ∈ range k, (2:ℝ)^i * k.choose i * k.choose i := by
      rw [mul_sum]
    _ ≤ ((k:ℝ) * n.choose k) * (qAB k k).eval 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simp only [qAB, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    one_add_one_eq_two, Nat.cast_mul, mul_comm _ ((2:ℝ)^_), ← mul_assoc]
      rw [sum_range_succ]
      exact le_add_of_nonneg_right (by positivity)
    _ ≤ _ := by
      have h := H_le_choose_mul_six_pow k k (le_refl k)
      simp only [Nat.choose_self, Nat.cast_one, one_mul] at h
      exact mul_le_mul_of_nonneg_left h (by positivity)


noncomputable def W (k : ℕ) : ℝ := (2:ℝ)^k / k.factorial
noncomputable def M (k : ℕ) : ℝ := (6:ℝ)^k / k.factorial
noncomputable def Q (n k : ℕ) : ℝ :=
  if k ≤ n then (qAB k n).eval 1 / ((k.factorial:ℝ) * n.choose k) else 0

@[simp] theorem Q_of_gt (n k : ℕ) (h : n < k) : Q n k = 0 := by
  simp [Q, Nat.not_le.mpr h]

theorem Q_nonneg (n k : ℕ) : 0 ≤ Q n k := by
  unfold Q
  split_ifs
  · simp only [qAB, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    one_add_one_eq_two, Nat.cast_mul, mul_comm _ ((2:ℝ)^_), ← mul_assoc]; positivity
  · positivity

theorem W_le_M (k : ℕ) : W k ≤ M k := by
  unfold W M
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by positivity)

private theorem Q_le_M (n k : ℕ) : Q n k ≤ M k := by
  by_cases hkn : k ≤ n
  · have hc : 0 < (n.choose k:ℝ) := by exact_mod_cast Nat.choose_pos hkn
    have hf : 0 < (k.factorial:ℝ) := by positivity
    rw [Q, if_pos hkn]
    apply (div_le_iff₀ (mul_pos hf hc)).2
    have ht := H_le_choose_mul_six_pow n k hkn
    have he : M k * ((k.factorial:ℝ) * n.choose k) = (n.choose k:ℝ) * 6^k := by
      unfold M
      field_simp
    rw [he]
    exact ht
  · simp only [Q, if_neg hkn]
    unfold M
    positivity

private theorem Q_scaled_identity (n k : ℕ) (hkn : k ≤ n) :
    (n:ℝ) * (Q n k - W k) =
      ((n:ℝ) * ((qAB k n).eval 1 - (2:ℝ)^k * n.choose k)) / ((k.factorial:ℝ) * n.choose k) := by
  have hc : (n.choose k:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hkn)
  have hf : (k.factorial:ℝ) ≠ 0 := by positivity
  rw [Q, if_pos hkn, W]
  field_simp
  <;> ring

theorem Q_scaled_bound (n k : ℕ) : |(n:ℝ) * (Q n k - W k)| ≤ (k:ℝ) * M k := by
  by_cases hkn : k ≤ n
  · have hc : 0 < (n.choose k:ℝ) := by exact_mod_cast Nat.choose_pos hkn
    have hf : 0 < (k.factorial:ℝ) := by positivity
    rw [Q_scaled_identity n k hkn]
    have ht := H_scaled_error_bound n k hkn
    rw [abs_of_nonneg (div_nonneg ht.1 (mul_nonneg hf.le hc.le))]
    apply (div_le_iff₀ (mul_pos hf hc)).2
    have he : ((k:ℝ) * M k) * ((k.factorial:ℝ) * n.choose k) =
        (k:ℝ) * n.choose k * 6^k := by
      unfold M
      field_simp
      <;> ring
    rw [he]
    exact ht.2
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    rw [Q_of_gt n k hnk, zero_sub, mul_neg, abs_neg,
      abs_of_nonneg (show 0 ≤ (n:ℝ) * W k by unfold W; positivity)]
    calc
      (n:ℝ) * W k ≤ (k:ℝ) * W k := mul_le_mul_of_nonneg_right (by exact_mod_cast hnk.le) (by unfold W; positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (W_le_M k) (by positivity)

private theorem tendsto_scaled_choose_ratio (i k : ℕ) (hik : i < k) :
    Tendsto (fun n : ℕ => (n:ℝ) * n.choose i / n.choose k) atTop
      (𝓝 (if k = i+1 then (k:ℝ) else 0)) := by
  let d := k-(i+1)
  have hd : k = i+1+d := by exact Eq.symm (Nat.add_sub_of_le hik)
  have he : (fun n : ℕ => (n:ℝ) * n.choose i / n.choose k) ~[atTop]
      (fun n : ℕ => (n:ℝ) * ((n:ℝ)^i / i.factorial) / ((n:ℝ)^k / k.factorial)) :=
    (IsEquivalent.refl.mul (isEquivalent_choose i)).div (isEquivalent_choose k)
  have ht := ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow d).const_mul
    ((k.factorial:ℝ) / i.factorial)
  have hf : (i.factorial:ℝ) ≠ 0 := by positivity
  have hg : (k.factorial:ℝ) ≠ 0 := by positivity
  have hc : (k.factorial:ℝ) / i.factorial * (0:ℝ)^d =
      (if k = i+1 then (k:ℝ) else 0) := by
    by_cases hk : k = i+1
    · have hd0 : d = 0 := by exact Eq.symm (Nat.eq_sub_of_add_eq' (id (Eq.symm hk)))
      simp only [hd0, pow_zero, mul_one, if_pos hk]
      rw [hk, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      exact mul_div_cancel_right₀ _ hf
    · have hd0 : d ≠ 0 := by dsimp; omega
      simp [hd0, hk]
  rw [hc] at ht
  apply he.symm.tendsto_nhds
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [hd, pow_add, pow_add, pow_one, inv_pow]
  field_simp [hf, hg, hn0]
  <;> ring


noncomputable def G (k : ℕ) : ℝ :=
  (1 / (k.factorial:ℝ)) * ∑ i ∈ range k,
    (2:ℝ)^i * k.choose i * (if k = i+1 then (k:ℝ) else 0)

theorem Q_scaled_limit (k : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ) * (Q n k - W k)) atTop (𝓝 (G k)) := by
  have ht : Tendsto (fun n : ℕ => (1 / (k.factorial:ℝ)) *
      ∑ i ∈ range k, (2:ℝ)^i * k.choose i * ((n:ℝ) * n.choose i / n.choose k))
      atTop (𝓝 (G k)) := by
    apply Tendsto.const_mul
    apply tendsto_finsetSum
    intro i hi
    exact (tendsto_scaled_choose_ratio i k (mem_range.mp hi)).const_mul _
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  have hc : (n.choose k:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hn)
  have hf : (k.factorial:ℝ) ≠ 0 := by positivity
  rw [Q_scaled_identity n k hn, H_leading]
  rw [mul_sum, mul_sum, sum_div]
  apply sum_congr rfl
  intro i hi
  field_simp
  <;> ring

private theorem summable_W : Summable W := Real.summable_pow_div_factorial 2
theorem summable_M : Summable M := Real.summable_pow_div_factorial 6
private theorem summable_scaled_M : Summable (fun k : ℕ => (k:ℝ) * M k) := by
  apply Summable.of_nonneg_of_le (fun k => by unfold M; positivity) _
    (Real.summable_pow_div_factorial 12)
  intro k
  have hk : (k:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  unfold M
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    (k:ℝ) * (6:ℝ)^k ≤ (2:ℝ)^k * 6^k := mul_le_mul_of_nonneg_right hk (by positivity)
    _ = 12^k := by rw [← mul_pow]; norm_num

theorem summable_succ_M : Summable (fun k : ℕ => ((k:ℝ)+1) * M k) := by
  convert summable_scaled_M.add summable_M using 1
  ext k
  ring

private theorem W_tsum_pos : 0 < ∑' k, W k := by
  apply summable_W.tsum_pos (fun k => by unfold W; positivity) 0
  norm_num [W]

private theorem Q_summable (n : ℕ) : Summable (Q n) := by
  apply summable_of_ne_finset_zero (s := range (n+1))
  intro k hk
  apply Q_of_gt
  simp only [mem_range, not_lt] at hk
  omega

private theorem Q_tsum (n : ℕ) : ∑' k, Q n k = ∑ k ∈ range (n+1), Q n k := by
  apply tsum_eq_sum
  intro k hk
  apply Q_of_gt
  simp only [mem_range, not_lt] at hk
  omega

private theorem Q_scaled_tsum_limit :
    Tendsto (fun n : ℕ => (n:ℝ) * ((∑' k, Q n k) - ∑' k, W k)) atTop
      (𝓝 (∑' k, G k)) := by
  have ht := tendsto_tsum_of_dominated_convergence summable_scaled_M Q_scaled_limit
    (Eventually.of_forall (fun n k => by simpa only [Real.norm_eq_abs] using Q_scaled_bound n k))
  convert ht using 1
  ext n
  rw [tsum_mul_left, (Q_summable n).tsum_sub summable_W]


theorem tendsto_of_scaled (r : ℕ → ℝ) (C K : ℝ)
    (h : Tendsto (fun n : ℕ => (n:ℝ) * (r n - C)) atTop (𝓝 K)) :
    Tendsto r atTop (𝓝 C) := by
  have ht := h.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  simp only [mul_zero] at ht
  have hz : Tendsto (fun n : ℕ => r n - C) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
    <;> ring
  simpa using hz.add_const C

noncomputable def P (n k : ℕ) : ℝ :=
  if k < n then Q n k / (n-k:ℕ) else 0

theorem P_scaled_bound (n k : ℕ) : |(n:ℝ) * P n k| ≤ ((k:ℝ)+1) * M k := by
  by_cases hkn : k < n
  · have hp : 0 < (n-k:ℕ) := by exact Nat.zero_lt_sub_of_lt hkn
    have hpR : (0:ℝ) < (n-k:ℕ) := by exact Nat.cast_pos'.mpr hp
    have hnat : n ≤ (k+1)*(n-k) := by
      have he := Nat.sub_add_cancel (Nat.le_of_lt hkn)
      have hm := Nat.mul_le_mul_left k hp
      nlinarith
    have hrat : (n:ℝ) / (n-k:ℕ) ≤ (k:ℝ)+1 := by
      apply (div_le_iff₀ hpR).2
      exact_mod_cast hnat
    have hq := Q_nonneg n k
    rw [P, if_pos hkn, abs_of_nonneg (by positivity)]
    calc
      (n:ℝ) * (Q n k / (n-k:ℕ)) = ((n:ℝ) / (n-k:ℕ)) * Q n k := by ring
      _ ≤ ((k:ℝ)+1) * M k := mul_le_mul hrat (Q_le_M n k) (Q_nonneg n k) (by positivity)
  · simp only [P, if_neg hkn, mul_zero, abs_zero]
    unfold M
    positivity

theorem P_scaled_limit (k : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ) * P n k) atTop (𝓝 (W k)) := by
  have hq := tendsto_of_scaled (fun n => Q n k) (W k) (G k) (Q_scaled_limit k)
  have hn : Tendsto (fun n : ℕ => (n:ℝ) / (n-k:ℕ)) atTop (𝓝 (1:ℝ)) := by
    apply (tendsto_natCast_div_add_atTop (-(k:ℝ))).congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [Nat.cast_sub hn]
    simp only [sub_eq_add_neg]
  have ht := hn.mul hq
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k+1)] with n hn
  rw [P, if_pos (show k < n by omega)]
  ring


private theorem P_tsum (n : ℕ) : ∑' k, P n k = ∑ k ∈ range (n+1), P n k := by
  apply tsum_eq_sum
  intro k hk
  have hkn : ¬ k < n := by simp only [mem_range, not_lt] at hk; omega
  simp [P, hkn]

private theorem P_scaled_tsum_limit :
    Tendsto (fun n : ℕ => (n:ℝ) * ∑' k, P n k) atTop (𝓝 (∑' k, W k)) := by
  have ht := tendsto_tsum_of_dominated_convergence summable_succ_M P_scaled_limit
    (Eventually.of_forall (fun n k => by simpa only [Real.norm_eq_abs] using P_scaled_bound n k))
  simpa only [tsum_mul_left] using ht

theorem diagonal_Q_scaled_limit :
    Tendsto (fun n : ℕ => (n:ℝ) * Q n n) atTop (𝓝 (0:ℝ)) := by
  apply squeeze_zero (fun n => mul_nonneg (by positivity) (Q_nonneg n n))
    (fun n => mul_le_mul_of_nonneg_left (Q_le_M n n) (by positivity))
  exact summable_scaled_M.tendsto_atTop_zero


theorem Q_factorial (n k : ℕ) (hkn : k ≤ n) :
    Q n k = ((n-k).factorial:ℝ) * (f (fun _ => 1) k n : ℝ) / n.factorial := by
  have hc : (n.choose k:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hkn)
  have hf : (k.factorial:ℝ) ≠ 0 := by positivity
  have hn : (n.factorial:ℝ) ≠ 0 := by positivity
  have he : (n.factorial:ℝ) = (n.choose k:ℝ) * (k.factorial:ℝ) * (n-k).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hkn).symm
  rw [Q, if_pos hkn, d_eq_binomial]
  apply (div_eq_div_iff (mul_ne_zero hf hc) hn).2
  rw [he]
  ring

private theorem delta_factorial_term (n k : ℕ) (hkn : k ≤ n) :
    delta Nat.factorial (n-k) * (f (fun _ => 1) k n : ℝ) / n.factorial = Q n k - P n k := by
  by_cases hk : k = n
  · subst k
    rw [Q_factorial n n (le_refl n)]
    simp [delta, P]
  · have hkn' : k < n := by exact Nat.lt_of_le_of_ne hkn hk
    have hd : delta Nat.factorial (n-k) =
        ((n-k).factorial:ℝ) - (n-k-1).factorial := by
      cases he : n-k
      case zero => omega
      case succ j => simp [delta, he]
    have hden : (n-k:ℕ) ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hkn'
    have hdenR : ((n-k:ℕ):ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr hden
    have hn : (n.factorial:ℝ) ≠ 0 := by positivity
    have he : ((n-k:ℕ):ℝ) * ((n-k-1).factorial:ℝ) = ((n-k).factorial:ℝ) := by
      exact_mod_cast Nat.mul_factorial_pred hden
    rw [hd, P, if_pos hkn', Q_factorial n k hkn, ← he]
    field_simp [hdenR, hn]
    <;> ring

private theorem normalized_convolution (n : ℕ) :
    (f Nat.factorial n n:ℝ) / n.factorial =
      2 * ∑' k, Q n k - 2 * ∑' k, P n k - Q n n := by
  have hc : conv (delta Nat.factorial) n n / n.factorial =
      (∑' k, Q n k) - ∑' k, P n k := by
    unfold conv
    have href := sum_range_reflect
      (fun j => delta Nat.factorial j * (f (fun _ => 1) (n-j) n : ℝ)) (n+1)
    simp only [Nat.add_sub_cancel] at href
    rw [← href, sum_div, Q_tsum, P_tsum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
    rw [Nat.sub_sub_self hkn]
    exact delta_factorial_term n k hkn
  have hd : (f (fun _ => 1) n n : ℝ) / n.factorial = Q n n := by
    rw [Q_factorial n n (le_refl n)]
    simp
  rw [diagonal_convolution, Nat.factorial_zero, Nat.cast_one, one_mul, sub_div,
    mul_div_assoc, hc, hd]
  ring

private theorem factorial_first_order :
    Tendsto (fun n : ℕ => (n:ℝ) *
      ((f Nat.factorial n n:ℝ) / n.factorial - 2 * ∑' k, W k)) atTop
      (𝓝 (2 * (∑' k, G k) - 2 * ∑' k, W k)) := by
  have ht := ((Q_scaled_tsum_limit.const_mul 2).sub
    (P_scaled_tsum_limit.const_mul 2)).sub diagonal_Q_scaled_limit
  simp only [sub_zero] at ht
  convert ht using 1
  ext n
  rw [normalized_convolution]
  ring
private theorem first_order_difference (r : ℕ → ℝ) (C K : ℝ)
    (h0 : Tendsto r atTop (𝓝 C))
    (h1 : Tendsto (fun n : ℕ => (n:ℝ) * (r n - C)) atTop (𝓝 K)) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1) * (r (n+1) - r n)) atTop (𝓝 0) := by
  have hshift := h1.comp (tendsto_add_atTop_nat 1)
  have hlim := (hshift.sub h1).sub (h0.sub_const C)
  simp only [sub_self] at hlim
  convert hlim using 1
  ext n
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  ring

theorem ratio_transfer (a b r : ℕ → ℝ) (C K L : ℝ)
    (hb : ∀ n, b n ≠ 0) (ha : ∀ n, a n = b n * r n) (hC : C ≠ 0)
    (h0 : Tendsto r atTop (𝓝 C))
    (h1 : Tendsto (fun n : ℕ => (n:ℝ) * (r n - C)) atTop (𝓝 K))
    (hB : Tendsto (fun n : ℕ => b (n+1) / b n / ((n:ℝ)+1)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => a (n+1) / a n - b (n+1) / b n) atTop (𝓝 0) := by
  have hd := first_order_difference r C K h0 h1
  have ht := (hB.mul hd).div h0 hC
  simp only [mul_zero, zero_div] at ht
  apply ht.congr'
  filter_upwards [h0.eventually (eventually_ne_nhds hC)] with n hn
  change (b (n+1) / b n / ((n:ℝ)+1) *
    (((n:ℝ)+1) * (r (n+1) - r n))) / r n =
    a (n+1) / a n - b (n+1) / b n
  rw [ha, ha]
  have hp : (n:ℝ)+1 ≠ 0 := by exact Nat.cast_add_one_ne_zero n
  field_simp [hb n, hn, hp]
  <;> ring

private theorem factorial_of_first_order (C K : ℝ) (hC : C ≠ 0)
    (h0 : Tendsto (fun n : ℕ => (f Nat.factorial n n : ℝ) / n.factorial) atTop (𝓝 C))
    (h1 : Tendsto (fun n : ℕ => (n:ℝ) * ((f Nat.factorial n n : ℝ) / n.factorial - C))
      atTop (𝓝 K)) : claimFactorial := by
  have hb (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by positivity
  have ha (n : ℕ) : (f Nat.factorial n n : ℝ) =
      (n.factorial:ℝ) * ((f Nat.factorial n n : ℝ) / n.factorial) := by
    field_simp [hb n]
  have hB : Tendsto (fun n : ℕ => ((n+1).factorial:ℝ) / n.factorial / ((n:ℝ)+1))
      atTop (𝓝 (1:ℝ)) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)) using 1
    ext n
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hp : (n:ℝ)+1 ≠ 0 := by exact Nat.cast_add_one_ne_zero n
    field_simp [hb n, hp]
  have ht := ratio_transfer (fun n => (f Nat.factorial n n:ℝ))
    (fun n => (n.factorial:ℝ)) _ C K 1 hb ha hC h0 h1 hB
  unfold claimFactorial
  convert ht using 1
  ext n
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [mul_div_cancel_right₀ _ (hb n)]


theorem result : D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth.claimFactorial := by
  have hc : 0 < 2 * ∑' k, W k := by linarith [W_tsum_pos]
  exact factorial_of_first_order _ _ hc.ne'
    (tendsto_of_scaled _ _ _ factorial_first_order) factorial_first_order

end D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth
