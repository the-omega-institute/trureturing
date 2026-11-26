/- GID: D5/S3/Quantum/Jacobi/EndpointMomentTruncation
   generality: G
   mirror-B: D5/B/S3/Quantum/Jacobi/EndpointMomentTruncation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic]
   utility: none
   digest: The first possible endpoint moment error at a Jacobi cutoff is the squared coupling product. -/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination

/-! Powers of the half-line Jacobi matrix act locally on the endpoint unit vector. -/

@[expose] public section
namespace D5.S3.Quantum.Jacobi.EndpointMomentTruncation

open Finset
noncomputable section

/-- The `i`-th coordinate of the `k`-th power applied to the endpoint vector.
`some n` keeps sites `0,...,n - 1`, with all other coordinates set to zero. -/
def amplitude (a b : ℕ → ℝ) (cut : Option ℕ) : ℕ → ℕ → ℝ
  | 0, i => if cut.elim true (fun n => decide (i < n)) then (if i = 0 then 1 else 0) else 0
  | k + 1, i => if cut.elim true (fun n => decide (i < n)) then
      (if i = 0 then 0 else b (i - 1)) * amplitude a b cut k (i - 1) +
        a i * amplitude a b cut k i + b i * amplitude a b cut k (i + 1)
    else 0

private theorem outside (a b : ℕ → ℝ) {n i : ℕ} (hi : n ≤ i) (k : ℕ) :
    amplitude a b (some n) k i = 0 := by
  cases k <;> simp [amplitude, Option.elim, Nat.not_lt_of_ge hi]

private theorem support_bound (a b : ℕ → ℝ) (k i : ℕ) (hi : k < i) :
    amplitude a b none k i = 0 := by
  induction k generalizing i with
  | zero => simp [amplitude, Option.elim, Nat.ne_of_gt hi]
  | succ k ih =>
    simp [amplitude, Option.elim, ih (i - 1) (by omega), ih i (by omega), ih (i + 1) (by omega)]

private theorem first_arrival (a b : ℕ → ℝ) (n : ℕ) :
    amplitude a b none n n = ∏ j ∈ range n, b j := by
  induction n with
  | zero => simp [amplitude, Option.elim]
  | succ n ih =>
    simp [amplitude, Option.elim, ih, support_bound a b n (n + 1) (by omega),
      support_bound a b n (n + 1 + 1) (by omega), prod_range_succ, mul_comm]

private theorem before_return (a b : ℕ → ℝ) (n k i : ℕ) (hi : i ≤ n) (ht : k + i < 2 * n) :
    amplitude a b none k i = amplitude a b (some n) k i := by
  induction k generalizing i with
  | zero =>
    by_cases h : i < n
    · simp [amplitude, Option.elim, h]
    · rw [outside a b (by omega)]; exact support_bound a b 0 i (by omega)
  | succ k ih =>
    by_cases h : i < n
    · simp only [amplitude, Option.elim, h, decide_true, ite_true]
      rw [ih (i - 1) (by omega) (by omega), ih i hi (by omega), ih (i + 1) (by omega) (by omega)]
    · rw [outside a b (by omega)]; exact support_bound a b (k + 1) i (by omega)

private theorem returning_front (a b : ℕ → ℝ) (n j i : ℕ) (h : i + j = n) :
    amplitude a b none (n + j) i - amplitude a b (some n) (n + j) i =
      (∏ q ∈ range n, b q) * ∏ q ∈ range j, b (i + q) := by
  induction j generalizing i with
  | zero =>
    have e : i = n := by omega
    subst i
    simp [outside a b (le_refl n), first_arrival]
  | succ j ih =>
    have hi : i < n := by omega
    have prev := before_return a b n (n + j) (i - 1) (by omega) (by omega)
    have mid := before_return a b n (n + j) i (by omega) (by omega)
    have next := ih (i + 1) (by omega)
    rw [show n + (j + 1) = n + j + 1 by omega]
    simp only [amplitude, Option.elim, hi, decide_true, ite_true]
    rw [prev, mid]
    rw [show ∏ q ∈ range (j + 1), b (i + q) = (∏ q ∈ range j, b (i + 1 + q)) * b i by
      rw [prod_range_succ', Nat.add_zero]
      congr 1
      apply prod_congr rfl
      intro x _
      congr 1
      omega]
    linear_combination b i * next

/-- Endpoint moments agree through order `2 * n - 1`. At order `2 * n` the full moment
minus the truncated moment equals the product of the first `n` squared couplings. -/
theorem first_omitted_moment (a b : ℕ → ℝ) (n : ℕ) :
    (∀ k < 2 * n, amplitude a b none k 0 = amplitude a b (some n) k 0) ∧
    amplitude a b none (2 * n) 0 - amplitude a b (some n) (2 * n) 0 =
      ∏ j ∈ range n, (b j) ^ 2 := by
  constructor
  · intro k hk
    exact before_return a b n k 0 (by omega) (by omega)
  · simpa [two_mul, pow_two, prod_mul_distrib] using returning_front a b n n 0 (by omega)

end
end D5.S3.Quantum.Jacobi.EndpointMomentTruncation
