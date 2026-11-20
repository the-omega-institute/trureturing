/- GID: D5/S1/Recurrence/Algebraic/ChenChenRealStepRowSums
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/ChenChenRealStepRowSums
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: For real m, step-m Eulerian rows sum to ∏(mj+2); even rows have equal parity sums. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#5)
escape_witness: row_sum (padding the previous row by zero, the recursion holds at every
  position of a row n ≥ 2 by padded_rec, and each entry of row n - 1 then receives total
  coefficient (m(n-1-j)+1) + (m(j-1)+1) = m(n-2)+2, so S(n) = (m(n-2)+2) S(n-1)) and
  alternating_zero (for even n the reflection k ↦ n+1-k pairs entries of opposite parity,
  so the alternating row sum equals its own negative).
proof_shape:
  Source, claim: source definitions; consumers: the theorems below.
  P: private definition (zero padding); consumers: padded_rec, sum_eq_range, row_sum.
  padded_rec: content (the boundary values agree with the recursion under zero padding);
    consumer: row_sum.
  sum_eq_range: bind-only helper (reindexing Icc 1 n to range n); consumer: row_sum.
  row_sum: content; consumer: result.
  reflection: content (T n k = T n (n+1-k) by strong induction on rows); consumer:
    alternating_zero.
  alternating_zero: content; consumer: result.
  result: content only through row_sum and alternating_zero; the parity sums follow from
    the split of the row into odd and even positions by linear arithmetic.
Direct frozen dependencies: none (Mathlib-only imports).
Search record (§3.1): D5/S1/Recurrence/Algebraic/ChenChenParityPositivity treats integer
  steps over ℤ and proves even-row positivity; its private reflection lemma is stated for
  Source (m : ℤ) (T : ℕ → ℕ → ℤ) and cannot be applied to a real step, and no D5
  declaration states the row-sum product, the even-row cancellation or the parity sums.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Row sums and parity sums of the real-step Eulerian triangle

Chen and Chen's step-`m` Eulerian triangle has `T(n,1) = T(n,n) = 1` and, for `1 < k < n`,
`T(n,k) = (m(n-k)+1) T(n-1,k-1) + (m(k-1)+1) T(n-1,k)`. For every real `m` and every
function satisfying these rules, the `n`-th row sums to `∏_{j=0}^{n-2} (mj+2)`. In an even row
the alternating sum `∑ (-1)^(k-1) T(n,k)` vanishes, so the entries at odd and at even positions
each sum to half the row sum.
-/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.ChenChenRealStepRowSums

/-- The boundary and interior recursion of the step-`m` Eulerian triangle, for real `m`.
Values outside the triangle, including row zero, are unconstrained. -/
def Source (m : ℝ) (T : ℕ → ℕ → ℝ) : Prop :=
  (∀ n, 1 ≤ n → T n 1 = 1 ∧ T n n = 1) ∧
  ∀ n k, 1 < k → k < n →
    T n k = (m * ((n : ℝ) - (k : ℝ)) + 1) * T (n - 1) (k - 1) +
      (m * ((k : ℝ) - 1) + 1) * T (n - 1) k

/-- Row sums, even-row alternating sums and even-row parity sums, for every real step and
every function satisfying the recursion. -/
def claim : Prop :=
  ∀ (m : ℝ) (T : ℕ → ℕ → ℝ), Source m T →
    (∀ n, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, T n k = ∏ j ∈ Finset.range (n - 1), (m * j + 2)) ∧
    (∀ n, 1 ≤ n → Even n →
      ∑ k ∈ Finset.Icc 1 n, T n k * (-1) ^ (k - 1) = 0 ∧
      ∑ k ∈ (Finset.Icc 1 n).filter Odd, T n k =
        (1 / 2) * ∑ k ∈ Finset.Icc 1 n, T n k ∧
      ∑ k ∈ (Finset.Icc 1 n).filter Even, T n k =
        (1 / 2) * ∑ k ∈ Finset.Icc 1 n, T n k)

/-- The triangle padded by zero outside `1 ≤ k ≤ n`. -/
private noncomputable def P (T : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  if 1 ≤ k ∧ k ≤ n then T n k else 0

/-- The padded triangle satisfies the recursion at every `k ≥ 1` in rows `n ≥ 2`. -/
private theorem padded_rec {m : ℝ} {T : ℕ → ℕ → ℝ} (h : Source m T) {n k : ℕ} (hn : 2 ≤ n)
    (hk : 1 ≤ k) :
    P T n k = (m * ((n : ℝ) - (k : ℝ)) + 1) * P T (n - 1) (k - 1) +
      (m * ((k : ℝ) - 1) + 1) * P T (n - 1) k := by
  unfold P
  by_cases h1 : k = 1
  · subst h1
    simp [(h.1 n (by omega)).1, (h.1 (n - 1) (by omega)).1, show 1 ≤ n by omega,
      show 1 ≤ n - 1 by omega]
  by_cases hn' : k = n
  · subst hn'
    have := (h.1 (k - 1) (by omega)).2
    simp [(h.1 k (by omega)).2, this, show ¬ k ≤ k - 1 by omega, show 1 ≤ k - 1 by omega,
      show k ≠ 0 by omega]
  by_cases hkn : k < n
  · simp only [hk, hkn.le, show 1 ≤ k - 1 by omega, show k - 1 ≤ n - 1 by omega,
      show k ≤ n - 1 by omega, and_self, ite_true]
    exact h.2 n k (by omega) hkn
  · simp only [show ¬ k ≤ n by omega, show ¬ k - 1 ≤ n - 1 by omega, show ¬ k ≤ n - 1 by omega,
      and_false, ite_false]
    ring

private theorem sum_eq_range (T : ℕ → ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, T n k = ∑ i ∈ Finset.range n, P T n (i + 1) := by
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) from rfl, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  simp [P, add_comm 1 i, show i + 1 ≤ n by omega]

private theorem row_sum {m : ℝ} {T : ℕ → ℕ → ℝ} (h : Source m T) :
    ∀ n, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, T n k = ∏ j ∈ Finset.range (n - 1), (m * j + 2) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [(h.1 1 le_rfl).1]
    have ihn := ih hpos
    rw [sum_eq_range] at ihn ⊢
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, Finset.prod_range_succ, ← ihn]
    have hrec : ∀ i ∈ Finset.range (n + 1), P T (n + 1) (i + 1) =
        (m * ((n : ℝ) - i) + 1) * P T n i + (m * (i : ℝ) + 1) * P T n (i + 1) := by
      intro i _
      rw [padded_rec h (by omega) (by omega)]
      push_cast
      ring
    rw [Finset.sum_congr rfl hrec, Finset.sum_add_distrib, Finset.sum_range_succ',
      Finset.sum_range_succ]
    have h0 : P T n 0 = 0 := by simp [P]
    have hn1 : P T n (n + 1) = 0 := by simp [P]
    rw [h0, hn1]
    simp only [mul_zero, add_zero]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring

private theorem reflection {m : ℝ} {T : ℕ → ℕ → ℝ} (h : Source m T)
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    T n k = T n (n + 1 - k) := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases hl : k = 1
    · subst k
      simpa using (h.1 n hn).1.trans (h.1 n hn).2.symm
    by_cases hr : k = n
    · subst k
      simpa using (h.1 n hn).2.trans (h.1 n hn).1.symm
    have hn' : 1 ≤ n - 1 := by omega
    have e₁ := ih (n - 1) (by omega) (k - 1) hn' (by omega) (by omega)
    have e₂ := ih (n - 1) (by omega) k hn' hk (by omega)
    have i₁ : n - 1 + 1 - (k - 1) = n + 1 - k := by omega
    have i₂ : n - 1 + 1 - k = n + 1 - k - 1 := by omega
    rw [i₁] at e₁
    rw [i₂] at e₂
    rw [h.2 n k (by omega) (by omega),
      h.2 n (n + 1 - k) (by omega) (by omega), ← e₁, ← e₂]
    have hc : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - (k : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc]
    ring

private theorem alternating_zero {m : ℝ} {T : ℕ → ℕ → ℝ} (h : Source m T) {n : ℕ}
    (hn : 1 ≤ n) (he : Even n) :
    ∑ k ∈ Finset.Icc 1 n, T n k * (-1) ^ (k - 1) = 0 := by
  have hrefl : ∑ k ∈ Finset.Icc 1 n, T n k * (-1) ^ (k - 1) =
      ∑ k ∈ Finset.Icc 1 n, T n (n + 1 - k) * (-1) ^ (n + 1 - k - 1) := by
    refine Finset.sum_nbij' (fun k => n + 1 - k) (fun k => n + 1 - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      rw [show n + 1 - (n + 1 - k) = k by omega]
  have hneg : ∑ k ∈ Finset.Icc 1 n, T n (n + 1 - k) * (-1) ^ (n + 1 - k - 1) =
      -∑ k ∈ Finset.Icc 1 n, T n k * (-1) ^ (k - 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    rw [← reflection h n k hn hk.1 hk.2]
    obtain ⟨r, hr⟩ := he
    have hsum : n + 1 - k - 1 + (k - 1) + 1 = 2 * r := by omega
    have h2 : (-1 : ℝ) ^ (n + 1 - k - 1 + (k - 1) + 1) = 1 := by
      rw [hsum, pow_mul]; norm_num
    rw [pow_add, pow_add, pow_one, mul_neg_one] at h2
    have hX : (-1 : ℝ) ^ (n + 1 - k - 1) * (-1) ^ (k - 1) = -1 := by linarith
    have hs : (-1 : ℝ) ^ (k - 1) * (-1) ^ (k - 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have hpar : (-1 : ℝ) ^ (n + 1 - k - 1) = -(-1) ^ (k - 1) := by
      calc (-1 : ℝ) ^ (n + 1 - k - 1)
          = (-1) ^ (n + 1 - k - 1) * ((-1) ^ (k - 1) * (-1) ^ (k - 1)) := by rw [hs, mul_one]
        _ = ((-1) ^ (n + 1 - k - 1) * (-1) ^ (k - 1)) * (-1) ^ (k - 1) := by ring
        _ = -(-1) ^ (k - 1) := by rw [hX]; ring
    rw [hpar]; ring
  linarith

/-- The row-sum and parity identities hold. -/
theorem result : claim := by
  intro m T h
  refine ⟨row_sum h, fun n hn he => ?_⟩
  have hR := alternating_zero h hn he
  have hsplit : ∑ k ∈ Finset.Icc 1 n, T n k * (-1) ^ (k - 1) =
      ∑ k ∈ (Finset.Icc 1 n).filter Odd, T n k - ∑ k ∈ (Finset.Icc 1 n).filter Even, T n k := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) Odd]
    have hne : (Finset.Icc 1 n).filter (fun k => ¬ Odd k) = (Finset.Icc 1 n).filter Even := by
      ext k; simp [Nat.not_odd_iff_even]
    rw [hne]
    have ho : ∀ k ∈ (Finset.Icc 1 n).filter Odd, T n k * (-1) ^ (k - 1) = T n k := by
      intro k hk
      obtain ⟨_, ⟨r, rfl⟩⟩ := Finset.mem_filter.mp hk
      simp [pow_mul]
    have hev : ∀ k ∈ (Finset.Icc 1 n).filter Even, T n k * (-1) ^ (k - 1) = -T n k := by
      intro k hk
      obtain ⟨hk1, ⟨r, rfl⟩⟩ := Finset.mem_filter.mp hk
      simp only [Finset.mem_Icc] at hk1
      rw [show r + r - 1 = 2 * (r - 1) + 1 by omega, pow_succ, pow_mul]
      norm_num
    rw [Finset.sum_congr rfl ho, Finset.sum_congr rfl hev, Finset.sum_neg_distrib]
    ring
  have htot : ∑ k ∈ Finset.Icc 1 n, T n k =
      ∑ k ∈ (Finset.Icc 1 n).filter Odd, T n k + ∑ k ∈ (Finset.Icc 1 n).filter Even, T n k := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) Odd]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k; simp [Nat.not_odd_iff_even]
  refine ⟨hR, ?_, ?_⟩ <;> linarith


end D5.S1.Recurrence.Algebraic.ChenChenRealStepRowSums
