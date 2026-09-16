/- GID: D5/S3/Analytic/NestedGridEntropy
   generality: G
   mirror-B: D5/B/S3/Analytic/NestedGridEntropy
   mirror-E: none(waiver:unbounded-refinement-history)
   anchors: []
   utility: none
   digest: Actual binary refinement histories obey a finite entropy budget with explicit nonmaximal-split and split-imbalance losses. -/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

/-!
# An entropy obstruction for nested grid histories

The data are lists of actual positive cell lengths. Each operation replaces
one length a+b by a and b; cells already separated are never merged or moved.
The proof derives positivity and total length from that history, telescopes
its Shannon entropy, and compares the final entropy with a maximal-cell cap.
No entropy growth law or terminal entropy certificate is a hypothesis.

The classical low-dispersion sequence of Niederreiter (1984), discussed with
its exact gap structure by Weiss, arXiv:2304.14202v3, provides the matching
ordinary construction. Its identification with the two-moment grid loss and
the sharp sequential constant are in the existing NS observer theory. This
file proves the finite history inequality, not the full asymptotic theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.NestedGridEntropy

open scoped BigOperators

/-- Any actual sequence of binary cell splits pays for its final resolution
with the entire past maximal-cell budget. The explicit nonnegative loss records
both splitting a cell smaller than the cap and departing from a balanced split.
The zero-step case is included. -/
theorem binary_refinement_entropy_budget
    (cells before after : ℕ → List ℝ) (a b cap : ℕ → ℝ)
    (initial : cells 0 = [1])
    (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (step : ∀ k,
      cells k = before k ++ (a k + b k) :: after k ∧
      cells (k + 1) = before k ++ a k :: b k :: after k)
    (hcap : ∀ k, ∀ x ∈ cells k, x ≤ cap k) :
    let loss : ℕ → ℝ := fun k =>
      (cap k - (a k + b k)) * Real.log 2 +
      (a k + b k) * (Real.log 2 - Real.binEntropy (a k / (a k + b k)))
    (∀ k, 0 ≤ loss k) ∧
      ∀ n : ℕ, Real.log (1 / cap n) + (∑ k ∈ Finset.range n, loss k) ≤
        Real.log 2 * (∑ k ∈ Finset.range n, cap k) := by
  let loss : ℕ → ℝ := fun k =>
    (cap k - (a k + b k)) * Real.log 2 +
    (a k + b k) * (Real.log 2 - Real.binEntropy (a k / (a k + b k)))
  let H : List ℝ → ℝ := fun xs => (xs.map Real.negMulLog).sum
  change (∀ k, 0 ≤ loss k) ∧ ∀ n : ℕ,
    Real.log (1 / cap n) + (∑ k ∈ Finset.range n, loss k) ≤
      Real.log 2 * (∑ k ∈ Finset.range n, cap k)
  have log2_nonneg : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have invariant : ∀ k, (∀ x ∈ cells k, 0 < x) ∧ (cells k).sum = 1 := by
    intro k
    induction k with
    | zero => simp [initial]
    | succ k ih =>
        obtain ⟨old, new⟩ := step k
        constructor
        · intro x hx
          rw [new] at hx
          rcases List.mem_append.mp hx with hp | hr
          · apply ih.1 x
            rw [old]
            exact List.mem_append.mpr (Or.inl hp)
          · rcases List.mem_cons.mp hr with rfl | hr
            · exact ha k
            · rcases List.mem_cons.mp hr with rfl | hr
              · exact hb k
              · apply ih.1 x
                rw [old]
                exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hr)))
        · have hsum := ih.2
          rw [old] at hsum
          rw [new]
          simpa only [List.sum_append, List.sum_cons, add_assoc] using hsum
  have chain (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
      Real.negMulLog x + Real.negMulLog y - Real.negMulLog (x + y) =
        (x + y) * Real.binEntropy (x / (x + y)) := by
    have hs : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
    have hcomp : 1 - x / (x + y) = y / (x + y) := by
      field_simp [hs] <;> ring
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hcomp]
    simp only [Real.negMulLog, Real.log_div (ne_of_gt hx) hs,
      Real.log_div (ne_of_gt hy) hs]
    field_simp [hs] <;> ring
  have increment (k : ℕ) : H (cells (k + 1)) = H (cells k) +
      (a k + b k) * Real.binEntropy (a k / (a k + b k)) := by
    obtain ⟨old, new⟩ := step k
    have h := chain (a k) (b k) (ha k) (hb k)
    simp only [H, old, new, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons]
    linarith
  have loss_nonneg (k : ℕ) : 0 ≤ loss k := by
    have hp : a k + b k ≤ cap k := by
      apply hcap k
      rw [(step k).1]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hp) log2_nonneg)
      (mul_nonneg (add_pos (ha k) (hb k)).le
        (sub_nonneg.mpr Real.binEntropy_le_log_two))
  have account : ∀ n : ℕ,
      H (cells n) + (∑ k ∈ Finset.range n, loss k) =
        Real.log 2 * (∑ k ∈ Finset.range n, cap k) := by
    intro n
    induction n with
    | zero => simp [initial, H, Real.negMulLog]
    | succ n ih =>
        rw [increment]
        simp only [Finset.sum_range_succ]
        have hstep : (a n + b n) * Real.binEntropy (a n / (a n + b n)) +
            loss n = cap n * Real.log 2 := by
          dsimp [loss]
          ring
        nlinarith
  have entropy_lower (xs : List ℝ) (d : ℝ) :
      (∀ x ∈ xs, 0 < x) → (∀ x ∈ xs, x ≤ d) →
        -xs.sum * Real.log d ≤ H xs := by
    induction xs with
    | nil => intro hx hd; simp [H]
    | cons x xs ih =>
        intro hx hd
        have hx0 := hx x (by simp)
        have hxd := hd x (by simp)
        have hlog := Real.log_le_log hx0 hxd
        have hxterm : -x * Real.log d ≤ Real.negMulLog x := by
          have h := mul_le_mul_of_nonneg_left hlog hx0.le
          unfold Real.negMulLog
          nlinarith
        have hrest := ih (fun z hz => hx z (by simp [hz]))
          (fun z hz => hd z (by simp [hz]))
        simp only [H, List.sum_cons, List.map_cons] at *
        linarith
  refine ⟨loss_nonneg, ?_⟩
  intro n
  have hlower := entropy_lower (cells n) (cap n) (invariant n).1 (hcap n)
  have hlower' : Real.log (1 / cap n) ≤ H (cells n) := by
    simpa only [(invariant n).2, neg_mul, one_mul, one_div, Real.log_inv] using hlower
  calc
    Real.log (1 / cap n) + (∑ k ∈ Finset.range n, loss k) ≤
        H (cells n) + (∑ k ∈ Finset.range n, loss k) :=
      add_le_add_right hlower' _
    _ = Real.log 2 * (∑ k ∈ Finset.range n, cap k) := account n

#print axioms binary_refinement_entropy_budget

end D5.S3.Analytic.NestedGridEntropy
