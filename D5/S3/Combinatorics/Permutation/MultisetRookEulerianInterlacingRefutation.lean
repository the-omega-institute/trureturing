/- GID: D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.claim; result=D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.result; claim=D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.claim
   digest: Multiset rook-Eulerian interlacing fails on a six-row Ferrers board. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#12894; Refuted)
Direct frozen dependencies: none; pinned Mathlib permutation, polynomial roots and sorting.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation

open Polynomial

/-- The rearrangements of the content, with every letter in its permitted row. -/
def W {n k : ℕ} (lam : Fin n → ℕ) (α : Fin k → ℕ) : Finset (List ℕ) :=
  (((List.finRange k).flatMap
    (fun c => List.replicate (α c) (c.val + 1))).permutations'.toFinset).filter
    (fun w => ∀ i : Fin n, 0 < w.getD i.val 0 ∧ w.getD i.val 0 ≤ lam i)

/-- Adjacent strict ascents, with the final position excluded. -/
def asc (w : List ℕ) : ℕ :=
  ((Finset.range (w.length - 1)).filter (fun i => w.getD i 0 < w.getD (i + 1) 0)).card

/-- The full multiset rook-Eulerian polynomial, equation (10). -/
noncomputable def R {n k : ℕ} (lam : Fin n → ℕ) (α : Fin k → ℕ) : ℝ[X] :=
  ∑ w ∈ W lam α, X ^ asc w

/-- The first-letter refinement, equation (11). -/
noncomputable def Rj {n k : ℕ} (lam : Fin n → ℕ) (α : Fin k → ℕ) (j : ℕ) : ℝ[X] :=
  ∑ w ∈ (W lam α).filter (fun w => w.getD 0 0 = j), X ^ asc w

/-- Definition 8, using decreasing lists of roots, with multiplicity.
    Polynomial.Splits is the existing real-rootedness predicate. -/
noncomputable def Interlaces (f g : ℝ[X]) : Prop :=
  0 < f.leadingCoeff ∧ 0 < g.leadingCoeff ∧ f.Splits ∧ g.Splits ∧
    (∀ x ∈ f.roots, x ≤ 0) ∧ (∀ x ∈ g.roots, x ≤ 0) ∧
    (g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1) ∧
    ∀ i : ℕ, i < f.roots.card →
      (f.roots.sort (· ≥ ·)).getD i 0 ≤ (g.roots.sort (· ≥ ·)).getD i 0 ∧
      (i + 1 < g.roots.card →
        (g.roots.sort (· ≥ ·)).getD (i + 1) 0 ≤ (f.roots.sort (· ≥ ·)).getD i 0)

/-- Both clauses of Conjecture 28, for every positive size, board and content. -/
noncomputable def claim : Prop :=
  ∀ (n k : ℕ) (lam : Fin n → ℕ) (α : Fin k → ℕ) (hn : 0 < n),
    Monotone lam → (∑ c, α c) = n →
      (R lam α).Splits ∧
      ∀ p q : ℕ, 1 ≤ q → q < p → p ≤ lam ⟨0, hn⟩ →
        Rj lam α p ≠ 0 → Rj lam α q ≠ 0 → Interlaces (Rj lam α p) (Rj lam α q)

set_option maxHeartbeats 2000000 in
-- The local budget covers reduction of the sixty-word certificate and its ascent sums.
/-- The interlacing clause fails for board 333344 and content (2,2,1,1). -/
theorem result : ¬ claim := by
  let board : Fin 6 → ℕ := ![3, 3, 3, 3, 4, 4]
  let content : Fin 4 → ℕ := ![2, 2, 1, 1]
  let certificate : Finset (List ℕ) := [
    [1, 1, 2, 2, 3, 4],
    [1, 1, 2, 2, 4, 3],
    [1, 1, 2, 3, 2, 4],
    [1, 1, 2, 3, 4, 2],
    [1, 1, 3, 2, 2, 4],
    [1, 1, 3, 2, 4, 2],
    [1, 2, 1, 2, 3, 4],
    [1, 2, 1, 2, 4, 3],
    [1, 2, 1, 3, 2, 4],
    [1, 2, 1, 3, 4, 2],
    [1, 2, 2, 1, 3, 4],
    [1, 2, 2, 1, 4, 3],
    [1, 2, 2, 3, 1, 4],
    [1, 2, 2, 3, 4, 1],
    [1, 2, 3, 1, 2, 4],
    [1, 2, 3, 1, 4, 2],
    [1, 2, 3, 2, 1, 4],
    [1, 2, 3, 2, 4, 1],
    [1, 3, 1, 2, 2, 4],
    [1, 3, 1, 2, 4, 2],
    [1, 3, 2, 1, 2, 4],
    [1, 3, 2, 1, 4, 2],
    [1, 3, 2, 2, 1, 4],
    [1, 3, 2, 2, 4, 1],
    [2, 1, 1, 2, 3, 4],
    [2, 1, 1, 2, 4, 3],
    [2, 1, 1, 3, 2, 4],
    [2, 1, 1, 3, 4, 2],
    [2, 1, 2, 1, 3, 4],
    [2, 1, 2, 1, 4, 3],
    [2, 1, 2, 3, 1, 4],
    [2, 1, 2, 3, 4, 1],
    [2, 1, 3, 1, 2, 4],
    [2, 1, 3, 1, 4, 2],
    [2, 1, 3, 2, 1, 4],
    [2, 1, 3, 2, 4, 1],
    [2, 2, 1, 1, 3, 4],
    [2, 2, 1, 1, 4, 3],
    [2, 2, 1, 3, 1, 4],
    [2, 2, 1, 3, 4, 1],
    [2, 2, 3, 1, 1, 4],
    [2, 2, 3, 1, 4, 1],
    [2, 3, 1, 1, 2, 4],
    [2, 3, 1, 1, 4, 2],
    [2, 3, 1, 2, 1, 4],
    [2, 3, 1, 2, 4, 1],
    [2, 3, 2, 1, 1, 4],
    [2, 3, 2, 1, 4, 1],
    [3, 1, 1, 2, 2, 4],
    [3, 1, 1, 2, 4, 2],
    [3, 1, 2, 1, 2, 4],
    [3, 1, 2, 1, 4, 2],
    [3, 1, 2, 2, 1, 4],
    [3, 1, 2, 2, 4, 1],
    [3, 2, 1, 1, 2, 4],
    [3, 2, 1, 1, 4, 2],
    [3, 2, 1, 2, 1, 4],
    [3, 2, 1, 2, 4, 1],
    [3, 2, 2, 1, 1, 4],
    [3, 2, 2, 1, 4, 1]].toFinset
  have hw : W board content = certificate := by
    decide +kernel
  classical
  have h1 : Rj board content 1 = 2 * X ^ 4 + 15 * X ^ 3 + 7 * X ^ 2 := by
    rw [Rj, hw]
    norm_num [certificate, asc, List.getD, Finset.range_add_one, Finset.filter_insert,
      Finset.filter_singleton, Finset.sum_filter, Finset.sum_insert, Finset.sum_singleton]
    ring
  have h3 : Rj board content 3 = X ^ 3 + 8 * X ^ 2 + 3 * X := by
    rw [Rj, hw]
    norm_num [certificate, asc, List.getD, Finset.range_add_one, Finset.filter_insert,
      Finset.filter_singleton, Finset.sum_filter, Finset.sum_insert, Finset.sum_singleton]
    ring
  have hm : Monotone board := by decide
  have hc : (∑ c, content c) = 6 := by decide
  intro h
  have hi := (h 6 4 board content (by decide) hm hc).2 3 1
  have hn1 : Rj board content 1 ≠ 0 := by
    intro hz
    have := congrArg (fun p : ℝ[X] => p.coeff 4) hz
    rw [h1] at this
    norm_num [coeff_X] at this
  have hn3 : Rj board content 3 ≠ 0 := by
    intro hz
    have := congrArg (fun p : ℝ[X] => p.coeff 3) hz
    rw [h3] at this
    norm_num [coeff_X] at this
  have hh := hi (by decide) (by decide) (by decide) hn3 hn1
  rw [h1, h3] at hh
  clear h hi hn1 hn3 hc hm h1 h3 hw certificate board content
  have hs : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 13 := Real.sqrt_nonneg _
  have hs3 : 3 < Real.sqrt 13 := by nlinarith
  have hs4 : Real.sqrt 13 < 4 := by nlinarith
  have hf : (X ^ 3 + 8 * X ^ 2 + 3 * X : ℝ[X]) =
      X * (X - C (-4 + Real.sqrt 13)) * (X - C (-4 - Real.sqrt 13)) := by
    have hcs : C (Real.sqrt 13) ^ 2 = (13 : ℝ[X]) := by
      rw [← map_pow, hs, C_ofNat]
    simp only [C_sub, C_add, C_neg, C_ofNat]
    linear_combination X * hcs
  have hg : (2 * X ^ 4 + 15 * X ^ 3 + 7 * X ^ 2 : ℝ[X]) =
      C 2 * X * X * (X - C (-(1 / 2))) * (X - C (-7)) := by
    have hhalf : (2 : ℝ[X]) * C (1 / 2) = 1 := by
      rw [← C_ofNat 2, ← C_mul]
      norm_num
    simp only [C_neg, C_ofNat]
    linear_combination -(X ^ 3 + 7 * X ^ 2) * hhalf
  have hr3 : (X ^ 3 + 8 * X ^ 2 + 3 * X : ℝ[X]).roots =
      (0 ::ₘ (-4 + Real.sqrt 13) ::ₘ (-4 - Real.sqrt 13) ::ₘ 0) := by
    rw [hf, roots_mul (mul_ne_zero (mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)),
      roots_mul (mul_ne_zero X_ne_zero (X_sub_C_ne_zero _))]
    simp only [roots_X, roots_X_sub_C, Multiset.singleton_add, Multiset.cons_add,
      Multiset.cons_zero]
  have hr1 : (2 * X ^ 4 + 15 * X ^ 3 + 7 * X ^ 2 : ℝ[X]).roots =
      (0 ::ₘ 0 ::ₘ (-(1 / 2)) ::ₘ (-7) ::ₘ 0) := by
    have hc2 : (C 2 : ℝ[X]) ≠ 0 := by simp
    rw [hg, roots_mul (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hc2 X_ne_zero) X_ne_zero)
        (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)),
      roots_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hc2 X_ne_zero) X_ne_zero)
        (X_sub_C_ne_zero _)),
      roots_mul (mul_ne_zero (mul_ne_zero hc2 X_ne_zero) X_ne_zero), roots_C_mul _ (by norm_num)]
    simp only [roots_X, roots_X_sub_C, Multiset.singleton_add, Multiset.cons_add,
      Multiset.cons_zero]
  have ha : (0 ::ₘ (-4 + Real.sqrt 13) ::ₘ (-4 - Real.sqrt 13) ::ₘ (0 : Multiset ℝ)).sort (· ≥ ·) =
      [0, -4 + Real.sqrt 13, -4 - Real.sqrt 13] := by
    rw [Multiset.sort_cons, Multiset.sort_cons, Multiset.sort_cons, Multiset.sort_zero]
    all_goals intro x hx
    all_goals simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    all_goals rcases hx with rfl | rfl <;> nlinarith
  have hb : (0 ::ₘ 0 ::ₘ (-(1 / 2)) ::ₘ (-7) ::ₘ (0 : Multiset ℝ)).sort (· ≥ ·) =
      [0, 0, -1 / 2, -7] := by
    norm_num [Multiset.sort_cons]
  have hchain := hh.2.2.2.2.2.2.2 2
  rw [hr3, hr1] at hchain
  have hbad := (hchain (by simp)).2 (by simp)
  rw [ha, hb] at hbad
  norm_num at hbad
  nlinarith

#print axioms result

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation
