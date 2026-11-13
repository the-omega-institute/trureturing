/- GID: D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Kurkov's full A102086 row identity, including both source tables. -/

/-
result:
  proof_shape: content (operator shift and row induction remain after helper inlining).
  escape_witness: shift_table, on the live path through row_step and coefficientTriangle_source.
  admission_basis: open-problem-resolution (#23496; full nonvacuous event).
Direct frozen D5 dependencies: none. Pinned Mathlib supplies the polynomial and linear-map APIs.

Private theorem proof shapes and live consumers:
  naturalP_zero: bind-only; naturalP_diag, polynomialTable_source.
  naturalP_diag: bind-only; polynomialTable_source.
  naturalP_above: bind-only; polynomialTable_source.
  naturalP_step: bind-only; polynomialTable_source.
  polynomialTable_source: bind-only; result.
  polynomial_unique: content (triangular-domain induction); result.
  coeff_above: content (row and column induction); row_expand, coefficientTriangle_source.
  shift_monomial: bind-only; shift_table.
  shift_table: content (operator-shift induction); row_step.
  row_expand: content after inlining coeff_above; row_step, result.
  row_step: content after inlining shift_table and row_expand; coefficientTriangle_source.
  coefficientTriangle_source: content (coefficient bounds and operator shift); result.
  triangle_unique: content (strong row induction); result.
The bind-only helpers organize live proofs and supply no independent novelty credit.
The definitions are symbolic source tables, not bounded enumeration, certificates,
checker algorithms or computational reductions; utility none applies to every declaration.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

/-! The complete polynomial-table and matrix-square identity of OEIS A102086. -/

namespace D5.S1.Recurrence.Algebraic.KurkovA102086RowPolynomial

noncomputable section

open Polynomial
open scoped BigOperators

/-- The lower triangular matrix in the NAME of OEIS A102086. -/
def IsSourceTriangle (T : ℕ → ℕ → ℤ) : Prop :=
  (∀ n k, n < k → T n k = 0) ∧
  (∀ n, T n n = (n : ℤ) + 1) ∧
  (∀ n k, k < n → T n k = ∑ j ∈ Finset.Ico k n, T (n - 1) j * T j k)

/-- The FORMULA table, including its integer exterior indices. -/
def IsSourcePolynomialTable (P : ℕ → ℤ → Polynomial ℤ) : Prop :=
  (∀ n, P n (n : ℤ) = X ^ n) ∧
  (∀ n, P n 0 = 1) ∧
  (∀ (n : ℕ) (k : ℤ), k < 0 ∨ (n : ℤ) < k → P n k = 0) ∧
  (∀ (n : ℕ) (k : ℤ), 0 < k → k < (n : ℤ) →
    P n k = P n (k - 1) + C (k + 1) * P (n - 1) k)

/-- Both source tables exist, and the conjecture holds for every such pair, at every row. -/
def claim : Prop :=
  (∃ T, IsSourceTriangle T) ∧
  (∃ P, IsSourcePolynomialTable P) ∧
  ∀ (T : ℕ → ℕ → ℤ) (P : ℕ → ℤ → Polynomial ℤ),
    IsSourceTriangle T → IsSourcePolynomialTable P → ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1), C (T n k) * X ^ k) = P (n + 1) (n : ℤ)

private def naturalP (a b : ℕ) : Polynomial ℤ :=
  if b = 0 then 1 else if b = a then X ^ a else if a < b then 0 else
    naturalP a (b - 1) + C ((b : ℤ) + 1) * naturalP (a - 1) b
termination_by a + b
decreasing_by all_goals omega

private theorem naturalP_zero (a : ℕ) : naturalP a 0 = 1 := by
  rw [naturalP]; simp

private theorem naturalP_diag (a : ℕ) : naturalP a a = X ^ a := by
  by_cases ha : a = 0
  · subst a; simp [naturalP_zero]
  · rw [naturalP, ite_eq_right ha, ite_eq_left rfl]

private theorem naturalP_above (a b : ℕ) (h : a < b) : naturalP a b = 0 := by
  rw [naturalP, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]

private theorem naturalP_step (a b : ℕ) (h0 : 0 < b) (h : b < a) :
    naturalP a b = naturalP a (b - 1) + C ((b : ℤ) + 1) * naturalP (a - 1) b := by
  rw [naturalP, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- An independently constructed source table; no matrix coefficients enter its definition. -/
private def polynomialTable (a : ℕ) (b : ℤ) : Polynomial ℤ :=
  if b < 0 then 0 else naturalP a b.toNat

private theorem polynomialTable_source : IsSourcePolynomialTable polynomialTable := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a; simp [polynomialTable, naturalP_diag]
  · intro a; simp [polynomialTable, naturalP_zero]
  · intro a b hb
    rcases hb with hb | hb
    · simp [polynomialTable, hb]
    · by_cases hneg : b < 0
      · simp [polynomialTable, hneg]
      · simp only [polynomialTable, ite_eq_right hneg]
        exact naturalP_above a b.toNat (by omega)
  · intro a b h0 hba
    have hcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (by omega)
    have hsub : (b - 1).toNat = b.toNat - 1 := by omega
    simp only [polynomialTable, ite_eq_right (show ¬ b < 0 by omega),
      ite_eq_right (show ¬ b - 1 < 0 by omega), hsub]
    rw [naturalP_step a b.toNat (by omega) (by omega), hcast]

private theorem polynomial_unique {P Q : ℕ → ℤ → Polynomial ℤ}
    (hP : IsSourcePolynomialTable P) (hQ : IsSourcePolynomialTable Q) : P = Q := by
  have hn : ∀ a b : ℕ, b ≤ a → P a b = Q a b := by
    intro a
    induction a with
    | zero =>
      intro b hb; have : b = 0 := by omega
      subst b; simpa using (hP.2.1 0).trans (hQ.2.1 0).symm
    | succ a ih =>
      intro b
      induction b with
      | zero => intro _; simpa using (hP.2.1 (a + 1)).trans (hQ.2.1 (a + 1)).symm
      | succ b ihb =>
        intro hb
        by_cases hd : b + 1 = a + 1
        · rw [hd]; exact (hP.1 (a + 1)).trans (hQ.1 (a + 1)).symm
        · rw [hP.2.2.2 (a + 1) ((b + 1 : ℕ) : ℤ) (by omega) (by omega),
            hQ.2.2.2 (a + 1) ((b + 1 : ℕ) : ℤ) (by omega) (by omega)]
          simpa using congrArg₂ (fun p q : Polynomial ℤ => p + C ((b : ℤ) + 1 + 1) * q)
            (ihb (by omega)) (ih (b + 1) (by omega))
  funext a b
  by_cases h0 : b < 0
  · exact (hP.2.2.1 a b (Or.inl h0)).trans (hQ.2.2.1 a b (Or.inl h0)).symm
  by_cases ha : (a : ℤ) < b
  · exact (hP.2.2.1 a b (Or.inr ha)).trans (hQ.2.2.1 a b (Or.inr ha)).symm
  simpa [Int.toNat_of_nonneg (by omega : 0 ≤ b)] using hn a b.toNat (by omega)

private theorem coeff_above {P : ℕ → ℤ → Polynomial ℤ}
    (hP : IsSourcePolynomialTable P) (a b k : ℕ) (hba : b ≤ a) (hk : b < k) :
    (P a (b : ℤ)).coeff k = 0 := by
  induction a generalizing b k with
  | zero =>
    have : b = 0 := by omega
    subst b; rw [Nat.cast_zero, hP.2.1]; simp [coeff_one, show k ≠ 0 by omega]
  | succ a ih =>
    induction b generalizing k with
    | zero => rw [Nat.cast_zero, hP.2.1]; simp [coeff_one, show k ≠ 0 by omega]
    | succ b ihb =>
      by_cases hd : b + 1 = a + 1
      · rw [hd, hP.1]; simp [show k ≠ a + 1 by omega]
      · rw [hP.2.2.2 (a + 1) ((b + 1 : ℕ) : ℤ) (by omega) (by omega)]
        have hsub : ((b + 1 : ℕ) : ℤ) - 1 = b := by omega
        simp only [hsub, Nat.add_sub_cancel, coeff_add, coeff_C_mul]
        rw [ihb k (by omega) (by omega), ih (b + 1) k (by omega) hk]
        simp

private noncomputable def shift (P : ℕ → ℤ → Polynomial ℤ) :
    Polynomial ℤ →ₗ[ℤ] Polynomial ℤ :=
  Polynomial.lsum fun j => (LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight (P (j + 1) (j : ℤ))

private theorem shift_monomial (P : ℕ → ℤ → Polynomial ℤ) (j : ℕ) (c : ℤ) :
    shift P (C c * X ^ j) = C c * P (j + 1) (j : ℤ) := by
  change (C c * X ^ j).sum (fun i d => d • P (i + 1) (i : ℤ)) = _
  rw [C_mul_X_pow_eq_monomial, sum_monomial_index _ _ (by simp), smul_eq_C_mul]

private theorem shift_table {P : ℕ → ℤ → Polynomial ℤ}
    (hP : IsSourcePolynomialTable P) (a b : ℕ) (hba : b ≤ a) :
    shift P (P a (b : ℤ)) = P (a + 1) (b : ℤ) := by
  induction a generalizing b with
  | zero =>
    have : b = 0 := by omega
    subst b
    rw [Nat.cast_zero, hP.2.1, hP.2.1]
    simpa [hP.2.1] using shift_monomial P 0 1
  | succ a ih =>
    induction b with
    | zero =>
      rw [Nat.cast_zero, hP.2.1, hP.2.1]
      simpa [hP.2.1] using shift_monomial P 0 1
    | succ b ihb =>
      by_cases hd : b + 1 = a + 1
      · rw [hd, hP.1]
        simpa using shift_monomial P (a + 1) 1
      · rw [hP.2.2.2 (a + 1) ((b + 1 : ℕ) : ℤ) (by omega) (by omega),
          map_add, ← smul_eq_C_mul, map_smul, smul_eq_C_mul,
          hP.2.2.2 (a + 1 + 1) ((b + 1 : ℕ) : ℤ) (by omega) (by omega)]
        have hsub : ((b + 1 : ℕ) : ℤ) - 1 = b := by omega
        simp only [hsub, Nat.add_sub_cancel]
        rw [ihb (by omega), ih (b + 1) (by omega)]

private theorem row_expand {P : ℕ → ℤ → Polynomial ℤ}
    (hP : IsSourcePolynomialTable P) (n : ℕ) :
    P (n + 1) (n : ℤ) = ∑ j ∈ Finset.range (n + 1),
      C ((P (n + 1) (n : ℤ)).coeff j) * X ^ j := by
  classical
  conv_lhs => rw [← sum_C_mul_X_pow_eq (P (n + 1) (n : ℤ))]
  apply sum_eq_of_subset _ (fun j => by simp)
  intro j hj
  simp only [mem_support_iff] at hj
  simp only [Finset.mem_range]
  by_contra hn
  exact hj (coeff_above hP (n + 1) n j (by omega) (by omega))

private theorem row_step {P : ℕ → ℤ → Polynomial ℤ}
    (hP : IsSourcePolynomialTable P) (n : ℕ) :
    P (n + 2) ((n + 1 : ℕ) : ℤ) =
      (∑ j ∈ Finset.range (n + 1),
        C ((P (n + 1) (n : ℤ)).coeff j) * P (j + 1) (j : ℤ)) +
        C ((n : ℤ) + 2) * X ^ (n + 1) := by
  have he := shift_table hP (n + 1) n (by omega)
  rw [row_expand hP n, map_sum] at he
  simp only [shift_monomial] at he
  rw [hP.2.2.2 (n + 2) ((n + 1 : ℕ) : ℤ) (by omega) (by omega)]
  have hs : ((n + 1 : ℕ) : ℤ) - 1 = n := by omega
  simp only [hs, show n + 2 - 1 = n + 1 by omega]
  rw [← he, hP.1]
  congr 2 <;> push_cast <;> ring

/-- Coefficients of the independently defined polynomial rows. -/
private def coefficientTriangle (P : ℕ → ℤ → Polynomial ℤ) (n k : ℕ) : ℤ :=
  (P (n + 1) (n : ℤ)).coeff k

private theorem coefficientTriangle_source {P : ℕ → ℤ → Polynomial ℤ}
    (hP : IsSourcePolynomialTable P) : IsSourceTriangle (coefficientTriangle P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro n k h; exact coeff_above hP (n + 1) n k (by omega) h
  · intro n
    cases n with
    | zero => simp [coefficientTriangle, hP.2.1]
    | succ n =>
      simp only [coefficientTriangle, row_step hP, coeff_add, finsetSum_coeff, coeff_C_mul]
      have hz : ∑ j ∈ Finset.range (n + 1),
          (P (n + 1) (n : ℤ)).coeff j * (P (j + 1) (j : ℤ)).coeff (n + 1) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [coeff_above hP (j + 1) j (n + 1) (by omega)
          (by simpa only [Finset.mem_range] using hj), mul_zero]
      rw [hz]
      simp
      omega
  · intro n k hkn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp only [coefficientTriangle, row_step hP, coeff_add,
      finsetSum_coeff, coeff_C_mul]
    rw [coeff_X_pow, ite_eq_right (by omega), mul_zero, add_zero]
    rw [← Finset.sum_range_add_sum_Ico _ (show k ≤ m + 1 by omega)]
    have hz : ∑ j ∈ Finset.range k,
        (P (m + 1) (m : ℤ)).coeff j * (P (j + 1) (j : ℤ)).coeff k = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [coeff_above hP (j + 1) j k (by omega)
        (by simpa only [Finset.mem_range] using hj), mul_zero]
    rw [hz, zero_add]
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]

private theorem triangle_unique {T U : ℕ → ℕ → ℤ}
    (hT : IsSourceTriangle T) (hU : IsSourceTriangle U) : T = U := by
  funext n k
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases ha : n < k
    · exact (hT.1 n k ha).trans (hU.1 n k ha).symm
    by_cases he : k = n
    · subst k; exact (hT.2.1 n).trans (hU.2.1 n).symm
    have hk : k < n := by omega
    rw [hT.2.2 n k hk, hU.2.2 n k hk]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := (Finset.mem_Ico.mp hj).2
    rw [ih (n - 1) (by omega) j, ih j hjn k]

/-- Kurkov's whole conjecture, with nonvacuity and the original source conventions. -/
theorem result : claim := by
  have hP := polynomialTable_source
  have hT := coefficientTriangle_source hP
  refine ⟨⟨coefficientTriangle polynomialTable, hT⟩, ⟨polynomialTable, hP⟩, ?_⟩
  intro T P ht hp n
  have ep := polynomial_unique hp hP
  subst P
  have et := triangle_unique ht hT
  subst T
  exact (row_expand hP n).symm

end
end D5.S1.Recurrence.Algebraic.KurkovA102086RowPolynomial
