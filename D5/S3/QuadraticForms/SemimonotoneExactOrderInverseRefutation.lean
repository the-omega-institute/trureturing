/- GID: D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.claim; result=D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.result; claim=D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.claim
   digest: A singular real matrix of exact semimonotone order three refutes the general inverse assertion. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Chauhan and Dubey, arXiv:2603.00639v1, Section 2, Definition 3.1,
and Remark 4.1, second bullet. The claim includes actual invertibility,
as well as determinant negativity and the off-diagonal inequalities for the inverse.
Principal blocks use arbitrary finite index subsets, including all larger sizes.
Their cardinalities are automatically bounded above by the ambient order.

admission_basis: open-problem-resolution (#22883; Refuted)
proof_shape: bind-only after expanding the consumed private helpers
escape_witness: none; no frozen D5 dependency
All private lemmas are consumed by result or by another consumed private lemma.
The unique public theorem result is the designated refutation result.
-/

namespace D5.S3.QuadraticForms.SemimonotoneExactOrderInverseRefutation

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Section 2: nonzero nonnegative vectors have a positive coordinate with nonnegative image. -/
def Semimonotone {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, x ≠ 0 → (∀ i, 0 ≤ x i) →
    ∃ i, 0 < x i ∧ 0 ≤ (A.mulVec x) i

/-- Definition 3.1: all blocks of size n-k qualify, and every larger block fails. -/
def IsExactOrder (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  k ≤ n ∧
    (∀ α : Finset (Fin n), α.card = n - k →
      Semimonotone (A.submatrix (fun i : α => i.val) (fun j : α => j.val))) ∧
    (∀ α : Finset (Fin n), n - k < α.card →
      ¬ Semimonotone (A.submatrix (fun i : α => i.val) (fun j : α => j.val)))

/-- Section 2: a Z-matrix has nonpositive off-diagonal entries. -/
def IsZMatrix {ι : Type} (A : Matrix ι ι ℝ) : Prop :=
  ∀ i j, i ≠ j → A i j ≤ 0

/-- The complete universal assertion asked in Remark 4.1, second bullet. -/
def claim : Prop :=
  ∀ (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    3 ≤ n → 1 ≤ k → k < n → IsExactOrder n k A →
      A.det < 0 ∧ IsUnit A ∧ IsZMatrix A⁻¹

/-- A real singular matrix with positive diagonal and strictly negative off-diagonal entries. -/
def counterexample : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, -5, -2, -2; -5, 1, -2, -2; -2, -2, 1, -5; -2, -2, -5, 1]

/-- Opposite signs on the two equal-sized blocks. -/
def kernelVector : Fin 4 → ℝ := ![1, 1, -1, -1]

private theorem diagonal (i : Fin 4) : counterexample i i = 1 := by
  fin_cases i <;> norm_num [counterexample, Matrix.of_apply]

private theorem off_diagonal (i j : Fin 4) (h : i ≠ j) : counterexample i j ≤ -2 := by
  fin_cases i <;> fin_cases j <;> norm_num [counterexample, Matrix.of_apply] at h ⊢

private theorem singleton_semimonotone (a : Fin 4) :
    Semimonotone (counterexample.submatrix (fun i : ({a} : Finset (Fin 4)) => i.val)
      (fun j : ({a} : Finset (Fin 4)) => j.val)) := by
  intro x hx hnonneg
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hx
  refine ⟨i, lt_of_le_of_ne (hnonneg i) (Ne.symm hi), ?_⟩
  have heq : ∀ j : ({a} : Finset (Fin 4)), j = i := fun j => Subsingleton.elim _ _
  simpa [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, heq,
    diagonal] using hnonneg i

private theorem larger_not_semimonotone (α : Finset (Fin 4)) (hα : 1 < α.card) :
    ¬ Semimonotone (counterexample.submatrix (fun i : α => i.val) (fun j : α => j.val)) := by
  intro h
  have hn : α.Nonempty := Finset.card_pos.mp (lt_trans Nat.zero_lt_one hα)
  have hone : (fun _ : α => (1 : ℝ)) ≠ 0 := by
    intro hz
    obtain ⟨a, ha⟩ := hn
    have := congrFun hz ⟨a, ha⟩
    norm_num at this
  obtain ⟨i, _, hi⟩ := h (fun _ => 1) hone (fun _ => zero_le_one)
  obtain ⟨b, hb, hbi⟩ := Finset.exists_mem_ne hα i.val
  let j : α := ⟨b, hb⟩
  have hji : j ≠ i := fun hij => hbi (congrArg Subtype.val hij)
  have hsum : (∑ l : α, counterexample i.val l.val) ≤
      ∑ l ∈ ({i, j} : Finset α), counterexample i.val l.val := by
    apply Finset.sum_le_sum_of_subset_of_nonpos (Finset.subset_univ _)
    intro l _ hl
    have hli : l ≠ i := by
      intro e
      exact hl (by simp [e])
    exact le_trans (off_diagonal _ _ (fun e => hli (Subtype.ext e.symm))) (by norm_num)
  have hpair : (∑ l ∈ ({i, j} : Finset α), counterexample i.val l.val) ≤ -1 := by
    rw [Finset.sum_pair hji.symm, diagonal]
    have hoff := off_diagonal i.val j.val (fun e => hji (Subtype.ext e.symm))
    linarith
  have hrow : 0 ≤ ∑ l : α, counterexample i.val l.val := by
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] using hi
  linarith

private theorem exact_order : IsExactOrder 4 3 counterexample := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro α hα
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (by simpa using hα)
    exact singleton_semimonotone a
  · intro α hα
    exact larger_not_semimonotone α (by simpa using hα)

private theorem kernel_vector_nonzero : kernelVector ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [kernelVector] at this

private theorem kernel_vector_mul : counterexample.mulVec kernelVector = 0 := by
  ext i
  fin_cases i <;> norm_num [counterexample, kernelVector, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.of_apply]

/-- Remark 4.1's conjunction fails at n=4 and k=3. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨hdet, hunit, _⟩ := h 4 3 counterexample (by norm_num) (by norm_num)
    (by norm_num) exact_order
  exact kernel_vector_nonzero
    (Matrix.eq_zero_of_mulVec_eq_zero (ne_of_lt hdet) kernel_vector_mul)

end D5.S3.QuadraticForms.SemimonotoneExactOrderInverseRefutation
