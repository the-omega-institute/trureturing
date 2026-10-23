/- GID: D5/S3/Quantum/Fibers/FiveModeRealWaitSpan
   generality: I
   mirror-B: D5/B/S3/Quantum/Fibers/FiveModeRealWaitSpan
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Fibers/FiveModeRealResponse.waits_separate_real; premises=D5/S3/Quantum/Fibers/FiveModeRealWaitSpan.symmetric_decomposition
   digest: Actual nonnegative waits of the five-mode generator span all real symmetric effects. -/

import D5.S3.Quantum.Fibers.NonnegativeConjugationSpan
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix Matrix.Norms.Operator
open NormedSpace
namespace D5.S3.Quantum.Fibers.FiveModeRealWaitSpan
open D5.S3.Quantum.Fibers.NonnegativeConjugationSpan

/-- The real generator in the fixed passive frame, in mode order N, 2, 3, 5, 25. -/
def generator : Matrix (Fin 5) (Fin 5) ℝ := !![0, 1, 1, 1, 0; -1, 0, 0, 0, -1; -1, 0, 0, 0, 0; -1, 0, 0, 0, -1; 0, 1, 0, 1, 0]

/-- The subspace of real symmetric five-mode effects. -/
def symmetricSpace : Submodule ℝ (Matrix (Fin 5) (Fin 5) ℝ) where
  carrier := {X | X.transpose = X}
  zero_mem' := by simp
  add_mem' := by intro X Y hX hY; simp_all [Matrix.transpose_add]
  smul_mem' := by intro c X hX; simp_all [Matrix.transpose_smul]

/-- This span uses actual nonnegative waiting times and one complete mode read. -/
def waitSpan : Submodule ℝ (Matrix (Fin 5) (Fin 5) ℝ) :=
  Submodule.span ℝ (Set.range (fun p : NNReal × Fin 5 =>
    conjugate generator (Matrix.single p.2 p.2 1) p.1))

private def selected (j : Fin 15) : ℕ × Fin 5 :=
  match j.val with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 3)
  | 4 => (0, 4)
  | 5 => (1, 0)
  | 6 => (1, 1)
  | 7 => (1, 2)
  | 8 => (1, 3)
  | 9 => (2, 0)
  | 10 => (2, 1)
  | 11 => (2, 2)
  | 12 => (3, 0)
  | 13 => (3, 1)
  | _ => (4, 0)
private def jet (j : Fin 15) : Matrix (Fin 5) (Fin 5) ℝ :=
  (NonnegativeConjugationSpan.commutator generator)^[(selected j).1] (Matrix.single (selected j).2 (selected j).2 1)
private def jetTable (j : Fin 15) : Matrix (Fin 5) (Fin 5) ℝ :=
  match j.val with
  | 0 => !![1, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]
  | 1 => !![0, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]
  | 2 => !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]
  | 3 => !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 0]
  | 4 => !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 1]
  | 5 => !![0, 1, 1, 1, 0; 1, 0, 0, 0, 0; 1, 0, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 0, 0]
  | 6 => !![0, -1, 0, 0, 0; -1, 0, 0, 0, -1; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, -1, 0, 0, 0]
  | 7 => !![0, 0, -1, 0, 0; 0, 0, 0, 0, 0; -1, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]
  | 8 => !![0, 0, 0, -1, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; -1, 0, 0, 0, -1; 0, 0, 0, -1, 0]
  | 9 => !![-6, 0, 0, 0, -2; 0, 2, 2, 2, 0; 0, 2, 2, 2, 0; 0, 2, 2, 2, 0; -2, 0, 0, 0, 0]
  | 10 => !![2, 0, 0, 0, 2; 0, -4, -1, -2, 0; 0, -1, 0, 0, 0; 0, -2, 0, 0, 0; 2, 0, 0, 0, 2]
  | 11 => !![2, 0, 0, 0, 0; 0, 0, -1, 0, 0; 0, -1, -2, -1, 0; 0, 0, -1, 0, 0; 0, 0, 0, 0, 0]
  | 12 => !![0, -14, -12, -14, 0; -14, 0, 0, 0, -6; -12, 0, 0, 0, -6; -14, 0, 0, 0, -6; 0, -6, -6, -6, 0]
  | 13 => !![0, 11, 3, 6, 0; 11, 0, 0, 0, 10; 3, 0, 0, 0, 3; 6, 0, 0, 0, 6; 0, 10, 3, 6, 0]
  | _ => !![80, 0, 0, 0, 46; 0, -40, -32, -40, 0; 0, -32, -24, -32, 0; 0, -40, -32, -40, 0; 46, 0, 0, 0, 24]

private def coefficients (X : Matrix (Fin 5) (Fin 5) ℝ) (j : Fin 15) : ℝ :=
  match j.val with
  | 0 => 1 * X 0 0 + 4 * X 0 4 + 5 * X 1 3 + 2 * X 2 3
  | 1 => 1 * X 1 1 + -2 * X 1 2 + -1 * X 1 3 + 2 * X 2 3
  | 2 => -2 * X 1 2 + 1 * X 1 3 + 1 * X 2 2
  | 3 => 2 * X 1 2 + -1 * X 1 3 + -2 * X 2 3 + 1 * X 3 3
  | 4 => -4 * X 0 4 + 2 * X 1 2 + -4 * X 1 3 + -2 * X 2 3 + 1 * X 4 4
  | 5 => 4 * X 0 1 + -3 * X 0 3 + -4 * X 1 4 + (-4 / 3 : ℝ) * X 2 4 + 3 * X 3 4
  | 6 => 7 * X 0 1 + -7 * X 0 3 + -8 * X 1 4 + 1 * X 2 4 + 7 * X 3 4
  | 7 => 1 * X 0 1 + -1 * X 0 2 + -1 * X 1 4 + (2 / 3 : ℝ) * X 2 4
  | 8 => 3 * X 0 1 + -3 * X 0 3 + -3 * X 1 4 + 1 * X 2 4 + 2 * X 3 4
  | 9 => (10 / 3 : ℝ) * X 0 4 + -1 * X 1 2 + (23 / 6 : ℝ) * X 1 3 + 1 * X 2 3
  | 10 => -1 * X 1 2 + 1 * X 2 3
  | 11 => (4 / 3 : ℝ) * X 0 4 + -2 * X 1 2 + (7 / 3 : ℝ) * X 1 3 + 1 * X 2 3
  | 12 => (1 / 2 : ℝ) * X 0 1 + (-1 / 2 : ℝ) * X 0 3 + (-1 / 2 : ℝ) * X 1 4 + (-1 / 6 : ℝ) * X 2 4 + (1 / 2 : ℝ) * X 3 4
  | 13 => 1 * X 0 1 + -1 * X 0 3 + -1 * X 1 4 + 1 * X 3 4
  | _ => (1 / 6 : ℝ) * X 0 4 + (1 / 6 : ℝ) * X 1 3

private def previous (j : Fin 10) : Fin 15 :=
  match j.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 9
  | 8 => 10
  | _ => 12

private theorem jet_steps (j : Fin 10) :
    NonnegativeConjugationSpan.commutator generator (jetTable (previous j)) =
      jetTable ⟨j.val + 5, by omega⟩ := by
  fin_cases j <;> ext i l <;> fin_cases i <;> fin_cases l <;>
    norm_num [previous, jetTable, generator, NonnegativeConjugationSpan.commutator,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ]

private theorem jet_values (j : Fin 15) : jet j = jetTable j := by
  have h0 : jet 0 = jetTable 0 := by
    ext i l
    fin_cases i <;> fin_cases l <;> norm_num [jet, selected, jetTable, Matrix.single_apply, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> decide
  have h1 : jet 1 = jetTable 1 := by
    ext i l
    fin_cases i <;> fin_cases l <;> norm_num [jet, selected, jetTable, Matrix.single_apply, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> decide
  have h2 : jet 2 = jetTable 2 := by
    ext i l
    fin_cases i <;> fin_cases l <;> norm_num [jet, selected, jetTable, Matrix.single_apply, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> decide
  have h3 : jet 3 = jetTable 3 := by
    ext i l
    fin_cases i <;> fin_cases l <;> norm_num [jet, selected, jetTable, Matrix.single_apply, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> decide
  have h4 : jet 4 = jetTable 4 := by
    ext i l
    fin_cases i <;> fin_cases l <;> norm_num [jet, selected, jetTable, Matrix.single_apply, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> decide
  have h5 : jet 5 = jetTable 5 := by
    change NonnegativeConjugationSpan.commutator generator (jet 0) = jetTable 5
    rw [h0]
    exact jet_steps 0
  have h6 : jet 6 = jetTable 6 := by
    change NonnegativeConjugationSpan.commutator generator (jet 1) = jetTable 6
    rw [h1]
    exact jet_steps 1
  have h7 : jet 7 = jetTable 7 := by
    change NonnegativeConjugationSpan.commutator generator (jet 2) = jetTable 7
    rw [h2]
    exact jet_steps 2
  have h8 : jet 8 = jetTable 8 := by
    change NonnegativeConjugationSpan.commutator generator (jet 3) = jetTable 8
    rw [h3]
    exact jet_steps 3
  have h9 : jet 9 = jetTable 9 := by
    change NonnegativeConjugationSpan.commutator generator (jet 5) = jetTable 9
    rw [h5]
    exact jet_steps 4
  have h10 : jet 10 = jetTable 10 := by
    change NonnegativeConjugationSpan.commutator generator (jet 6) = jetTable 10
    rw [h6]
    exact jet_steps 5
  have h11 : jet 11 = jetTable 11 := by
    change NonnegativeConjugationSpan.commutator generator (jet 7) = jetTable 11
    rw [h7]
    exact jet_steps 6
  have h12 : jet 12 = jetTable 12 := by
    change NonnegativeConjugationSpan.commutator generator (jet 9) = jetTable 12
    rw [h9]
    exact jet_steps 7
  have h13 : jet 13 = jetTable 13 := by
    change NonnegativeConjugationSpan.commutator generator (jet 10) = jetTable 13
    rw [h10]
    exact jet_steps 8
  have h14 : jet 14 = jetTable 14 := by
    change NonnegativeConjugationSpan.commutator generator (jet 12) = jetTable 14
    rw [h12]
    exact jet_steps 9
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14

private theorem symmetric_decomposition (X : Matrix (Fin 5) (Fin 5) ℝ)
    (hX : X.transpose = X) : ∑ j, coefficients X j • jet j = X := by
  simp_rw [jet_values]
  have h10 : X 1 0 = X 0 1 := congrFun (congrFun hX 0) 1
  have h20 : X 2 0 = X 0 2 := congrFun (congrFun hX 0) 2
  have h30 : X 3 0 = X 0 3 := congrFun (congrFun hX 0) 3
  have h40 : X 4 0 = X 0 4 := congrFun (congrFun hX 0) 4
  have h21 : X 2 1 = X 1 2 := congrFun (congrFun hX 1) 2
  have h31 : X 3 1 = X 1 3 := congrFun (congrFun hX 1) 3
  have h41 : X 4 1 = X 1 4 := congrFun (congrFun hX 1) 4
  have h32 : X 3 2 = X 2 3 := congrFun (congrFun hX 2) 3
  have h42 : X 4 2 = X 2 4 := congrFun (congrFun hX 2) 4
  have h43 : X 4 3 = X 3 4 := congrFun (congrFun hX 3) 4
  ext i l
  fin_cases i <;> fin_cases l <;>
    norm_num [coefficients, jetTable, Matrix.sum_apply, Matrix.smul_apply,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, h10, h20, h30, h40, h21, h31, h41, h32, h42, h43] <;> ring <;> first | rfl | exact (congrFun (congrFun hX _) _).symm

/-- Skew symmetry of the fixed menu generator, consumed by its actual waiting laws. -/
theorem generator_skew : generator.transpose = -generator := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [generator]

/-- All real symmetric effects are spanned by actual nonnegative-time waits.
The exact finite jet calculation is consumed by this analytic conclusion. -/
theorem five_mode_nonnegative_wait_span : waitSpan = symmetricSpace := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨t,s⟩, rfl⟩
    change (conjugate generator (Matrix.single s s 1) t).transpose = _
    simp only [conjugate, Matrix.transpose_mul, ← Matrix.exp_transpose,
      Matrix.transpose_smul, generator_skew, Matrix.transpose_neg, neg_neg,
      Matrix.transpose_single, smul_neg, mul_assoc]
  · intro X hX
    rw [← symmetric_decomposition X hX]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    have hjet := commutator_jets_in_nonnegative_span generator
      (Matrix.single (selected j).2 (selected j).2 1) (selected j).1 0 le_rfl
    have hsub : observationSpan generator (Matrix.single (selected j).2 (selected j).2 1)
        ≤ waitSpan := by
      apply Submodule.span_le.mpr
      rintro _ ⟨t, ht, rfl⟩
      exact Submodule.subset_span ⟨(⟨t,ht⟩, (selected j).2), rfl⟩
    apply hsub
    simpa only [conjugate, zero_smul, exp_zero, one_mul, mul_one, jet] using hjet

end D5.S3.Quantum.Fibers.FiveModeRealWaitSpan
