/- GID: D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.claim; result=D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.result; claim=D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.claim
   digest: Four projectors of ranks 2,2,3,3 refute the fewer-effects orthogonality conjecture. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FinCases

/-! Conjecture 2 in Liu and DeBrota, arXiv:2105.02074v2, Appendix C. The positive
square root and squared Frobenius distance are those of Section IV. The construction
has ranks 2,2,2,4 in dimension ten; projectors of ranks 2,2,3,3 give a smaller value. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation

/-- The Gram matrix of the positive square roots of the effects. -/
def gram {n d : ℕ} (f : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => Matrix.trace (CFC.sqrt (f i) * CFC.sqrt (f j))

/-- Squared Frobenius distance of the square-root Gram matrix from the identity. -/
def orthogonality {n d : ℕ} (f : Fin n → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (gram f i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j)

/-- A POVM with exactly `n` nonzero effects on the `d` dimensional complex space. -/
def IsPOVMWith (n d : ℕ) (f : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i, (f i).PosSemidef ∧ f i ≠ 0) ∧ ∑ i, f i = 1

/-- The source construction: `a = d / n` ones in each of the first `n - 1` effects
and `a + b` in the last, where `b = d % n`, on consecutive disjoint blocks. -/
def construction (n d : ℕ) : Fin n → Matrix (Fin d) (Fin d) ℂ :=
  fun i => Matrix.diagonal fun k =>
    if i.val * (d / n) ≤ k.val ∧
        k.val < (if i.val < n - 1 then (i.val + 1) * (d / n) else d)
    then 1 else 0

/-- Conjecture 2: the constructed POVM minimizes orthogonality for `0 < n < d`. -/
def claim : Prop :=
  ∀ n d : ℕ, 0 < n → n < d →
    ∀ f : Fin n → Matrix (Fin d) (Fin d) ℂ,
      IsPOVMWith n d f → orthogonality (construction n d) ≤ orthogonality f

/-- Consecutive coordinate projectors with ranks 2,2,3,3. -/
private def competitor : Fin 4 → Matrix (Fin 10) (Fin 10) ℂ :=
  fun i => Matrix.diagonal fun k =>
    if (if i.val < 2 then i.val * 2 else i.val * 3 - 2) ≤ k.val ∧
        k.val < (if i.val < 2 then (i.val + 1) * 2 else (i.val + 1) * 3 - 2)
    then 1 else 0

private theorem construction_sqrt (i : Fin 4) :
    CFC.sqrt (construction 4 10 i) = construction 4 10 i := by
  apply CFC.sqrt_unique
  · dsimp only [construction]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    split_ifs <;> simp
  · apply Matrix.PosSemidef.nonneg
    dsimp only [construction]
    apply Matrix.PosSemidef.diagonal
    intro k
    split_ifs <;> simp <;> split_ifs <;> simp

private theorem competitor_sqrt (i : Fin 4) :
    CFC.sqrt (competitor i) = competitor i := by
  apply CFC.sqrt_unique
  · dsimp only [competitor]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    split_ifs <;> simp
  · apply Matrix.PosSemidef.nonneg
    dsimp only [competitor]
    apply Matrix.PosSemidef.diagonal
    intro k
    split_ifs <;> simp <;> split_ifs <;> simp

private theorem construction_gram :
    gram (construction 4 10) = Matrix.diagonal ![2, 2, 2, 4] := by
  ext i j
  change Matrix.trace (CFC.sqrt (construction 4 10 i) *
    CFC.sqrt (construction 4 10 j)) = _
  rw [construction_sqrt, construction_sqrt]
  dsimp only [construction]
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, Matrix.diagonal_apply]

private theorem competitor_gram :
    gram competitor = Matrix.diagonal ![2, 2, 3, 3] := by
  ext i j
  change Matrix.trace (CFC.sqrt (competitor i) * CFC.sqrt (competitor j)) = _
  rw [competitor_sqrt, competitor_sqrt]
  dsimp only [competitor]
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, Matrix.diagonal_apply]

private theorem competitor_povm : IsPOVMWith 4 10 competitor := by
  constructor
  · intro i
    constructor
    · dsimp only [competitor]
      apply Matrix.PosSemidef.diagonal
      intro k
      split_ifs <;> simp <;> split_ifs <;> simp
    · intro hzero
      have hdiag := congrFun (congrFun competitor_gram i) i
      change Matrix.trace (CFC.sqrt (competitor i) * CFC.sqrt (competitor i)) = _ at hdiag
      rw [hzero, CFC.sqrt_zero, zero_mul, Matrix.trace_zero] at hdiag
      fin_cases i <;> norm_num [Matrix.diagonal_apply] at hdiag
  · ext k l
    change (∑ i, competitor i) k l = (1 : Matrix (Fin 10) (Fin 10) ℂ) k l
    simp only [Matrix.sum_apply, Fin.sum_univ_succ]
    dsimp only [competitor]
    fin_cases k <;> fin_cases l <;> norm_num [Matrix.diagonal_apply, Matrix.one_apply]

private theorem construction_orthogonality : orthogonality (construction 4 10) = 12 := by
  change (∑ i, ∑ j, Complex.normSq
    (gram (construction 4 10) i j - (1 : Matrix (Fin 4) (Fin 4) ℂ) i j)) = 12
  rw [construction_gram]
  norm_num [Fin.sum_univ_succ, Matrix.diagonal_apply, Matrix.one_apply, Complex.normSq_apply]

private theorem competitor_orthogonality : orthogonality competitor = 10 := by
  change (∑ i, ∑ j, Complex.normSq
    (gram competitor i j - (1 : Matrix (Fin 4) (Fin 4) ℂ) i j)) = 10
  rw [competitor_gram]
  norm_num [Fin.sum_univ_succ, Matrix.diagonal_apply, Matrix.one_apply, Complex.normSq_apply]

/-- The constructed POVM fails to minimize orthogonality, already for four effects
on a ten dimensional space. -/
theorem result : ¬ claim := by
  intro h
  have hle := h 4 10 (by decide) (by decide) competitor competitor_povm
  rw [construction_orthogonality, competitor_orthogonality] at hle
  norm_num at hle

end D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation
