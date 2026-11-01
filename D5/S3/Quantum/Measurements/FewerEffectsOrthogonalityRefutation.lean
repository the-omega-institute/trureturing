/- GID: D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.claim; result=D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.result; claim=D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.claim
   digest: Four projectors of ranks 2,2,3,3 refute the fewer-effects orthogonality conjecture. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Conjecture 2 in Liu and DeBrota, arXiv:2105.02074v2, Appendix C. The positive
square root and squared Frobenius distance are those of Section III. The construction
has ranks 2,2,2,4 in dimension ten; projectors of ranks 2,2,3,3 give a smaller value. -/

set_option autoImplicit false

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
  sorry

private theorem competitor_sqrt (i : Fin 4) :
    CFC.sqrt (competitor i) = competitor i := by
  sorry

private theorem construction_gram :
    gram (construction 4 10) = Matrix.diagonal ![2, 2, 2, 4] := by
  sorry

private theorem competitor_gram :
    gram competitor = Matrix.diagonal ![2, 2, 3, 3] := by
  sorry

private theorem competitor_povm : IsPOVMWith 4 10 competitor := by
  sorry

private theorem construction_orthogonality : orthogonality (construction 4 10) = 12 := by
  sorry

private theorem competitor_orthogonality : orthogonality competitor = 10 := by
  sorry

/-- The constructed POVM fails to minimize orthogonality, already for four effects
on a ten dimensional space. -/
theorem result : ¬ claim := by
  intro h
  have hle := h 4 10 (by decide) (by decide) competitor competitor_povm
  rw [construction_orthogonality, competitor_orthogonality] at hle
  norm_num at hle

end D5.S3.Quantum.Measurements.FewerEffectsOrthogonalityRefutation
