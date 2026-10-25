/- GID: D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.claim; result=D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.result; claim=D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.claim
   digest: A stable two-block matrix has an unstable asynchronous iteration with unit delays. -/

import D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! A stable two-block iteration becomes unstable when only remote entries are delayed. -/

noncomputable section

open Matrix
open scoped ENNReal NNReal

namespace D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation

/-- Coordinates grouped into blocks of the prescribed sizes. -/
@[reducible] def BlockIndex (ℓ : ℕ) (n : Fin ℓ → ℕ) := Σ i : Fin ℓ, Fin (n i)

/-- The history state has the newest iterate in slot zero. -/
def asyncMatrix {ℓ : ℕ} {n : Fin ℓ → ℕ}
    (M : Matrix (BlockIndex ℓ n) (BlockIndex ℓ n) ℝ)
    (δ : Fin ℓ → Fin ℓ → ℕ) (k : ℕ) :
    Matrix (Fin (k + 1) × BlockIndex ℓ n) (Fin (k + 1) × BlockIndex ℓ n) ℝ :=
  fun rp sq =>
    if rp.1.val = 0 then
      if sq.1.val = δ sq.2.1 rp.2.1 then M rp.2 sq.2 else 0
    else if sq.1.val + 1 = rp.1.val ∧ sq.2 = rp.2 then 1 else 0

/-- The spectral radius is taken after extension of scalars to the complex numbers. -/
def radius {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : ℝ≥0∞ :=
  spectralRadius ℂ (M.map (algebraMap ℝ ℂ))

/-- Nonempty blocks, zero local delay, bounded positive remote delays, and a stable radius. -/
def Admissible (ℓ : ℕ) (n : Fin ℓ → ℕ) (k : ℕ)
    (M : Matrix (BlockIndex ℓ n) (BlockIndex ℓ n) ℝ)
    (δ : Fin ℓ → Fin ℓ → ℕ) (lambda : ℝ) : Prop :=
  (∀ i, 0 < n i) ∧ (∀ i, δ i i = 0) ∧
    (∀ i j, i ≠ j → 1 ≤ δ i j ∧ δ i j ≤ k) ∧
    0 < lambda ∧ lambda < 1 ∧ radius M = ENNReal.ofReal lambda

/-- The proposed power bound, uniformly over block arrays and admissible delays. -/
def Q1 : Prop :=
  ∀ (ℓ : ℕ) (n : Fin ℓ → ℕ) (k : ℕ)
    (M : Matrix (BlockIndex ℓ n) (BlockIndex ℓ n) ℝ)
    (δ : Fin ℓ → Fin ℓ → ℕ) (lambda : ℝ),
    Admissible ℓ n k M δ lambda →
      radius (asyncMatrix M δ k) ≤ ENNReal.ofReal (lambda ^ ((1 : ℝ) / (k + 1)))

/-- A uniformly subunit bound depending only on the original radius and maximum delay. -/
def Q2 : Prop :=
  ∃ f : ℝ → ℕ → ℝ,
    (∀ lambda k, 0 < lambda → lambda < 1 → 0 < f lambda k ∧ f lambda k < 1) ∧
    ∀ (ℓ : ℕ) (n : Fin ℓ → ℕ) (k : ℕ)
      (M : Matrix (BlockIndex ℓ n) (BlockIndex ℓ n) ℝ)
      (δ : Fin ℓ → Fin ℓ → ℕ) (lambda : ℝ),
      Admissible ℓ n k M δ lambda →
        radius (asyncMatrix M δ k) ≤ ENNReal.ofReal (f lambda k)

/-- At least one of the two proposed bounds for the price of asynchrony holds. -/
def claim : Prop := Q1 ∨ Q2

@[reducible] private def sizes : Fin 2 → ℕ := fun _ => 1

private def baseMatrix : Matrix (BlockIndex 2 sizes) (BlockIndex 2 sizes) ℝ :=
  fun p q => if p.1 = 0 then (if q.1 = 0 then 7 / 4 else 5 / 4)
    else (if q.1 = 0 then -5 / 4 else -3 / 4)

private def delays : Fin 2 → Fin 2 → ℕ := fun i j => if i = j then 0 else 1

private def unstableVector : Fin 2 × BlockIndex 2 sizes → ℂ :=
  fun rp => if rp.1 = 0 then (if rp.2.1 = 0 then 10 else -5)
    else (if rp.2.1 = 0 then 8 else -4)

private theorem base_square_zero :
    (baseMatrix.map (algebraMap ℝ ℂ) -
      algebraMap ℂ (Matrix (BlockIndex 2 sizes) (BlockIndex 2 sizes) ℂ) (1 / 2)) ^ 2 = 0 := by
  apply Matrix.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [pow_two, Matrix.mul_apply, Fintype.sum_sigma, Fin.sum_univ_two, Fin.sum_univ_succ,
      baseMatrix, Matrix.map_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, sizes, Fintype.sum_unique]

private theorem base_spectrum :
    spectrum ℂ (baseMatrix.map (algebraMap ℝ ℂ)) = {(1 / 2 : ℂ)} := by
  sorry

private theorem base_radius : radius baseMatrix = ENNReal.ofReal (1 / 2) := by
  sorry

private theorem witness_admissible : Admissible 2 sizes 1 baseMatrix delays (1 / 2) := by
  sorry

private theorem unstable_eigenvector :
    unstableVector ≠ 0 ∧
    (asyncMatrix baseMatrix delays 1).map (algebraMap ℝ ℂ) *ᵥ unstableVector =
      (5 / 4 : ℂ) • unstableVector := by
  sorry

private theorem asynchronous_radius :
    ENNReal.ofReal (5 / 4) ≤ radius (asyncMatrix baseMatrix delays 1) := by
  sorry

private theorem not_q1 : ¬ Q1 := by
  sorry

private theorem not_q2 : ¬ Q2 := by
  sorry

/-- A matrix of radius one half with unit remote delays refutes both proposed bounds. -/
theorem result : ¬ claim := by
  intro h
  exact h.elim not_q1 not_q2

end D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
