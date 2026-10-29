/- GID: D5/S3/Fourier/CuntzZeroFreeColumnRefutation
   generality: G
   mirror-B: D5/B/S3/Fourier/CuntzZeroFreeColumnRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Fourier/CuntzZeroFreeColumnRefutation.claim; result=D5/S3/Fourier/CuntzZeroFreeColumnRefutation.result; claim=D5/S3/Fourier/CuntzZeroFreeColumnRefutation.claim
   digest: Zero-free columns of integral Fourier matrices consist of units. -/

/-
proof_shape:
  FourierAxioms, IsIntegralFourierMatrix, claim: not-applicable(definition).
  weighted_column_squares: bind-only; consumer: zero_free_column_units.
  positive_weight_integer_square_rigidity: bind-only; consumer: zero_free_column_units.
  zero_free_column_units: bind-only; consumer: result.
  result: bind-only; no hypotheses; conclusion: Not claim.
escape_witness: none (all three helpers expand to pinned-library applications and normalization).
admission_basis: open-problem-resolution (#22614; Refuted).
Direct frozen dependencies: none, for every declaration.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The source indices 1,...,n use Fin n, with source index 1 represented by 0.
The defining matrix equation of Definition 4.1 fixes row norms; the reversed-index
explanatory sum in Definition 3.1 is not imposed as an additional hypothesis.
The general argument uses no determinant, symmetrization, fusion integrality or T.
The utility header designates the closed refutation of claim.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt

namespace D5.S3.Fourier.CuntzZeroFreeColumnRefutation

open scoped BigOperators

/-- Conditions (1)--(4) of Cuntz, Definition 4.1, with its positive square-root convention.
The source's indices 1,...,n are represented by Fin n; source index 1 is Lean index 0.
The diagonal equation fixes d as the row norms. -/
def FourierAxioms {n : ℕ} (hn : 0 < n)
    (s : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) : Prop :=
  (∀ i : Fin n, s i ⟨0, hn⟩ = 1) ∧
  Matrix.det s ≠ 0 ∧
  (∀ i : Fin n, 0 < Real.sqrt (d i)) ∧
  (s.map (Int.cast : ℤ → ℝ)) * (s.map (Int.cast : ℤ → ℝ)).transpose =
    Matrix.diagonal d ∧
  (∀ (i j : Fin n), Real.sqrt (d j) * (s i j : ℝ) =
    Real.sqrt (d i) * (s j i : ℝ)) ∧
  (∀ (i j l : Fin n), ∃ z : ℤ,
    (∑ k : Fin n, (s k i : ℝ) * (s k j : ℝ) * (s k l : ℝ) / d k) = (z : ℝ))

/-- The integral Fourier matrices explicitly specified in Definition 4.1, before its
additional congruence conditions (5)--(6). No T-matrix is required. -/
def IsIntegralFourierMatrix {n : ℕ} (hn : 0 < n)
    (s : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ d : Fin n → ℝ, FourierAxioms hn s d

/-- The existential assertion asked in Section 7(5), with every size, matrix,
column and row quantified. -/
def claim : Prop :=
  ∃ (n : ℕ) (hn : 0 < n) (s : Matrix (Fin n) (Fin n) ℤ),
    IsIntegralFourierMatrix hn s ∧
      ∃ k : Fin n, (∀ i : Fin n, s i k ≠ 0) ∧
        ∃ i : Fin n, s i k ≠ 1 ∧ s i k ≠ -1

private theorem weighted_column_squares {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (hgram : A * A.transpose = Matrix.diagonal d) (k : ι) :
    (∑ i, (A i k) ^ 2 / d i) = 1 := by
  have hright : A * (A.transpose * Matrix.diagonal (fun i => (d i)⁻¹)) = 1 := by
    rw [← Matrix.mul_assoc, hgram, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hd i]
    · simp [hij]
  have hleft : (A.transpose * Matrix.diagonal (fun i => (d i)⁻¹)) * A = 1 :=
    mul_eq_one_comm.mp hright
  have hdiag := congrArg (fun M : Matrix ι ι ℝ => M k k) hleft
  rw [Matrix.one_apply_eq, Matrix.mul_apply] at hdiag
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply] at hdiag
  calc
    (∑ i, A i k ^ 2 / d i) = ∑ i, A i k * (d i)⁻¹ * A i k := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 1 := hdiag

private theorem positive_weight_integer_square_rigidity {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hsum : (∑ i, w i) = 1) (hsq : (∑ i, w i * (a i : ℝ) ^ 2) = 1)
    (ha : ∀ i, a i ≠ 0) (i : ι) : a i = 1 ∨ a i = -1 := by
  have hsquare : ∀ j, (1 : ℝ) ≤ (a j : ℝ) ^ 2 := by
    intro j
    have hz : (0 : ℤ) < a j ^ 2 := sq_pos_of_ne_zero (ha j)
    have hz' : (1 : ℤ) ≤ a j ^ 2 := hz
    exact_mod_cast hz'
  have hle : ∀ j, w j ≤ w j * (a j : ℝ) ^ 2 := by
    intro j
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hsquare j) (hw j).le
  have heq : w i = w i * (a i : ℝ) ^ 2 := by
    exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp (hsum.trans hsq.symm)
      i (Finset.mem_univ i)
  have hsqi : (a i : ℝ) ^ 2 = 1 := by
    nlinarith [hw i]
  have hzi : a i ^ 2 = (1 : ℤ) := by exact_mod_cast hsqi
  exact sq_eq_one_iff.mp hzi

private theorem zero_free_column_units {n : ℕ} (hn : 0 < n)
    (s : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ)
    (hfirst : ∀ i, s i ⟨0, hn⟩ = 1) (hd : ∀ i, 0 < d i)
    (hgram : (s.map (Int.cast : ℤ → ℝ)) *
      (s.map (Int.cast : ℤ → ℝ)).transpose = Matrix.diagonal d)
    (k : Fin n) (hk : ∀ i, s i k ≠ 0) (i : Fin n) :
    s i k = 1 ∨ s i k = -1 := by
  have hcol := weighted_column_squares (s.map (Int.cast : ℤ → ℝ)) d
    (fun j => ne_of_gt (hd j)) hgram
  have hsum : (∑ j, (d j)⁻¹) = 1 := by
    simpa [Matrix.map_apply, hfirst] using hcol ⟨0, hn⟩
  have hsq : (∑ j, (d j)⁻¹ * (s j k : ℝ) ^ 2) = 1 := by
    simpa [Matrix.map_apply, div_eq_mul_inv, mul_comm] using hcol k
  exact positive_weight_integer_square_rigidity (fun j => s j k)
    (fun j => (d j)⁻¹) (fun j => inv_pos.mpr (hd j)) hsum hsq hk i

theorem result : ¬ claim := by
  rintro ⟨n, hn, s, ⟨d, h⟩, k, hk, i, hi1, hi2⟩
  have hd : ∀ j, 0 < d j := fun j => Real.sqrt_pos.mp (h.2.2.1 j)
  rcases zero_free_column_units hn s d h.1 hd h.2.2.2.1 k hk i with hunit | hunit
  · exact hi1 hunit
  · exact hi2 hunit

end D5.S3.Fourier.CuntzZeroFreeColumnRefutation
