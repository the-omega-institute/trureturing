/- GID: D5/S3/Zeros/CriticalPoints/SchurStripBoundary
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/SchurStripBoundary
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: The right strip boundary estimate and its phase equality information. -/

import D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
import D5.S3.Zeros.CriticalPoints.RankOneTraceBound
import Mathlib.Tactic.Ring

/-! The right boundary is a weighted rank-one sum between imaginary powers. -/

set_option autoImplicit false
noncomputable section

open Matrix Complex
open scoped BigOperators ComplexConjugate

namespace D5.S3.Zeros.CriticalPoints.SchurStripBoundary

open RankOneComplexPowers RankOneTraceBound

private theorem boundary_factorization (n : ℕ) (hn : 0 < n)
    (u : Fin n → ℂ) (t : Fin n → ℝ) (ht : ∀ j, 0 < t j) (p y : ℝ) :
    H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) *
        diagonal (fun j => u j * positivePower (t j) ((p : ℂ) * (1 + (y : ℂ) * I))) *
        H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) =
      H n (((p * y / 2 : ℝ) : ℂ) * I) *
        (H n ((p / 2 : ℝ) : ℂ) *
          diagonal (fun j => ((t j ^ p : ℝ) : ℂ) *
            (u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I))) *
          H n ((p / 2 : ℝ) : ℂ)) *
        H n (((p * y / 2 : ℝ) : ℂ) * I) := by
  have hleft : H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) =
      H n (((p * y / 2 : ℝ) : ℂ) * I) * H n ((p / 2 : ℝ) : ℂ) := by
    rw [H_add n hn]
    congr 1
    push_cast
    ring
  have hright : H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) =
      H n ((p / 2 : ℝ) : ℂ) * H n (((p * y / 2 : ℝ) : ℂ) * I) := by
    rw [H_add n hn]
    congr 1
    push_cast
    ring
  have hd : (fun j => u j * positivePower (t j) ((p : ℂ) * (1 + (y : ℂ) * I))) =
      fun j => ((t j ^ p : ℝ) : ℂ) *
        (u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I)) := by
    funext j
    have he : (p : ℂ) * (1 + (y : ℂ) * I) =
        (p : ℂ) + (((p * y : ℝ) : ℂ) * I) := by push_cast; ring
    rw [he, positivePower_add, positivePower_ofReal (ht j)]
    ring
  conv_lhs => lhs; lhs; rw [hleft]
  conv_lhs => rhs; rw [hright]
  rw [hd]
  simp only [Matrix.mul_assoc]

/-- A unitary trace functional has the sharp right boundary bound, with common phases at equality.
The matrix expression is the value at `1 + y I` of the Schur strip interpolation family. -/
theorem right_boundary_bound_and_phases (n : ℕ) (hn : 0 < n)
    (u : Fin n → ℂ) (hu : ∀ j, ‖u j‖ = 1)
    (t : Fin n → ℝ) (ht : ∀ j, 0 < t j) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    let A := H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) *
      diagonal (fun j => u j * positivePower (t j) ((p : ℂ) * (1 + (y : ℂ) * I))) *
      H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2)
    let M := ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ j, t j ^ p
    ‖Matrix.trace (K * A)‖ ≤ M ∧
      (‖Matrix.trace (K * A)‖ = M →
        ∀ i j, u i * positivePower (t i) (((p * y : ℝ) : ℂ) * I) =
          u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I)) := by
  dsimp only
  let L := H n (((p * y / 2 : ℝ) : ℂ) * I)
  let V := L * K * L
  let a : Fin n → ℝ := fun j => t j ^ p
  let γ : Fin n → ℂ := fun j =>
    u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I)
  let B := H n ((p / 2 : ℝ) : ℂ) *
    diagonal (fun j => (a j : ℂ) * γ j) * H n ((p / 2 : ℝ) : ℂ)
  have hL : L ∈ Matrix.unitaryGroup (Fin n) ℂ := H_unitary n hn _
  have hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (Matrix.unitaryGroup (Fin n) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem hL hK) hL
  have ha : ∀ j, 0 < a j := fun j => Real.rpow_pos_of_pos (ht j) p
  have hγ : ∀ j, ‖γ j‖ = 1 := by
    intro j
    dsimp [γ]
    rw [norm_mul, hu j, one_mul, norm_positivePower]
    simp
  have htrace :
      Matrix.trace (K * (H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2) *
        diagonal (fun j => u j * positivePower (t j) ((p : ℂ) * (1 + (y : ℂ) * I))) *
        H n ((p : ℂ) * (1 + (y : ℂ) * I) / 2))) =
      Matrix.trace (V * ∑ j, ((a j : ℂ) * γ j) •
        Matrix.vecMulVec (column n p j).ofLp (star (column n p j).ofLp)) := by
    rw [boundary_factorization n hn u t ht p y]
    change Matrix.trace (K * (L * B * L)) = _
    rw [show K * (L * B * L) = (K * L) * B * L by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_cycle]
    change Matrix.trace ((L * (K * L)) * B) = _
    rw [show L * (K * L) = V by simp only [V, Matrix.mul_assoc]]
    dsimp only [B]
    rw [sandwich_eq_sum_columns]
  have hmass : ∑ j, a j * ‖column n p j‖ ^ 2 =
      ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ j, t j ^ p := by
    simp only [column_norm_sq n hn p]
    rw [← Finset.sum_mul, mul_comm]
  rw [htrace]
  constructor
  · exact (norm_trace_rank_one_sum_le (column n p) a γ (fun j => (ha j).le) hγ V hV).trans_eq
      hmass
  · intro heq
    exact phases_eq_of_norm_trace_rank_one_sum_eq (column n p) a γ ha hγ V hV
      (column_inner_ne_zero n hn p hp) (heq.trans hmass.symm)

end D5.S3.Zeros.CriticalPoints.SchurStripBoundary
