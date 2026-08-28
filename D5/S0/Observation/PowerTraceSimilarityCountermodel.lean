/- GID: D5/S0/Observation/PowerTraceSimilarityCountermodel
   generality: G
   mirror-B: D5/B/S0/Observation/PowerTraceSimilarityCountermodel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal positive-power traces do not determine matrix similarity. -/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Rank

/- Library-search audit trail (2026-08-25):
   * Repository searches for `power.*trace`, `charpoly`, `rank.*one`,
     `Matrix.single 0 1`, and matrix similarity found only
     `D5.S0.Observation.BoundedPowerTraceCRTRecovery`, whose integer theorem
     concerns one bounded trace and has none of the characteristic-polynomial,
     rank, or non-similarity clauses required here.
   * Pinned Mathlib exact hits `Matrix.charpoly_fin_two`, `Matrix.rank_zero`,
     `Matrix.rank_vecMulVec_le`, and `Matrix.single_eq_single_vecMulVec_single`
     provide the standard matrix facts used below. No theorem packages the
     source's explicit zero/nilpotent countermodel or its full clause set.
   * No canonical matrix-similarity predicate was found, so similarity is
     exposed directly as conjugacy by a unit of the matrix ring. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Observation.PowerTraceSimilarityCountermodel

open Polynomial

/-- The zero matrix and the nonzero nilpotent Jordan block have equal traces
for every positive power and equal characteristic polynomials, but different
ranks. Consequently they are not conjugate, and equality of all positive-power
traces does not determine a matrix similarity class. -/
theorem power_traces_do_not_determine_similarity {K : Type*} [Field K] :
    let A : Matrix (Fin 2) (Fin 2) K := 0
    let N : Matrix (Fin 2) (Fin 2) K := Matrix.single 0 1 1
    (∀ k : ℕ, 1 ≤ k →
        Matrix.trace (A ^ k) = 0 ∧ Matrix.trace (N ^ k) = 0) ∧
      A.charpoly = X ^ 2 ∧
      N.charpoly = X ^ 2 ∧
      A.rank = 0 ∧
      N.rank = 1 ∧
      (¬ ∃ P : (Matrix (Fin 2) (Fin 2) K)ˣ,
        (P : Matrix (Fin 2) (Fin 2) K) * A *
            (↑P⁻¹ : Matrix (Fin 2) (Fin 2) K) = N) ∧
      ¬ ∀ M1 M2 : Matrix (Fin 2) (Fin 2) K,
        (∀ k : ℕ, 1 ≤ k →
          Matrix.trace (M1 ^ k) = Matrix.trace (M2 ^ k)) →
        ∃ P : (Matrix (Fin 2) (Fin 2) K)ˣ,
          (P : Matrix (Fin 2) (Fin 2) K) * M1 *
            (↑P⁻¹ : Matrix (Fin 2) (Fin 2) K) = M2 := by
  dsimp only
  let N : Matrix (Fin 2) (Fin 2) K := Matrix.single 0 1 1
  have hNne : N ≠ 0 := by
    intro h
    have h01 := congrFun (congrFun h 0) 1
    simp [N] at h01
  have hN2 : N ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, N, Matrix.mul_apply, Fin.sum_univ_two]
  have hTraceA : ∀ k : ℕ, 1 ≤ k →
      Matrix.trace ((0 : Matrix (Fin 2) (Fin 2) K) ^ k) = 0 := by
    intro k hk
    simp [Nat.ne_of_gt hk]
  have hTraceN : ∀ k : ℕ, 1 ≤ k → Matrix.trace (N ^ k) = 0 := by
    intro k hk
    rcases k with _ | _ | k
    · omega
    · simp [N, Matrix.trace]
    · rw [show k + 1 + 1 = 2 + k by omega, pow_add, hN2]
      simp
  have hCharpolyN : N.charpoly = X ^ 2 := by
    rw [Matrix.charpoly_fin_two]
    have hTrace : Matrix.trace N = 0 := by simpa using hTraceN 1 (by omega)
    have hDet : N.det = 0 := by
      simp [N, Matrix.det_fin_two]
    rw [hTrace, hDet]
    simp
  have hRankN : N.rank = 1 := by
    have hUpper : N.rank ≤ 1 := by
      simpa [N, Matrix.single_eq_single_vecMulVec_single] using
        Matrix.rank_vecMulVec_le (Pi.single 0 (1 : K)) (Pi.single 1 (1 : K))
    have hPositive : 0 < N.rank := by
      rw [Matrix.rank_eq_finrank_span_cols]
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      let column : Submodule.span K (Set.range N.col) :=
        ⟨N.col 1, Submodule.subset_span ⟨1, rfl⟩⟩
      refine ⟨column, ?_⟩
      intro hzero
      have hvalue := congrFun (congrArg Subtype.val hzero) 0
      simp [column, N] at hvalue
    exact Nat.le_antisymm hUpper hPositive
  have hNotConjugate :
      ¬ ∃ P : (Matrix (Fin 2) (Fin 2) K)ˣ,
        (P : Matrix (Fin 2) (Fin 2) K) *
            (0 : Matrix (Fin 2) (Fin 2) K) *
              (↑P⁻¹ : Matrix (Fin 2) (Fin 2) K) = N := by
    rintro ⟨P, h⟩
    apply hNne
    simpa using h.symm
  refine ⟨?_, by simp, hCharpolyN, by simp, hRankN, hNotConjugate, ?_⟩
  · intro k hk
    exact ⟨hTraceA k hk, hTraceN k hk⟩
  · intro hAll
    apply hNotConjugate
    apply hAll 0 N
    intro k hk
    rw [hTraceA k hk, hTraceN k hk]

#print axioms power_traces_do_not_determine_similarity

end D5.S0.Observation.PowerTraceSimilarityCountermodel
