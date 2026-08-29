/- GID: D5/S3/Observer/GoldenCoding/MinimalBinaryUnimodularBreak
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/MinimalBinaryUnimodularBreak
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary nonnegative unimodular matrices have sharp golden expansion floors. -/

import D5.S1.Eigenstructure.FibonacciMatrixDiscriminant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/- Library-search audit trail (2026-08-29):
   * Current-tree name and body-shape searches found no frozen theorem combining
     both determinant-sign bounds and both canonical equality witnesses.
   * The existing declarations `fibonacciSubstitution`, `expandingEigenvector`,
     `fibonacci_substitution_spec`, and
     `fibonacci_substitution_trace_det_discriminant` supply the canonical real
     Fibonacci matrix and its spectral data.
   * Pinned Mathlib supplies `Matrix.charpoly_fin_two`, `Matrix.trace_fin_two`,
     `Matrix.det_fin_two`, `Real.goldenRatio_sq`, and
     `Real.one_lt_goldenRatio`; no exact theorem for the two sharp integral
     trace bounds was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.Observer.GoldenCoding.MinimalBinaryUnimodularBreak

open D5.S1.Scale

/-- A real characteristic root above one of a nonnegative integral binary
matrix is at least `phi` in determinant sign `-1` and at least `phi^2` in
determinant sign `1`. The Fibonacci matrix and its square realize equality. -/
theorem minimal_binary_unimodular_break
    (M : Matrix (Fin 2) (Fin 2) ℕ)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (hroot : Polynomial.IsRoot
      (M.map (Nat.cast : ℕ → ℝ)).charpoly lambda) :
    (Matrix.det (M.map (Nat.cast : ℕ → ℤ)) = -1 →
        Real.goldenRatio ≤ lambda) ∧
      (Matrix.det (M.map (Nat.cast : ℕ → ℤ)) = 1 →
        Real.goldenRatio ^ 2 ≤ lambda) ∧
      (let F : Matrix (Fin 2) (Fin 2) ℕ := !![1, 1; 1, 0]
       Matrix.det (F.map (Nat.cast : ℕ → ℤ)) = -1 ∧
         F.map (Nat.cast : ℕ → ℝ) = fibonacciSubstitution ∧
         1 < Real.goldenRatio ∧
         Polynomial.IsRoot (F.map (Nat.cast : ℕ → ℝ)).charpoly
           Real.goldenRatio) ∧
      (let F : Matrix (Fin 2) (Fin 2) ℕ := !![1, 1; 1, 0]
       let F2 := F ^ 2
       F2 = !![2, 1; 1, 1] ∧
         Matrix.det (F2.map (Nat.cast : ℕ → ℤ)) = 1 ∧
         1 < Real.goldenRatio ^ 2 ∧
         Polynomial.IsRoot (F2.map (Nat.cast : ℕ → ℝ)).charpoly
           (Real.goldenRatio ^ 2)) := by
  have hpoly :
      lambda ^ 2 - Matrix.trace (M.map (Nat.cast : ℕ → ℝ)) * lambda +
          Matrix.det (M.map (Nat.cast : ℕ → ℝ)) = 0 := by
    rw [Matrix.charpoly_fin_two] at hroot
    simpa [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul] using hroot
  have htrace :
      Matrix.trace (M.map (Nat.cast : ℕ → ℝ)) =
        ((M 0 0 + M 1 1 : ℕ) : ℝ) := by
    simp [Matrix.trace_fin_two]
  rw [htrace] at hpoly
  have negativeDeterminantBound :
      Matrix.det (M.map (Nat.cast : ℕ → ℤ)) = -1 →
        Real.goldenRatio ≤ lambda := by
    intro hdet
    have hdetReal :
        Matrix.det (M.map (Nat.cast : ℕ → ℝ)) = -1 := by
      rw [Matrix.det_fin_two] at hdet ⊢
      simp only [Matrix.map_apply] at hdet ⊢
      exact_mod_cast hdet
    rw [hdetReal] at hpoly
    let t : ℕ := M 0 0 + M 1 1
    have ht : 1 ≤ t := by
      by_contra hnot
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos hnot
      simp [t, ht0] at hpoly
      nlinarith
    have hquadratic : 0 ≤ lambda ^ 2 - lambda - 1 := by
      have htReal : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith
    by_contra hnot
    have hlt : lambda < Real.goldenRatio := lt_of_not_ge hnot
    have hleft : lambda - Real.goldenRatio < 0 := sub_neg.mpr hlt
    have hright : 0 < lambda - (1 - Real.goldenRatio) := by
      nlinarith [Real.one_lt_goldenRatio]
    have hfactor :
        lambda ^ 2 - lambda - 1 =
          (lambda - Real.goldenRatio) *
            (lambda - (1 - Real.goldenRatio)) := by
      nlinarith [Real.goldenRatio_sq]
    rw [hfactor] at hquadratic
    exact (not_lt_of_ge hquadratic) (mul_neg_of_neg_of_pos hleft hright)
  have positiveDeterminantBound :
      Matrix.det (M.map (Nat.cast : ℕ → ℤ)) = 1 →
        Real.goldenRatio ^ 2 ≤ lambda := by
    intro hdet
    have hdetReal :
        Matrix.det (M.map (Nat.cast : ℕ → ℝ)) = 1 := by
      rw [Matrix.det_fin_two] at hdet ⊢
      simp only [Matrix.map_apply] at hdet ⊢
      exact_mod_cast hdet
    rw [hdetReal] at hpoly
    let t : ℕ := M 0 0 + M 1 1
    have ht : 3 ≤ t := by
      by_contra hnot
      have htLe : t ≤ 2 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hnot)
      have htReal : (t : ℝ) ≤ 2 := by exact_mod_cast htLe
      nlinarith
    have hquadratic : 0 ≤ lambda ^ 2 - 3 * lambda + 1 := by
      have htReal : (3 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith
    by_contra hnot
    have hlt : lambda < Real.goldenRatio ^ 2 := lt_of_not_ge hnot
    have hleft : lambda - (Real.goldenRatio + 1) < 0 := by
      rw [← Real.goldenRatio_sq]
      exact sub_neg.mpr hlt
    have hright : 0 < lambda - (2 - Real.goldenRatio) := by
      nlinarith [Real.one_lt_goldenRatio]
    have hfactor :
        lambda ^ 2 - 3 * lambda + 1 =
          (lambda - (Real.goldenRatio + 1)) *
            (lambda - (2 - Real.goldenRatio)) := by
      nlinarith [Real.goldenRatio_sq]
    rw [hfactor] at hquadratic
    exact (not_lt_of_ge hquadratic) (mul_neg_of_neg_of_pos hleft hright)
  refine ⟨negativeDeterminantBound, positiveDeterminantBound, ?_, ?_⟩
  · dsimp
    refine ⟨by norm_num [Matrix.det_fin_two], ?_,
      Real.one_lt_goldenRatio, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [fibonacciSubstitution]
    · rw [Matrix.charpoly_fin_two]
      simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_add,
        Matrix.trace_fin_two, Matrix.det_fin_two]
  · dsimp
    have hmatrix :
        (!![(1 : ℕ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) ^ 2 =
          !![2, 1; 1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨hmatrix, ?_, ?_, ?_⟩
    · rw [hmatrix]
      norm_num [Matrix.det_fin_two]
    · nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    · rw [hmatrix, Matrix.charpoly_fin_two]
      simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Matrix.trace_fin_two, Matrix.det_fin_two]
      nlinarith [Real.goldenRatio_sq]

-- The claimed lower-bound conclusions are not unconditional order facts.
example : ¬ Real.goldenRatio ≤ (1 : ℝ) :=
  not_le_of_gt Real.one_lt_goldenRatio

example : ¬ Real.goldenRatio ^ 2 ≤ (1 : ℝ) := by
  nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]

#print axioms minimal_binary_unimodular_break

end D5.S3.Observer.GoldenCoding.MinimalBinaryUnimodularBreak
