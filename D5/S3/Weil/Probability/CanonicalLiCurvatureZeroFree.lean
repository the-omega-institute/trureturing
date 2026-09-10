/- GID: D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/CanonicalLiCurvatureZeroFree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual normalized canonical Li second differences have an explicit finite Toeplitz-to-growth-to-RH proof with no external Li criterion. -/

import D5.S3.Weil.Probability.CanonicalLiGrowthZeroFree
import D5.S3.Weil.TestFunctions.LiCurvatureCriterion
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases

/-!
Only canonicalLiCoefficient is used; it is imported from the merged owner.
The new curvature definition is its normalized second difference, including
normalization at zero. The finite matrix calculation is a direct two-point
compression of the existing toeplitzMatrix. It never infers positive
definiteness of an arbitrary sequence from bounds on its individual entries.

Bounded actual second differences imply an all-index quadratic bound by two
finite inductions. The preceding actual-xi analytic continuation consumes that
bound. Arithmetic boundedness or positivity remains an input, not a conclusion.
The classical growth criterion is not claimed as new mathematics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.CanonicalLiCurvatureZeroFree

open Matrix
open D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open D5.S3.Weil.Probability.CanonicalLiGrowthZeroFree
open scoped BigOperators ComplexOrder

/-- The actual canonical curvature, with its even integer extension. -/
def canonicalLiCurvature (n : ℤ) : ℂ :=
  if n = 0 then 1 else
    (((canonicalLiCoefficient (n.natAbs + 1) - 2 * canonicalLiCoefficient n.natAbs +
      canonicalLiCoefficient (n.natAbs - 1)) / (2 * canonicalLiCoefficient 1) : ℝ) : ℂ)

@[simp] theorem canonical_li_curvature_zero : canonicalLiCurvature 0 = 1 := by
  simp [canonicalLiCurvature]

/-- Bounded second differences give a quadratic envelope by controlling each
successive first difference. No positivity of L beyond its absolute bounds is
required, and every index, rather than a finite prefix, is covered. -/
theorem quadratic_of_bounded_second_difference (L : ℕ → ℝ) (a : ℝ)
    (zeroValue : L 0 = 0) (first : |L 1| ≤ a)
    (second : ∀ n : ℕ, 1 ≤ n →
      |L (n + 1) - 2 * L n + L (n - 1)| ≤ 2 * a) :
    ∀ n : ℕ, |L n| ≤ a * (n : ℝ) ^ 2 := by
  have increment (n : ℕ) : |L (n + 1) - L n| ≤ a * (2 * (n : ℝ) + 1) := by
    induction n with
    | zero => simpa [zeroValue] using first
    | succ n ih =>
        have hs := second (n + 1) (by omega)
        have identity : L (n + 1 + 1) - L (n + 1) =
            (L (n + 1) - L n) +
              (L (n + 1 + 1) - 2 * L (n + 1) + L (n + 1 - 1)) := by
          rw [show n + 1 - 1 = n by omega]
          ring
        calc
          _ = |(L (n + 1) - L n) +
              (L (n + 1 + 1) - 2 * L (n + 1) + L (n + 1 - 1))| := by rw [identity]
          _ ≤ |L (n + 1) - L n| +
              |L (n + 1 + 1) - 2 * L (n + 1) + L (n + 1 - 1)| := abs_add_le _ _
          _ ≤ a * (2 * (n : ℝ) + 1) + 2 * a := add_le_add ih hs
          _ = _ := by push_cast; ring
  intro n
  induction n with
  | zero => simp [zeroValue]
  | succ n ih =>
      calc
        |L (n + 1)| = |L n + (L (n + 1) - L n)| := by congr 1; ring
        _ ≤ |L n| + |L (n + 1) - L n| := abs_add_le _ _
        _ ≤ a * (n : ℝ) ^ 2 + a * (2 * (n : ℝ) + 1) := add_le_add ih (increment n)
        _ = _ := by push_cast; ring

/-- The actual arithmetic second differences alone suffice for the analytic
RH implication. This does not assume all Li coefficients nonnegative. -/
theorem canonical_li_second_difference_bound_implies_rh
    (second : ∀ n : ℕ, 1 ≤ n →
      |canonicalLiCoefficient (n + 1) - 2 * canonicalLiCoefficient n +
        canonicalLiCoefficient (n - 1)| ≤ 2 * canonicalLiCoefficient 1) :
    RiemannHypothesis := by
  apply canonical_li_quadratic_growth_implies_rh (canonicalLiCoefficient 1)
  exact quadratic_of_bounded_second_difference canonicalLiCoefficient (canonicalLiCoefficient 1)
    canonical_li_zero (by rw [abs_of_pos canonical_li_one_pos]) second

/-- At order n, two actual endpoint test vectors extract the required canonical
second-difference bound. This uses only a two-point principal compression. -/
theorem canonical_curvature_second_difference_bound
    (positive : ∀ N : ℕ, (toeplitzMatrix canonicalLiCurvature N).PosSemidef)
    (n : ℕ) (hn : 1 ≤ n) :
    |canonicalLiCoefficient (n + 1) - 2 * canonicalLiCoefficient n +
      canonicalLiCoefficient (n - 1)| ≤ 2 * canonicalLiCoefficient 1 := by
  have hn0 : n ≠ 0 := by omega
  let d : ℝ := (canonicalLiCoefficient (n + 1) - 2 * canonicalLiCoefficient n +
    canonicalLiCoefficient (n - 1)) / (2 * canonicalLiCoefficient 1)
  let pick : Fin 2 → Fin (n + 1) := fun i => if i = 0 then 0 else ⟨n, Nat.lt_succ_self n⟩
  have compressed := (positive n).submatrix pick
  have entries : (toeplitzMatrix canonicalLiCurvature n).submatrix pick pick =
      (fun i j : Fin 2 => if i = j then (1 : ℂ) else (d : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.submatrix, toeplitzMatrix, pick, canonicalLiCurvature, hn0, d]
  rw [entries] at compressed
  have plus := compressed.re_dotProduct_nonneg (fun _ : Fin 2 => (1 : ℂ))
  have minus := compressed.re_dotProduct_nonneg (fun i : Fin 2 => if i = 0 then (1 : ℂ) else -1)
  norm_num [dotProduct, mulVec, Fin.sum_univ_two, Pi.star_apply] at plus minus
  have unitBound : |d| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have denominator : 0 < 2 * canonicalLiCoefficient 1 := by linarith [canonical_li_one_pos]
  have divided : |canonicalLiCoefficient (n + 1) - 2 * canonicalLiCoefficient n +
      canonicalLiCoefficient (n - 1)| / (2 * canonicalLiCoefficient 1) ≤ 1 := by
    simpa only [d, abs_div, abs_of_pos denominator] using unitBound
  exact (div_le_one denominator).mp divided

/-- All Toeplitz orders of the actual derivative-defined normalized curvature
imply Mathlib RiemannHypothesis, without any externally supplied Li criterion,
Herglotz representation, recurrence or zero-measure identification. -/
theorem canonical_curvature_posSemidef_implies_rh
    (positive : ∀ N : ℕ, (toeplitzMatrix canonicalLiCurvature N).PosSemidef) :
    RiemannHypothesis :=
  canonical_li_second_difference_bound_implies_rh
    (canonical_curvature_second_difference_bound positive)

/-- A failed RH forces a finite order at which the actual canonical curvature
Toeplitz condition fails. No bound on that order is asserted. -/
theorem not_rh_forces_canonical_curvature_failure (failure : ¬ RiemannHypothesis) :
    ∃ N : ℕ, ¬ (toeplitzMatrix canonicalLiCurvature N).PosSemidef := by
  by_contra! positive
  exact failure (canonical_curvature_posSemidef_implies_rh positive)

#print axioms quadratic_of_bounded_second_difference
#print axioms canonical_curvature_second_difference_bound
#print axioms canonical_curvature_posSemidef_implies_rh

end D5.S3.Weil.Probability.CanonicalLiCurvatureZeroFree
