/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Tridiagonal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Tridiagonal
   mirror-E: none(waiver:formal-tridiagonal-coefficient-construction)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic,mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Coefficient recursion constructs the unique valuation-bounded tridiagonal solution. -/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Tridiagonal

noncomputable def tridiagonalRow (index : ℕ) :
    PowerSeries ℚ × PowerSeries ℚ × PowerSeries ℚ :=
  (-2 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
      2 * PowerSeries.X ^ (index + 2),
    PowerSeries.X * (1 - PowerSeries.X ^ (index + 1)),
    PowerSeries.X ^ 2 * (1 - PowerSeries.X ^ index))

noncomputable def tridiagonalCoefficient (degree index : ℕ) : ℚ :=
  PowerSeries.coeff degree
      ((1 - PowerSeries.X ^ 2) ^ 2 * PowerSeries.X ^ (2 * index) : PowerSeries ℚ) -
    ∑ earlier : Fin degree,
      (PowerSeries.coeff (degree - earlier.val) (tridiagonalRow index).1 *
          tridiagonalCoefficient earlier.val index +
        PowerSeries.coeff (degree - earlier.val) (tridiagonalRow index).2.1 *
          tridiagonalCoefficient earlier.val (index + 1) +
        PowerSeries.coeff (degree - earlier.val) (tridiagonalRow index).2.2 *
          tridiagonalCoefficient earlier.val (index - 1))
termination_by degree
decreasing_by all_goals exact Fin.is_lt _

noncomputable def tridiagonalSeries (index : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun degree => tridiagonalCoefficient degree index

theorem tridiagonal_solution :
    (∀ index : ℕ, (PowerSeries.X : PowerSeries ℚ) ^ index ∣ tridiagonalSeries index) ∧
    (∀ index : ℕ,
      (1 + (tridiagonalRow index).1) * tridiagonalSeries index +
        (tridiagonalRow index).2.1 * tridiagonalSeries (index + 1) +
        (tridiagonalRow index).2.2 * tridiagonalSeries (index - 1) =
          (1 - PowerSeries.X ^ 2) ^ 2 * PowerSeries.X ^ (2 * index)) ∧
    (∀ candidate : ℕ → PowerSeries ℚ,
      (∀ index : ℕ,
        (1 + (tridiagonalRow index).1) * candidate index +
          (tridiagonalRow index).2.1 * candidate (index + 1) +
          (tridiagonalRow index).2.2 * candidate (index - 1) =
            (1 - PowerSeries.X ^ 2) ^ 2 * PowerSeries.X ^ (2 * index)) →
        candidate = tridiagonalSeries) := by
  classical
  have hconvolution (series factor : PowerSeries ℚ)
      (hzero : PowerSeries.coeff 0 factor = 0) (degree : ℕ) :
      PowerSeries.coeff degree (factor * series) =
        ∑ earlier : Fin degree,
          PowerSeries.coeff (degree - earlier.val) factor *
            PowerSeries.coeff earlier.val series := by
    rw [mul_comm factor series, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    simp only [Nat.sub_self, hzero, mul_zero, add_zero]
    rw [Fin.sum_univ_eq_sum_range
      (fun earlier => PowerSeries.coeff (degree - earlier) factor *
        PowerSeries.coeff earlier series) degree]
    apply Finset.sum_congr rfl
    intro earlier hearlier
    exact mul_comm _ _
  have hrowZero (index : ℕ) :
      PowerSeries.coeff 0 (tridiagonalRow index).1 = 0 ∧
      PowerSeries.coeff 0 (tridiagonalRow index).2.1 = 0 ∧
      PowerSeries.coeff 0 (tridiagonalRow index).2.2 = 0 := by
    simp [tridiagonalRow, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hrecurrence (index : ℕ) :
      (1 + (tridiagonalRow index).1) * tridiagonalSeries index +
        (tridiagonalRow index).2.1 * tridiagonalSeries (index + 1) +
        (tridiagonalRow index).2.2 * tridiagonalSeries (index - 1) =
          (1 - PowerSeries.X ^ 2) ^ 2 * PowerSeries.X ^ (2 * index) := by
    apply PowerSeries.ext
    intro degree
    simp only [add_mul, one_mul, map_add,
      hconvolution _ _ (hrowZero index).1 degree,
      hconvolution _ _ (hrowZero index).2.1 degree,
      hconvolution _ _ (hrowZero index).2.2 degree,
      tridiagonalSeries, PowerSeries.coeff_mk]
    rw [tridiagonalCoefficient]
    simp only [Finset.sum_add_distrib]
    ring
  have hsupport (degree index : ℕ) (hlarge : degree < index) :
      tridiagonalCoefficient degree index = 0 := by
    induction degree using Nat.strong_induction_on generalizing index with
    | h degree ih =>
        have hforce : PowerSeries.coeff degree
            ((1 - PowerSeries.X ^ 2) ^ 2 * PowerSeries.X ^ (2 * index) :
              PowerSeries ℚ) = 0 := by
          rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
        rw [tridiagonalCoefficient, hforce]
        have hsum : (∑ earlier : Fin degree,
            (PowerSeries.coeff (degree - earlier.val) (tridiagonalRow index).1 *
                tridiagonalCoefficient earlier.val index +
              PowerSeries.coeff (degree - earlier.val) (tridiagonalRow index).2.1 *
                tridiagonalCoefficient earlier.val (index + 1) +
              PowerSeries.coeff (degree - earlier.val) (tridiagonalRow index).2.2 *
                tridiagonalCoefficient earlier.val (index - 1))) = 0 := by
          apply Finset.sum_eq_zero
          intro earlier hearlier
          have hlt := earlier.isLt
          rw [ih earlier.val hlt index (by omega),
            ih earlier.val hlt (index + 1) (by omega),
            ih earlier.val hlt (index - 1) (by omega)]
          simp
        rw [hsum]
        ring
  refine ⟨?_, hrecurrence, ?_⟩
  · intro index
    rw [PowerSeries.X_pow_dvd_iff]
    intro degree hdegree
    simpa only [tridiagonalSeries, PowerSeries.coeff_mk] using
      hsupport degree index hdegree
  · intro candidate hcandidate
    have hcoefficients (degree index : ℕ) :
        PowerSeries.coeff degree (candidate index) =
          PowerSeries.coeff degree (tridiagonalSeries index) := by
      induction degree using Nat.strong_induction_on generalizing index with
      | h degree ih =>
          have hcandidateCoeff := congrArg (PowerSeries.coeff degree) (hcandidate index)
          have hsolutionCoeff := congrArg (PowerSeries.coeff degree) (hrecurrence index)
          simp only [add_mul, one_mul, map_add,
            hconvolution _ _ (hrowZero index).1 degree,
            hconvolution _ _ (hrowZero index).2.1 degree,
            hconvolution _ _ (hrowZero index).2.2 degree]
              at hcandidateCoeff hsolutionCoeff
          have hearlier (earlier : Fin degree) (neighbor : ℕ) :
              PowerSeries.coeff earlier.val (candidate neighbor) =
                PowerSeries.coeff earlier.val (tridiagonalSeries neighbor) :=
            ih earlier.val earlier.isLt neighbor
          simp_rw [hearlier] at hcandidateCoeff
          linear_combination hcandidateCoeff - hsolutionCoeff
    funext index
    exact PowerSeries.ext fun degree => hcoefficients degree index

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Tridiagonal
