/- GID: D5/S0/Tower/NonPisotFrontier/BetaThirteen
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotFrontier/BetaThirteen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frontier base has a conjugate of modulus above one, so it is not Pisot. -/

import Mathlib.Analysis.Real.Sqrt

/- Library-search audit trail (2026-08-18):
   * Repository search found the d-bonacci Perron roots and their bounds, but
     no material on quadratic bases outside that family; the frontier base is
     not a d-bonacci root, since it satisfies a quadratic with constant term
     three.
   * Pinned Mathlib supplies `Real.sq_sqrt` and `Real.sqrt_lt_sqrt`; no Pisot
     predicate exists there, so the non-Pisot property is stated concretely as
     a modulus bound on the conjugate rather than through a definition. -/

namespace D5.S0.Tower.NonPisotFrontier.BetaThirteen

/-- The frontier base named in the source: the larger root of `x² = x + 3`. -/
noncomputable def betaThirteen : Real := (1 + Real.sqrt 13) / 2

/-- Its algebraic conjugate. -/
noncomputable def betaThirteenConjugate : Real := (1 - Real.sqrt 13) / 2

theorem sqrt_thirteen_sq : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)

theorem sqrt_thirteen_nonneg : 0 ≤ Real.sqrt 13 := Real.sqrt_nonneg 13

/-- Three is below the square root of thirteen, and the square root of thirteen
is below four.  Both are needed to bound the conjugate. -/
theorem sqrt_thirteen_bounds : 3 < Real.sqrt 13 ∧ Real.sqrt 13 < 4 := by
  have hsq := sqrt_thirteen_sq
  have hnn := sqrt_thirteen_nonneg
  constructor <;> nlinarith [hsq, hnn]

/-- Both roots satisfy the same quadratic. -/
theorem betaThirteen_quadratic : betaThirteen ^ 2 = betaThirteen + 3 := by
  have hsq := sqrt_thirteen_sq
  simp only [betaThirteen]
  nlinarith [hsq]

theorem betaThirteenConjugate_quadratic :
    betaThirteenConjugate ^ 2 = betaThirteenConjugate + 3 := by
  have hsq := sqrt_thirteen_sq
  simp only [betaThirteenConjugate]
  nlinarith [hsq]

/-- The base itself exceeds two, so it is not among the d-bonacci Perron roots,
every one of which lies below two. -/
theorem two_lt_betaThirteen : 2 < betaThirteen := by
  have h := sqrt_thirteen_bounds.1
  simp only [betaThirteen]
  linarith

/-- The conjugate is negative. -/
theorem betaThirteenConjugate_neg : betaThirteenConjugate < 0 := by
  have h := sqrt_thirteen_bounds.1
  simp only [betaThirteenConjugate]
  linarith

/-- The conjugate has modulus above one.  This is the precondition of the
frontier claim: a Pisot base has every conjugate of modulus below one, so this
base lies outside the Pisot region. -/
theorem one_lt_abs_betaThirteenConjugate : 1 < |betaThirteenConjugate| := by
  have hneg := betaThirteenConjugate_neg
  have h := sqrt_thirteen_bounds.1
  rw [abs_of_neg hneg]
  simp only [betaThirteenConjugate]
  linarith

/-- The frontier base is outside the Pisot region and outside the d-bonacci
family, stated as one proposition. -/
theorem betaThirteen_is_outside_the_pisot_region :
    betaThirteen ^ 2 = betaThirteen + 3 ∧
      2 < betaThirteen ∧
      betaThirteenConjugate ^ 2 = betaThirteenConjugate + 3 ∧
      1 < |betaThirteenConjugate| :=
  ⟨betaThirteen_quadratic, two_lt_betaThirteen,
    betaThirteenConjugate_quadratic, one_lt_abs_betaThirteenConjugate⟩

end D5.S0.Tower.NonPisotFrontier.BetaThirteen
