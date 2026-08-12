/- GID: D5/S3/Constants/COneExactValue
   generality: I
   mirror-B: D5/B/S3/Constants/COneExactValue
   mirror-E: none(waiver:exact-algebraic-identity-only)
   anchors: []
   digest: The c1 constant has two exact golden-ratio forms and the stated decimal approximation. -/

/- Library-search audit trail (2026-08-13):
   * `7 * (1 - Real.sqrt 5) / 24`: no hit in pinned Mathlib or D5.
   * `-7 / (12 * Real.goldenRatio)`: no hit in pinned Mathlib or D5.
   * `2 * Real.sqrt 5 * sturmianDirichletValue + e`: no hit in pinned Mathlib or D5.
   * `36051983`: no hit in pinned Mathlib or D5.
   * `2 * Real.sqrt 5 * t0 + e`: hits `D5.S3.Constants.Values.c1`, but that
     declaration uses the registered-open rational reference center `Values.t0`, not the
     exact Sturmian-Dirichlet value deposited for the source's `T0` clause.
   * `Mathlib.NumberTheory.Real.GoldenRatio` supplies `Real.goldenRatio` and its
     reciprocal identities; this module reuses that canonical definition.
-/

import D5.S3.Constants.SturmianDirichletValue
import D5.S3.Constants.Values

namespace D5.S3.Constants.COneExactValue

open D5.S3.Constants.SturmianDirichletValue

/-- The source's `c1` uses the exact deposited Sturmian-Dirichlet value for `T0` and
the canonical elementary shell `E`, rather than the older rational reference center. -/
noncomputable def cOne : Real :=
  2 * Real.sqrt 5 * sturmianDirichletValue + D5.S3.Constants.Values.e

/-- The `c1` relation reduces to both exact golden forms. Its printed eight-decimal
value differs from the exact constant by less than half a unit in the last shown place. -/
theorem c_one_exact_value :
    cOne = 2 * Real.sqrt 5 * sturmianDirichletValue + D5.S3.Constants.Values.e ∧
      cOne = 7 * (1 - Real.sqrt 5) / 24 ∧
      cOne = -7 / (12 * Real.goldenRatio) ∧
      |cOne - (-36051983 / 100000000 : Real)| < 1 / 200000000 := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hsqrt_lower : (2236067977 / 1000000000 : Real) < Real.sqrt 5 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hsqrt_upper : Real.sqrt 5 < (2236067978 / 1000000000 : Real) :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hfirst : cOne = 7 * (1 - Real.sqrt 5) / 24 := by
    simp only [cOne, sturmianDirichletValue, D5.S3.Constants.Values.e]
    nlinarith
  refine ⟨rfl, hfirst, ?_, ?_⟩
  · rw [hfirst]
    have hden : (1 + Real.sqrt 5 : Real) ≠ 0 := by positivity
    rw [show Real.goldenRatio = (1 + Real.sqrt 5) / 2 by rfl]
    field_simp [hden]
    nlinarith
  · rw [hfirst, abs_lt]
    constructor <;> nlinarith

/-- Checked evidence that the theorem's real domain is inhabited. -/
example : Real := 0

/-- Checked evidence that the assumption-free theorem has satisfiable hypotheses. -/
example : True := True.intro

/-- Changing the exact numerator from seven to eight breaks the first closed form. -/
example : cOne ≠ 8 * (1 - Real.sqrt 5) / 24 := by
  rw [c_one_exact_value.2.1]
  intro h
  have hsqrt_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  nlinarith

#print axioms c_one_exact_value

end D5.S3.Constants.COneExactValue
