/- GID: D5/S0/Tower/NonPisotFrontier/OrbitWitness
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotFrontier/OrbitWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The fourth conjugate iterate of one passes the escape threshold. -/

import D5.S0.Tower.NonPisotFrontier.ConjugateBridge

/- Library-search audit trail (2026-08-18):
   * Repository search found the base, its conjugate, the coordinate step and
     the threshold; nothing pins the greedy digits of one at this base.
   * The four digit bounds are wide, the tightest margin being about three
     tenths, so `3 < sqrt 13 < 4` suffices and no numeric approximation of the
     base is needed. -/

namespace D5.S0.Tower.NonPisotFrontier.OrbitWitness

open D5.S0.Tower.NonPisotFrontier.BetaThirteen

local notation "β" => betaThirteen
local notation "β'" => betaThirteenConjugate

/-- The first four greedy remainders of one, in coordinates against one and the
base.  Each is written as the integer pair the step map produces. -/
noncomputable def step1 : Real := -2 + 1 * β
noncomputable def step2 : Real := 3 + (-1 : Real) * β
noncomputable def step3 : Real := -4 + 2 * β
noncomputable def step4 : Real := 5 + (-2 : Real) * β

/-- The greedy digit at the first step is two: the base lies between two and
three, so multiplying one by it lands there. -/
theorem digit_one : 2 ≤ β * 1 ∧ β * 1 < 3 := by
  have h := sqrt_thirteen_bounds
  simp only [betaThirteen]
  constructor <;> linarith [h.1, h.2]

theorem step1_eq : β * 1 - 2 = step1 := by simp only [step1]; ring

/-- The second digit is zero. -/
theorem digit_two : 0 ≤ β * step1 ∧ β * step1 < 1 := by
  have hsq := sqrt_thirteen_sq
  have h := sqrt_thirteen_bounds
  simp only [step1, betaThirteen]
  constructor <;> nlinarith [hsq, h.1, h.2]

theorem step2_eq : β * step1 - 0 = step2 := by
  have hq := betaThirteen_quadratic
  have hexpand : β * (-2 + 1 * β) = -2 * β + β ^ 2 := by ring
  simp only [step1, step2]
  rw [hexpand, hq]; ring

/-- The third digit is one. -/
theorem digit_three : 1 ≤ β * step2 ∧ β * step2 < 2 := by
  have hsq := sqrt_thirteen_sq
  have h := sqrt_thirteen_bounds
  simp only [step2, betaThirteen]
  constructor <;> nlinarith [hsq, h.1, h.2]

theorem step3_eq : β * step2 - 1 = step3 := by
  have hq := betaThirteen_quadratic
  have hexpand : β * (3 + (-1 : Real) * β) = 3 * β - β ^ 2 := by ring
  simp only [step2, step3]
  rw [hexpand, hq]; ring

/-- The fourth digit is one. -/
theorem digit_four : 1 ≤ β * step3 ∧ β * step3 < 2 := by
  have hsq := sqrt_thirteen_sq
  have h := sqrt_thirteen_bounds
  simp only [step3, betaThirteen]
  constructor <;> nlinarith [hsq, h.1, h.2]

theorem step4_eq : β * step3 - 1 = step4 := by
  have hq := betaThirteen_quadratic
  have hexpand : β * (-4 + 2 * β) = -4 * β + 2 * β ^ 2 := by ring
  simp only [step3, step4]
  rw [hexpand, hq]; ring

/-- The conjugate of the fourth remainder, in closed form. -/
noncomputable def conjugateStep4 : Real := 5 + (-2 : Real) * β'

theorem conjugateStep4_eq : conjugateStep4 = 4 + Real.sqrt 13 := by
  simp only [conjugateStep4, betaThirteenConjugate]; ring

/-- The witness: after four greedy steps the conjugate coordinate has absolute
value four plus the square root of thirteen, which exceeds the escape threshold
three plus the square root of thirteen by exactly one. -/
theorem conjugate_step4_passes_threshold :
    3 + Real.sqrt 13 < |conjugateStep4| := by
  have hnn := sqrt_thirteen_nonneg
  have heq := conjugateStep4_eq
  rw [heq, abs_of_nonneg (by linarith)]
  linarith

/-- The four digits and the witness, packaged. -/
theorem first_four_digits_and_witness :
    (2 ≤ β * 1 ∧ β * 1 < 3) ∧
      (0 ≤ β * step1 ∧ β * step1 < 1) ∧
        (1 ≤ β * step2 ∧ β * step2 < 2) ∧
          (1 ≤ β * step3 ∧ β * step3 < 2) ∧
            conjugateStep4 = 4 + Real.sqrt 13 ∧
              3 + Real.sqrt 13 < |conjugateStep4| :=
  ⟨digit_one, digit_two, digit_three, digit_four, conjugateStep4_eq,
    conjugate_step4_passes_threshold⟩

end D5.S0.Tower.NonPisotFrontier.OrbitWitness
