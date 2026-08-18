/- GID: D5/S0/Tower/NonPisotFrontier/BaseIdentification
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotFrontier/BaseIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frontier base and the older non-Pisot base are the same number. -/

import D5.S0.Tower.NonPisotFrontier.BetaThirteen
import D5.S0.Tower.NonPisot.Beta13

/- Library-search audit trail (2026-08-18):
   * `NonPisot/Beta13.lean` defines the positive root of `x^2 - x - 3` under the
     name `beta13`, thirty hours before `NonPisotFrontier/BetaThirteen.lean`
     defined it again as `betaThirteen`.  The two bodies are identical, so the
     identifications below hold by `rfl`.  Both modules are frozen, so the
     duplication cannot be removed; issue 2418 records it.
   * The search that should have found it is `Real.sqrt 13` or `x^2 - x - 3`,
     not the name about to be introduced.
   * Pinned Mathlib supplies `Irrational.ratCast_sub`; the irrationality itself
     is imported from the older module rather than reproved. -/

namespace D5.S0.Tower.NonPisotFrontier.BaseIdentification

open D5.S0.Tower.NonPisotFrontier.BetaThirteen
open D5.S0.Tower.NonPisot.Beta13

/-- The two names denote one number. -/
theorem betaThirteen_eq_beta13 : betaThirteen = beta13 := rfl

/-- So do the two names for its conjugate. -/
theorem betaThirteenConjugate_eq_beta13Conjugate :
    betaThirteenConjugate = beta13Conjugate := rfl

/-- The conjugate is one minus the base. -/
theorem conjugate_eq_one_sub : betaThirteenConjugate = 1 - betaThirteen := by
  simp only [betaThirteenConjugate, betaThirteen]
  ring

/-- Irrationality transported from the older module rather than reproved. -/
theorem betaThirteen_irrational : Irrational betaThirteen :=
  betaThirteen_eq_beta13 ▸ beta13_irrational

/-- Hence the conjugate is irrational too. -/
theorem betaThirteenConjugate_irrational : Irrational betaThirteenConjugate := by
  have h : Irrational (((1 : Rat) : Real) - betaThirteen) :=
    betaThirteen_irrational.ratCast_sub 1
  rw [conjugate_eq_one_sub]
  simpa using h

/-- The two developments describe one base, and it is irrational. -/
theorem the_two_bases_are_one :
    betaThirteen = beta13 ∧ betaThirteenConjugate = beta13Conjugate ∧
      Irrational betaThirteen ∧ Irrational betaThirteenConjugate :=
  ⟨betaThirteen_eq_beta13, betaThirteenConjugate_eq_beta13Conjugate,
    betaThirteen_irrational, betaThirteenConjugate_irrational⟩

end D5.S0.Tower.NonPisotFrontier.BaseIdentification
