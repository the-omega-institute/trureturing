/- GID: D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The symmetric Bernoulli bias laws are probability data on the closed bias range. -/

import D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder

/- Library-search audit trail (2026-09-03):
   * Repository search for public declarations mentioning `BiasLaw` returned no
     hits; the only declarations of this shape are two byte-identical `private`
     copies, in `SymmetricBernoulliSecondOrder` and in
     `FourLocalEvidenceClosedForms`, which imports the former.
   * Pinned Mathlib was searched for the two law names and for the two-point
     mass-function shape; this search found no upstream declaration. It does not
     exclude an equivalent generic upstream statement carrying another name.
   * No new primitive is introduced. The two laws are the frozen definitions of
     `SymmetricBernoulliSecondOrder`, used through the import above. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliProbabilityData

open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder

/-- The positive-bias law has unit mass, at every real bias. -/
theorem positiveBiasLaw_sum (delta : Real) : ∑ b, positiveBiasLaw delta b = 1 := by
  norm_num [positiveBiasLaw, Fintype.sum_bool]

/-- The negative-bias law has unit mass, at every real bias. -/
theorem negativeBiasLaw_sum (delta : Real) : ∑ b, negativeBiasLaw delta b = 1 := by
  norm_num [negativeBiasLaw, Fintype.sum_bool]

/-- The positive-bias law is nonnegative on the closed bias range. -/
theorem positiveBiasLaw_nonneg {delta : Real} (hdelta : |delta| <= 1 / 2) (b : Bool) :
    0 <= positiveBiasLaw delta b := by
  rw [abs_le] at hdelta
  cases b <;> simp only [positiveBiasLaw, Bool.false_eq_true, ↓reduceIte] <;> linarith

/-- The negative-bias law is nonnegative on the closed bias range. -/
theorem negativeBiasLaw_nonneg {delta : Real} (hdelta : |delta| <= 1 / 2) (b : Bool) :
    0 <= negativeBiasLaw delta b := by
  rw [abs_le] at hdelta
  cases b <;> simp only [negativeBiasLaw, Bool.false_eq_true, ↓reduceIte] <;> linarith

/-- Both symmetric Bernoulli bias laws are probability data on the closed bias
range.  This is the bundle that consumers destructure; the strict inequality
`|delta| < 1 / 2` under which it is currently re-derived is not needed. -/
theorem bias_laws_probability_data {delta : Real} (hdelta : |delta| <= 1 / 2) :
    ((forall b, 0 <= positiveBiasLaw delta b) /\
      ∑ b, positiveBiasLaw delta b = 1) /\
    ((forall b, 0 <= negativeBiasLaw delta b) /\
      ∑ b, negativeBiasLaw delta b = 1) :=
  ⟨⟨positiveBiasLaw_nonneg hdelta, positiveBiasLaw_sum delta⟩,
    ⟨negativeBiasLaw_nonneg hdelta, negativeBiasLaw_sum delta⟩⟩

end D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliProbabilityData
