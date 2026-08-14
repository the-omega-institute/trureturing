/- GID: D5/S3/DivergenceSupport/LandauerSaturation
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/LandauerSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize Landauer slack, saturation, and strictness from nonnegative remainders. -/

import D5.S3.DivergenceSupport.LandauerBound
import D5.S3.DivergenceSupport.LandauerIdentity

/-!
# Landauer bound saturation

The exact balance makes the slack in the Landauer bound equal to the sum of its mutual-information
and divergence remainders. Under their nonnegativity hypotheses, equality is therefore equivalent
to both remainders vanishing. Strictness is equivalent to their sum being positive.

Library-search audit trail (2026-08-14):

* A repository-wide Lean search found no existing Landauer slack, saturation, equality criterion,
  or strictness theorem. The frozen modules provide only the balance identity and lower bound.
* Pinned mathlib contains `add_eq_zero_iff_of_nonneg` and `sub_eq_zero`. Its `add_pos_iff` requires
  a canonically ordered additive monoid and does not apply to `Real`.
* Pinned mathlib contains no Landauer-specific saturation theorem.

Saturation here means that no residual mutual information and no reservoir divergence remain.
However, this module proves only consequences of a real-number balance. It does not model a physical
process, derive the balance from dynamics, or establish that variables named `mutualInfo` and
`divergence` are the physical quantities suggested by their names.
-/

namespace D5.S3.DivergenceSupport.LandauerSaturation

/-- The slack in the Landauer bound is exactly the sum of the two discarded remainders. -/
theorem landauer_slack_of_balance
    (beta heat entropyChange mutualInfo divergence : Real)
    (hbalance : beta * heat = -entropyChange + mutualInfo + divergence) :
    beta * heat - (-entropyChange) = mutualInfo + divergence := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  linarith

/-- Equality in the bound is equivalent to the sum of the two remainders vanishing. -/
theorem landauer_saturation_sum_iff
    (beta heat entropyChange mutualInfo divergence : Real)
    (hbalance : beta * heat = -entropyChange + mutualInfo + divergence) :
    -entropyChange = beta * heat ↔ mutualInfo + divergence = 0 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  fail_if_success linarith
  have hslack := landauer_slack_of_balance
    beta heat entropyChange mutualInfo divergence hbalance
  constructor
  · intro hsaturated
    linarith
  · intro hremainder
    linarith

/-- Under nonnegativity, equality holds exactly when both discarded remainders vanish. -/
theorem landauer_saturation_iff
    (beta heat entropyChange mutualInfo divergence : Real)
    (hbalance : beta * heat = -entropyChange + mutualInfo + divergence)
    (hmutualInfo : 0 <= mutualInfo) (hdivergence : 0 <= divergence) :
    -entropyChange = beta * heat ↔ mutualInfo = 0 ∧ divergence = 0 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  fail_if_success linarith
  rw [landauer_saturation_sum_iff
    beta heat entropyChange mutualInfo divergence hbalance]
  exact add_eq_zero_iff_of_nonneg hmutualInfo hdivergence

/-- The bound is strict exactly when the sum of the discarded remainders is positive. -/
theorem landauer_strict_iff
    (beta heat entropyChange mutualInfo divergence : Real)
    (hbalance : beta * heat = -entropyChange + mutualInfo + divergence)
    (hmutualInfo : 0 <= mutualInfo) (hdivergence : 0 <= divergence) :
    -entropyChange < beta * heat ↔ 0 < mutualInfo + divergence := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  fail_if_success linarith
  have hbound :=
    D5.S3.DivergenceSupport.LandauerBound.landauer_bound_of_balance
      beta heat entropyChange mutualInfo divergence hbalance hmutualInfo hdivergence
  have hslack := landauer_slack_of_balance
    beta heat entropyChange mutualInfo divergence hbalance
  constructor
  · intro hstrict
    linarith
  · intro hremainder
    have hne : Ne (-entropyChange) (beta * heat) := by
      intro heq
      linarith
    exact lt_of_le_of_ne hbound hne

/- The balance can be saturated: all target variables may be zero. -/
example :
    ∃ beta heat entropyChange mutualInfo divergence : Real,
      beta * heat = -entropyChange + mutualInfo + divergence ∧
      mutualInfo = 0 ∧ divergence = 0 ∧
      -entropyChange = beta * heat := by
  refine ⟨0, 0, 0, 0, 0, ?_⟩
  have hbalance : (0 : Real) * 0 = -(0 : Real) + 0 + 0 :=
    D5.S3.DivergenceSupport.LandauerIdentity.landauer_identity_from_balances
      0 0 0 0 0 0 (by norm_num) (by norm_num)
  have hsaturation : -(0 : Real) = (0 : Real) * 0 :=
    (landauer_saturation_iff 0 0 0 0 0 hbalance (by norm_num) (by norm_num)).2
      ⟨rfl, rfl⟩
  exact ⟨hbalance, rfl, rfl, hsaturation⟩

/- The balance can be strict: a unit mutual-information remainder supplies a unit slack. -/
example :
    ∃ beta heat entropyChange mutualInfo divergence : Real,
      beta * heat = -entropyChange + mutualInfo + divergence ∧
      0 < mutualInfo ∧ divergence = 0 ∧
      -entropyChange < beta * heat := by
  refine ⟨1, 1, 0, 1, 0, ?_⟩
  have hbalance : (1 : Real) * 1 = -(0 : Real) + 1 + 0 :=
    D5.S3.DivergenceSupport.LandauerIdentity.landauer_identity_from_balances
      1 1 0 1 1 0 (by norm_num) (by norm_num)
  have hstrict : -(0 : Real) < (1 : Real) * 1 :=
    (landauer_strict_iff 1 1 0 1 0 hbalance (by norm_num) (by norm_num)).2
      (by norm_num)
  exact ⟨hbalance, by norm_num, rfl, hstrict⟩

#print axioms landauer_slack_of_balance
#print axioms landauer_saturation_sum_iff
#print axioms landauer_saturation_iff
#print axioms landauer_strict_iff

end D5.S3.DivergenceSupport.LandauerSaturation
