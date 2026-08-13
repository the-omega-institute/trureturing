/- GID: D5/S3/Factorization/BasicDiscriminantMinimum
   generality: G
   mirror-B: D5/B/S3/Factorization/BasicDiscriminantMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The least positive basic discriminant in the explicit odd squarefree class is five. -/

import Mathlib.Data.Nat.Squarefree

namespace D5.S3.Factorization.BasicDiscriminantMinimum

/-- The elementary positive discriminant predicate used for this partial closure. -/
def BasicDiscriminant (d : ℕ) : Prop :=
  1 < d ∧ Squarefree d ∧ d % 4 = 1

/-- Five belongs to the explicit positive odd squarefree discriminant class. -/
theorem five_basic_discriminant : BasicDiscriminant 5 := by
  unfold BasicDiscriminant
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hdiv
  have hpdiv : p ∣ 5 := dvd_trans (dvd_mul_left p p) hdiv
  have hp_le : p ≤ 5 := Nat.le_of_dvd (by norm_num) hpdiv
  have hp_cases : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by
    have hp_two : 2 ≤ p := hp.two_le
    omega
  rcases hp_cases with rfl | rfl | rfl | rfl <;> norm_num at hp hdiv

/-- Every member of the class has discriminant at least five. -/
theorem basic_discriminant_minimum {d : ℕ} (h : BasicDiscriminant d) : 5 ≤ d := by
  unfold BasicDiscriminant at h
  omega

end D5.S3.Factorization.BasicDiscriminantMinimum
