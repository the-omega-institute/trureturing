/- GID: D5/S1/Digit/CompositeGasPronic
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A6 pronic classification of the integer points of the digit-gas root. -/

import D5.S1.Digit.CompositeGasBeta

namespace D5.S1.Digit

/-- A6, sufficient direction: every pronic parameter has the indicated integer root. -/
theorem e6_beta_pronic (m : ℕ) : e6Beta (m * (m + 1)) = m + 1 := by
  symm
  apply e6_beta_unique
  · positivity
  · push_cast
    ring

/--
A6: the digit-gas root is a natural number exactly at pronic parameters.
The endpoint `c = 0` is included by `m = 0`, giving `e6Beta 0 = 1` as in A3.
-/
theorem e6_beta_eq_nat_iff_pronic (c : ℕ) :
    (∃ n : ℕ, e6Beta c = (n : ℝ)) ↔ (∃ m : ℕ, c = m * (m + 1)) := by
  constructor
  · rintro ⟨n, hn⟩
    have hsq_real : (n : ℝ) ^ 2 = (n : ℝ) + (c : ℝ) := by
      simpa [hn] using e6_beta_sq c
    have hsq_nat : n ^ 2 = n + c := by
      exact_mod_cast hsq_real
    have hn_ge_one_real : (1 : ℝ) ≤ (n : ℝ) := by
      simpa [hn] using e6_beta_ge_one c
    have hn_ge_one : 1 ≤ n := by
      exact_mod_cast hn_ge_one_real
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn_ge_one
    have hn_succ : n = m + 1 := by omega
    subst n
    refine ⟨m, ?_⟩
    nlinarith [hsq_nat]
  · rintro ⟨m, rfl⟩
    refine ⟨m + 1, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using e6_beta_pronic m

@[simp] theorem e6_beta_six : e6Beta 6 = 3 := by
  have h := e6_beta_pronic 2
  norm_num at h
  exact h

@[simp] theorem e6_beta_twelve : e6Beta 12 = 4 := by
  have h := e6_beta_pronic 3
  norm_num at h
  exact h

end D5.S1.Digit
