/- GID: D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation
   mirror-E: none(waiver:symbolic-refutation-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Basic]
   utility: none
   digest: Residue five modulo six forbids every Vos Post log-bounded partition. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.Congruence.VosPostLogBoundedSemiprimePartitionRefutation

/-- A representation of `m` as a prime plus a semiprime, with the prime
bounded by the natural logarithm of the smaller semiprime factor. -/
def Rep (m : ℕ) : Prop :=
  ∃ p q r : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      m = p + q * r ∧
        (p : ℝ) ≤ Real.log ((min q r : ℕ) : ℝ)

/-- The weakest eventual form of Jonathan Vos Post's 2004 OEIS A100952
conjecture, including its allowance for a larger threshold than 60. -/
def claim : Prop :=
  ∃ B : ℕ, 60 ≤ B ∧ ∀ m : ℕ, B < m → Rep m

private theorem not_rep_six_mul_add_five (t : ℕ) :
    ¬ Rep (6 * t + 5) := by
  rintro ⟨p, q, r, hp, hq, hr, hsum, hlog⟩
  have hmin_two : 2 ≤ min q r := le_min hq.two_le hr.two_le
  have hmin_gt_three : 3 < min q r := by
    by_contra h
    have hmin_le_three : min q r ≤ 3 := by omega
    have hmin_pos : (0 : ℝ) < ((min q r : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < min q r by omega)
    have hmin_ne_one : ((min q r : ℕ) : ℝ) ≠ 1 := by
      exact_mod_cast (show min q r ≠ 1 by omega)
    have hlog_strict := Real.log_lt_sub_one_of_pos hmin_pos hmin_ne_one
    have hp_two : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hmin_cast : (((min q r : ℕ) : ℝ)) ≤ 3 := by
      exact_mod_cast hmin_le_three
    linarith
  have hq_gt_three : 3 < q := hmin_gt_three.trans_le (min_le_left q r)
  have hr_gt_three : 3 < r := hmin_gt_three.trans_le (min_le_right q r)
  have hq_mod_two : q % 2 = 1 :=
    hq.eq_two_or_odd.resolve_left (by omega)
  have hr_mod_two : r % 2 = 1 :=
    hr.eq_two_or_odd.resolve_left (by omega)
  have hp_two : p = 2 := by
    rcases hp.eq_two_or_odd with hp_two | hp_mod_two
    · exact hp_two
    · have hsum_mod := congrArg (fun n : ℕ => n % 2) hsum
      norm_num [Nat.add_mod, Nat.mul_mod, hp_mod_two, hq_mod_two, hr_mod_two] at hsum_mod
  have hthree_dvd : 3 ∣ q * r := by
    refine ⟨2 * t + 1, ?_⟩
    omega
  rcases Nat.Prime.dvd_mul Nat.prime_three |>.mp hthree_dvd with hq_three | hr_three
  · have : 3 = q :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp hq_three
    omega
  · have : 3 = r :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp hr_three
    omega

/-- Vos Post's eventual logarithmically bounded semiprime-partition conjecture
is false, even when equal semiprime factors are allowed. -/
theorem result : ¬ claim := by
  rintro ⟨B, _, hrep⟩
  exact not_rep_six_mul_add_five (B + 10)
    (hrep (6 * (B + 10) + 5) (by omega))

#print axioms result

end D5.S3.Arith.Congruence.VosPostLogBoundedSemiprimePartitionRefutation
