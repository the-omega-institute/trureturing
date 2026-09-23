/- GID: D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.claim; result=D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.result; claim=D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.claim
   digest: The integer 6 refutes the published divisor-weighted divergence lower bound. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.ZelinskyZhangConjectureTwentyTwoRefutation

noncomputable section

/-- The divisor-weighted logarithmic sum defined by Zelinsky and Zhang. -/
def v (n : Nat) : Real :=
  ∑ d ∈ (Nat.divisors n).filter (fun d => 1 < d),
    (1 / (d : Real)) *
      Real.log (((((Nat.divisors n).card - 1 : Nat) : Real)) / (d : Real))

/-- Zelinsky and Zhang's Conjecture 22, including all twelve stated exclusions. -/
def claim : Prop :=
  ∀ n : Nat,
    0 < n →
    n ∉ ({1, 12, 24, 30, 36, 48, 60, 72, 120, 180, 240, 360} : Finset Nat) →
    1 / ((Nat.minFac n : Real) ^ 2) ≤ v n

/-- The integer `6` refutes Conjecture 22. -/
theorem result : ¬ claim := by
  intro hclaim
  have h6 := hclaim 6 (by norm_num) (by norm_num)
  have hdivisors : Nat.divisors 6 = {1, 2, 3, 6} := by
    decide +kernel
  have hminFac : Nat.minFac 6 = 2 := by
    norm_num
  have h32 : Real.log (3 / 2 : Real) < 1 / 2 := by
    have h := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : Real) < 3 / 2)
      (by norm_num : (3 / 2 : Real) ≠ 1)
    norm_num at h ⊢
    exact h
  have h12 : Real.log (1 / 2 : Real) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  rw [v, hdivisors, hminFac] at h6
  norm_num [Finset.sum_filter, Finset.sum_insert] at h6
  linarith

end

end D5.S0.Certificates.ZelinskyZhangConjectureTwentyTwoRefutation
