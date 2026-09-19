/- GID: D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/LaymanDivisorPowerCongruenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.claim; result=D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.result; claim=D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.claim
   digest: The value 690 refutes Layman's three divisor-power congruence conjectures. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.LaymanDivisorPowerCongruenceRefutation

/-- Membership in OEIS A196226, with the intended evenness condition explicit. -/
def membership (m : ℕ) : Prop :=
  2 ∣ m ∧ ArithmeticFunction.sigma 1 m % m = 3 + m / 2

/-- The disjunction of Layman's three divisor-power congruence conjectures. -/
def claim : Prop :=
  (∀ m : ℕ, membership m ∧ m ≥ 14 →
      Nat.ModEq m (ArithmeticFunction.sigma 2 m) (5 + m / 2)) ∨
  (∀ m : ℕ, membership m ∧ m ≥ 22 →
      Nat.ModEq m (ArithmeticFunction.sigma 3 m) (9 + m / 2)) ∨
  (∀ m : ℕ, membership m ∧ m ≥ 38 →
      Nat.ModEq m (ArithmeticFunction.sigma 4 m) (17 + m / 2))

/-- The witness `m = 690` refutes each of the three conjectures. -/
theorem result : ¬ claim := by
  have hsigmaOne : ArithmeticFunction.sigma 1 690 = 1728 := by decide +kernel
  have hsigmaTwo : ArithmeticFunction.sigma 2 690 = 689000 := by decide +kernel
  have hsigmaThree : ArithmeticFunction.sigma 3 690 = 386358336 := by decide +kernel
  have hsigmaFour : ArithmeticFunction.sigma 4 690 = 244202442248 := by decide +kernel
  have hMembership : membership 690 := by
    norm_num [membership, hsigmaOne]
  intro hClaim
  rcases hClaim with hTwo | hThree | hFour
  · have h := hTwo 690 ⟨hMembership, by norm_num⟩
    rw [hsigmaTwo] at h
    norm_num [Nat.ModEq] at h
  · have h := hThree 690 ⟨hMembership, by norm_num⟩
    rw [hsigmaThree] at h
    norm_num [Nat.ModEq] at h
  · have h := hFour 690 ⟨hMembership, by norm_num⟩
    rw [hsigmaFour] at h
    norm_num [Nat.ModEq] at h

#print axioms membership
#print axioms claim
#print axioms result

end D5.S0.Certificates.LaymanDivisorPowerCongruenceRefutation
