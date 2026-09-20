/- GID: D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/LaymanDivisorPowerCongruenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.Data.Nat.ModEq]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.claim; result=D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.result; claim=D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.claim
   digest: The value 690 refutes Layman's three divisor-power congruence conjectures. -/

/- Formalization classification:
   proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #8955)
   Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.LaymanDivisorPowerCongruenceRefutation

/-- `%N` of OEIS A196226: `A054024(m) = σ₁(m) mod m` equals `3 + m/2`; `3 + m/2` is an integer only for even `m`, so `2 ∣ m` is the entry's own domain. -/
def membership (m : ℕ) : Prop :=
  2 ∣ m ∧ ArithmeticFunction.sigma 1 m % m = 3 + m / 2

/-- Layman's Conjectures (1), (2), (3) of A196226 as one disjunction: thresholds 14, 22, 38 and constants 5, 9, 17 = 2^k + 1. -/
def claim : Prop :=
  (∀ m : ℕ, membership m ∧ m ≥ 14 →
      Nat.ModEq m (ArithmeticFunction.sigma 2 m) (5 + m / 2)) ∨
  (∀ m : ℕ, membership m ∧ m ≥ 22 →
      Nat.ModEq m (ArithmeticFunction.sigma 3 m) (9 + m / 2)) ∨
  (∀ m : ℕ, membership m ∧ m ≥ 38 →
      Nat.ModEq m (ArithmeticFunction.sigma 4 m) (17 + m / 2))

/-- `m = 690` refutes each of the three conjectures. -/
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

example : membership 690 := by
  have hsigmaOne : ArithmeticFunction.sigma 1 690 = 1728 := by decide +kernel
  norm_num [membership, hsigmaOne]

example :
    ArithmeticFunction.sigma 2 690 = 689000 ∧
      ArithmeticFunction.sigma 3 690 = 386358336 ∧
      ArithmeticFunction.sigma 4 690 = 244202442248 := by
  decide +kernel

#print axioms result

end D5.S0.Certificates.LaymanDivisorPowerCongruenceRefutation
