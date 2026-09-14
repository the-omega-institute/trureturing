/- GID: D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Basic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.claim; result=D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.result; claim=D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.claim
   digest: The value 17 refutes Detlefs's four-residue characterization of 13-rough numbers. -/

import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.DetlefsRoughResidueCharacterizationRefutation

/-!
OEIS A008365 consists of the positive integers having no prime factor below
13. Gary Detlefs's comment of 2011-12-30 conjectures that these are exactly
the positive integers whose twenty-fourth powers modulo 2310 lie in the four
residue classes 1, 421, 631, and 841.

The prime 17 refutes only that proposed characterization: it is 13-rough,
while its twenty-fourth power has residue 1681 modulo 2310.
-/

/-- Every prime factor of `n` is at least 13. -/
def isRough13 (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → 13 ≤ p

/-- Membership in Detlefs's four proposed residue classes modulo 2310. -/
def inResidueSet (n : ℕ) : Prop :=
  n ^ 24 % 2310 = 1 ∨
    n ^ 24 % 2310 = 421 ∨
      n ^ 24 % 2310 = 631 ∨
        n ^ 24 % 2310 = 841

/-- Detlefs's proposed characterization of the positive 13-rough integers. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n → (isRough13 n ↔ inResidueSet n)

/-- The prime 17 is 13-rough, but its twenty-fourth power has residue 1681. -/
theorem result : ¬ claim := by
  intro hclaim
  have hrough : isRough13 17 := by
    intro p hp hdvd
    have h17prime : Nat.Prime 17 := by decide
    rcases h17prime.eq_one_or_self_of_dvd p hdvd with hpone | hpseventeen
    · exact (hp.ne_one hpone).elim
    · subst p
      decide
  have hresidue : 17 ^ 24 % 2310 = 1681 := by decide
  have hnotResidue : ¬ inResidueSet 17 := by
    unfold inResidueSet
    rw [hresidue]
    decide
  exact hnotResidue ((hclaim 17 (by decide)).mp hrough)

#print axioms isRough13
#print axioms inResidueSet
#print axioms claim
#print axioms result

end D5.S0.Certificates.DetlefsRoughResidueCharacterizationRefutation
