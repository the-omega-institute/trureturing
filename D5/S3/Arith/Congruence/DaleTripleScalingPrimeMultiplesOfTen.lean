/- GID: D5/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Tactic.NormNum.Prime]
   utility: none
   digest: Four prime values at successive powers-of-three scalings force k to be four or a multiple of ten. -/

import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.Congruence.DaleTripleScalingPrimeMultiplesOfTen

/-- Harvey P. Dale's 2015 conjecture for OEIS A112041. -/
def claim : Prop :=
  forall k : Nat, 0 < k ->
    (Nat.Prime (k + 1) /\ Nat.Prime (3 * k + 1) /\
      Nat.Prime (9 * k + 1) /\ Nat.Prime (27 * k + 1)) ->
    k = 4 \/ 10 ∣ k

/-- The parity and residue classes modulo five settle Dale's conjecture. -/
theorem result : claim := by
  intro k hk hprime
  rcases hprime with ⟨hp1, hp3, hp9, hp27⟩
  have hk_mod_two : k % 2 = 0 := by
    rcases hp1.eq_two_or_odd with htwo | hodd
    · have hk_one : k = 1 := by omega
      subst k
      exact ((by decide : ¬ Nat.Prime (3 * 1 + 1)) hp3).elim
    · omega
  by_cases hzero : k % 5 = 0
  · right
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have hclasses :
      k % 5 = 1 \/ k % 5 = 2 \/ k % 5 = 3 \/ k % 5 = 4 := by
    have hlt := Nat.mod_lt k (by decide : 0 < 5)
    omega
  rcases hclasses with hone | htwo | hthree | hfour
  · have hdvd : 5 ∣ 9 * k + 1 := by omega
    have heq : 5 = 9 * k + 1 :=
      (hp9.eq_one_or_self_of_dvd 5 hdvd).resolve_left (by decide)
    omega
  · have hdvd : 5 ∣ 27 * k + 1 := by omega
    have heq : 5 = 27 * k + 1 :=
      (hp27.eq_one_or_self_of_dvd 5 hdvd).resolve_left (by decide)
    omega
  · have hdvd : 5 ∣ 3 * k + 1 := by omega
    have heq : 5 = 3 * k + 1 :=
      (hp3.eq_one_or_self_of_dvd 5 hdvd).resolve_left (by decide)
    omega
  · left
    have hdvd : 5 ∣ k + 1 := by omega
    have heq : 5 = k + 1 :=
      (hp1.eq_one_or_self_of_dvd 5 hdvd).resolve_left (by decide)
    omega

#print axioms claim
#print axioms result

end D5.S3.Arith.Congruence.DaleTripleScalingPrimeMultiplesOfTen
