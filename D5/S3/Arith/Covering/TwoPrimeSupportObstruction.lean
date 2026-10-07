/- GID: D5/S3/Arith/Covering/TwoPrimeSupportObstruction
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/TwoPrimeSupportObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A whole distinct cover cannot have a common modulus supported on only two odd primes. -/

import D5.S3.Arith.Congruence.TwoOddPrimeUncoveredDensity
import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

variable {L : ℕ}

open D5.S3.Arith.Congruence.TwoOddPrimeUncoveredDensity

/-- A whole cover cannot have a common modulus supported on only two distinct odd primes.

The imported density theorem already proves the finite two-prime obstruction.  This
bridge preserves the original modulus labels and the single covering source while
transporting the cover to the finite residue window. -/
theorem no_two_odd_prime_supported_common_modulus
    (S : OddDistinctCoveringSystem L)
    (p q A B : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q)
    (hpq : p ≠ q)
    (hcommon : S.commonModulus = p ^ A * q ^ B) : False := by
  classical
  let D : Finset ℕ := Finset.univ.image S.modulus
  let a : ℕ → ℕ := fun d =>
    if h : ∃ i : Fin L, S.modulus i = d then
      S.residue (Classical.choose h)
    else 0
  have hmoduli : ∀ d ∈ D, 1 < d ∧ d ∣ p ^ A * q ^ B := by
    intro d hd
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hd
    rw [← hi]
    constructor
    · exact S.modulus_one_lt i
    · rw [← hcommon]
      exact S.modulus_dvd_commonModulus i
  have ha_modulus (i : Fin L) :
      a (S.modulus i) % S.modulus i = S.residue i % S.modulus i := by
    dsimp [a]
    have hi : ∃ j : Fin L, S.modulus j = S.modulus i := by
      exact ⟨i, rfl⟩
    rw [dif_pos hi]
    have heq : Classical.choose hi = i := by
      apply S.modulus_injective
      exact Classical.choose_spec hi
    rw [heq]
  have hcover : ∀ x : Fin (p ^ A * q ^ B),
      ∃ d ∈ D, x.val % d = a d % d := by
    intro x
    obtain ⟨i, hxi⟩ := S.covers x.val
    refine ⟨S.modulus i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    have hxi' : x.val % S.modulus i = S.residue i % S.modulus i := hxi
    exact hxi'.trans (ha_modulus i).symm
  exact two_odd_prime_residue_classes_do_not_cover
    p q hp hq hpodd hqodd hpq A B D a hmoduli hcover

end Erdos7.OddDistinctCoveringSystem
