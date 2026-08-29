/- GID: D5/S3/PrimeForms/Splitting/ThreeRingProfileFactorization
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Splitting/ThreeRingProfileFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The prime three-ring profile factors uniquely through units modulo sixty. -/

import D5.S3.PrimeForms.Splitting.ThreeRingProfileFibers
import Mathlib.NumberTheory.LSeries.PrimesInAP

/- Library-search audit trail (2026-08-25):
   * Repository searches found `triRingImage` as the canonical factored map on
     `(ZMod 60)ˣ`, but no named prime-side three-ring profile or factorization law.
   * Pinned Mathlib hit `ZMod.unitOfCoprime` constructs the unit residue of a
     prime coprime to sixty.
   * Pinned Mathlib hit `Nat.forall_exists_prime_gt_and_eq_mod` is Dirichlet's
     theorem and proves that prime reduction onto `(ZMod 60)ˣ` is surjective. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.Splitting.ThreeRingProfileFactorization

open D5.S3.PrimeForms.Splitting.ThreeRingProfileFibers

/-- The three-ring splitting profile of a prime unramified at two, three, and five. -/
def primeThreeRingProfile
    (p : {p : ℕ // p.Prime ∧ p.Coprime 60}) : ThreeRingProfile :=
  triRingImage (ZMod.unitOfCoprime p.1 p.2.2)

/-- The prime three-ring profile is the canonical unit-class image evaluated
at the prime's residue modulo sixty. -/
theorem prime_three_ring_profile_factors_mod_sixty
    (p : {p : ℕ // p.Prime ∧ p.Coprime 60}) :
    primeThreeRingProfile p =
      triRingImage (ZMod.unitOfCoprime p.1 p.2.2) :=
  rfl
#print axioms prime_three_ring_profile_factors_mod_sixty

/-- The canonical map on units modulo sixty is the unique map factoring the
three-ring profile of every prime coprime to sixty. Dirichlet's theorem supplies
a prime representative of each unit class. -/
theorem prime_three_ring_profile_factor_unique :
    ∃! factor : (ZMod 60)ˣ -> ThreeRingProfile,
      ∀ p : {p : ℕ // p.Prime ∧ p.Coprime 60},
        primeThreeRingProfile p =
          factor (ZMod.unitOfCoprime p.1 p.2.2) := by
  refine ⟨triRingImage, prime_three_ring_profile_factors_mod_sixty, ?_⟩
  intro factor hfactor
  funext unit
  obtain ⟨p, _, hpPrime, hpResidue⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod unit.isUnit 5
  have hpUnit : IsUnit (p : ZMod 60) := by
    rw [hpResidue]
    exact unit.isUnit
  have hpCoprime : p.Coprime 60 :=
    (ZMod.isUnit_iff_coprime p 60).mp hpUnit
  let prime : {p : ℕ // p.Prime ∧ p.Coprime 60} :=
    ⟨p, hpPrime, hpCoprime⟩
  have unitEquality : ZMod.unitOfCoprime prime.1 prime.2.2 = unit := by
    apply Units.ext
    simpa [prime] using hpResidue
  calc
    factor unit = factor (ZMod.unitOfCoprime prime.1 prime.2.2) :=
      congrArg factor unitEquality.symm
    _ = primeThreeRingProfile prime := (hfactor prime).symm
    _ = triRingImage (ZMod.unitOfCoprime prime.1 prime.2.2) :=
      prime_three_ring_profile_factors_mod_sixty prime
    _ = triRingImage unit := congrArg triRingImage unitEquality
#print axioms prime_three_ring_profile_factor_unique

example :
    (¬((2 : ℕ).Prime ∧ Nat.Coprime 2 60)) ∧
      (¬((3 : ℕ).Prime ∧ Nat.Coprime 3 60)) ∧
      ¬((5 : ℕ).Prime ∧ Nat.Coprime 5 60) := by
  decide

example :
    primeThreeRingProfile ⟨7, by decide⟩ =
      primeThreeRingProfile ⟨67, by decide⟩ := by
  decide

end D5.S3.PrimeForms.Splitting.ThreeRingProfileFactorization
