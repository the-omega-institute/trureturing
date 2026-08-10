/- GID: D5/S3/ArithUnits/PrimeModInverse
   generality: G
   mirror-B: D5/B/S3/ArithUnits/PrimeModInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A natural number not divisible by a prime is a unit modulo that prime. -/

/- Library-search audit trail (2026-08-11):
   * Repository searches for `prime_not_dvd_is_unit`, `not_dvd.*isUnit`,
     `isUnit.*not_dvd`, and invertibility in `ZMod` found no theorem or Blueprint with the
     exact signature below.
   * Repository HIT: `PrimeModUnit.prime_modulus_is_unit_iff_ne_zero` characterizes all units
     modulo a prime as nonzero residues. `FermatLittle.fermat_little_theorem` uses the same
     nondivisibility premise but has a modular-congruence conclusion, not an `IsUnit` conclusion.
   * Pinned-mathlib searches for `isUnit_iff_coprime`, `coprime_iff_not_dvd`,
     `isUnit_prime_iff_not_dvd`, `isUnit_prime_of_not_dvd`, and
     `isUnit_natCast_iff_not_dvd_pow` found the two exact bridge lemmas used below:
     `ZMod.isUnit_iff_coprime` and `Nat.Prime.coprime_iff_not_dvd`.
   * The nearby `ZMod.isUnit_prime_of_not_dvd` instead makes the prime the residue modulo an
     arbitrary modulus, so it does not have the roles required here. The prime-power theorem is
     more general in its modulus but is unnecessary for the prime-modulus adapter.
-/

import Mathlib.Data.ZMod.Basic

namespace D5.S3.ArithUnits.PrimeModInverse

/-- A natural number not divisible by a prime represents a unit modulo that prime. -/
theorem prime_not_dvd_is_unit (p a : ℕ) (hp : Nat.Prime p)
    (ha : ¬ p ∣ a) : IsUnit (a : ZMod p) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (hp.coprime_iff_not_dvd.mpr ha).symm

end D5.S3.ArithUnits.PrimeModInverse
