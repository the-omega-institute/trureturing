/- GID: D5/S3/ArithUnits/FermatLittle
   generality: G
   mirror-B: D5/B/S3/ArithUnits/FermatLittle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A power one below a prime is congruent to one when the prime does not divide the base. -/

import Mathlib.FieldTheory.Finite.Basic

namespace D5.S3.ArithUnits.FermatLittle

/-- Fermat's little theorem in natural-number congruence form. This is a thin
wrapper around Mathlib's coprime formulation, with nondivisibility as the
explicit premise. -/
theorem fermat_little_theorem (p a : Nat) (hp : Nat.Prime p)
    (hpa : Not (p ∣ a)) :
    Nat.ModEq p (a ^ (p - 1)) 1 :=
  Nat.ModEq.pow_card_sub_one_eq_one hp
    (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr hpa))

end D5.S3.ArithUnits.FermatLittle
