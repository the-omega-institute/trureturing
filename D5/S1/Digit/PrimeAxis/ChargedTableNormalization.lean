/- GID: D5/S1/Digit/PrimeAxis/ChargedTableNormalization
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxis/ChargedTableNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite sequences of charged carries normalize every finitely supported prime-indexed raw table. -/

import D5.S1.Deficit.ChargedCarryPath
import D5.S1.Digit.PrimeAxisTable

set_option autoImplicit false

namespace D5.S1.Digit.PrimeAxis.ChargedTableNormalization

open D5.S1.Deficit

/-- One charged carry changes the selected prime row and leaves every other row unchanged. -/
def TableStep (r r' : PrimeAxis →₀ RawDigits) (p : PrimeAxis) (z : ℤ) : Prop :=
  ChargedCarryStep (r p) (r' p) z ∧ ∀ q, q ≠ p → r' q = r q

/-- A finite sequence of actual table carries records its total charge at each prime. -/
inductive TablePath : (PrimeAxis →₀ RawDigits) → (PrimeAxis →₀ RawDigits) →
    (PrimeAxis →₀ ℤ) → Prop
  /-- The empty path leaves the table unchanged and has zero charge at every prime. -/
  | refl (r : PrimeAxis →₀ RawDigits) : TablePath r r 0
  /-- Appending a carry adds its integer charge only at the prime row on which it acts. -/
  | tail {r s t : PrimeAxis →₀ RawDigits} {charge : PrimeAxis →₀ ℤ}
      {p : PrimeAxis} {z : ℤ} :
      TablePath r s charge → TableStep s t p z →
      TablePath r t (charge + Finsupp.single p z)

/-- Normalize each raw row; the zero row remains zero, so the resulting table has finite support. -/
noncomputable def rowNormalize (r : PrimeAxis →₀ RawDigits) : PrimeAxis →₀ RawDigits :=
  r.mapRange normalize (by
    apply normalize_eq_of_canonical
    simp [CanonicalRaw])

end D5.S1.Digit.PrimeAxis.ChargedTableNormalization
