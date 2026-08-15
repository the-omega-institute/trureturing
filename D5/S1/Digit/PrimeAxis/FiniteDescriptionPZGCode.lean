/- GID: D5/S1/Digit/PrimeAxis/FiniteDescriptionPZGCode
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxis/FiniteDescriptionPZGCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Embed shifted prime-sequence description codes into canonical PZG tables. -/

import D5.S0.History.PrimeSequenceCode
import D5.S1.Digit.PrimeAxisEncoding

/- Library-search audit trail (2026-08-15):
   * Pinned Mathlib supplies `Finset.prod_pos`, `pow_pos`,
     `Nat.Prime.pos`, and `Nat.prime_nth_prime`; they prove that every
     shifted prime-sequence code is positive, including the empty product.
   * `Equiv.apply_symm_apply` is the exact inverse law used for the existing
     `primeAxisEncoding` equivalence.
   * Repository searches found the two endpoint codings but no declaration
     composing `primeSequenceCode` with `primeAxisEncoding.symm`.
-/

namespace D5.S1.Digit.PrimeAxis.FiniteDescriptionPZGCode

open D5.S0.History.PrimeSequenceCode
open D5.S1.Digit

/-- Every shifted prime-sequence code is a positive natural number. -/
theorem prime_sequence_code_pos (description : List Nat) :
    0 < primeSequenceCode description := by
  rw [primeSequenceCode]
  exact Finset.prod_pos fun i _ =>
    pow_pos (Nat.Prime.pos (Nat.prime_nth_prime i)) _

/-- Package a shifted prime-sequence code in the positive-natural carrier. -/
noncomputable def positivePrimeSequenceCode (description : List Nat) : ℕ+ :=
  ⟨primeSequenceCode description, prime_sequence_code_pos description⟩

/-- Interpret a finite natural description as a canonical PZG prime-axis
table carrying its shifted prime-sequence code. -/
noncomputable def finiteDescriptionPZGCode
    (description : List Nat) : PrimeAxisTable :=
  primeAxisEncoding.symm (positivePrimeSequenceCode description)

/-- The PZG table encoder returns exactly the shifted prime-sequence code,
and the table decoder therefore recovers the same natural number. This is a
generic description-code membership bridge, not a kernel fixed point. -/
theorem finite_description_pzg_code_spec (description : List Nat) :
    primeAxisEncoding (finiteDescriptionPZGCode description) =
        positivePrimeSequenceCode description ∧
      decodePrimeAxisTable (finiteDescriptionPZGCode description) =
        primeSequenceCode description := by
  have hencode :
      primeAxisEncoding (finiteDescriptionPZGCode description) =
        positivePrimeSequenceCode description := by
    exact Equiv.apply_symm_apply primeAxisEncoding _
  constructor
  · exact hencode
  · calc
      decodePrimeAxisTable (finiteDescriptionPZGCode description) =
          ((primeAxisEncoding (finiteDescriptionPZGCode description) : ℕ+) : Nat) :=
        (primeAxisEncoding_coe _).symm
      _ = (positivePrimeSequenceCode description : Nat) :=
        congrArg Subtype.val hencode
      _ = primeSequenceCode description := rfl

#print axioms prime_sequence_code_pos
#print axioms positivePrimeSequenceCode
#print axioms finiteDescriptionPZGCode
#print axioms finite_description_pzg_code_spec

end D5.S1.Digit.PrimeAxis.FiniteDescriptionPZGCode
