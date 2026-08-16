/- GID: D5/S0/Tower/Champions/EncodingSensitivity
   generality: I
   mirror-B: D5/B/S0/Tower/Champions/EncodingSensitivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fingerprints distinguish codings; occupied first places all decode to one. -/

import D5.S0.Tower.Champions.CodingFingerprint

/- Library-search audit trail (2026-08-17):
   * Repository search found the three frozen first-place decoding theorems and
     `coding_fingerprint_values_pairwise_distinct`; `marker_digit_injective`
     supplied the finite-enumeration proof pattern used below.
   * Pinned mathlib and Loogle both expose `Function.Injective` as the exact
     abstraction for a quantity that distinguishes its input. LeanSearch's
     queried API returned no response. No third-party theorem is imported. -/

namespace D5.S0.Tower.Champions.EncodingSensitivity

/-- The three coding systems compared by the source clause. -/
inductive CodingSystem where
  | binary
  | zeckendorf
  | tribonacci

/-- The frozen coding fingerprint, indexed by coding system. -/
noncomputable def codingFingerprintFor : CodingSystem → Real
  | .binary =>
      D5.S0.Tower.Champions.CodingFingerprint.binaryCodingFingerprint
  | .zeckendorf =>
      D5.S0.Tower.Champions.CodingFingerprint.zeckendorfCodingFingerprint
  | .tribonacci =>
      D5.S0.Tower.Champions.CodingFingerprint.tribonacciCodingFingerprint

/-- The value decoded from the occupied first place of each coding system. -/
def firstPlaceDecodedValue : CodingSystem → Nat
  | .binary => 2 ^ 0
  | .zeckendorf => D5.S0.Conventions.wValue 0
  | .tribonacci =>
      D5.S0.Tower.Tribonacci.Representation.decode
        D5.S0.Tower.Champions.CodingFingerprint.tribonacciFirstDigitName

/-- The coding fingerprint distinguishes every pair of the three encodings. -/
theorem coding_fingerprint_is_encoding_sensitive :
    Function.Injective codingFingerprintFor := by
  rcases D5.S0.Tower.Champions.CodingFingerprint.coding_fingerprint_values_pairwise_distinct with
    ⟨hBinaryZeckendorf, hBinaryTribonacci, hZeckendorfTribonacci⟩
  intro left right equality
  cases left <;> cases right <;> simp_all [codingFingerprintFor]

/-- First-place decoding is blind to the choice among the three encodings. -/
theorem first_place_decoded_value_is_encoding_blind :
    ∀ coding, firstPlaceDecodedValue coding = 1 := by
  intro coding
  cases coding with
  | binary =>
      change (2 ^ 0 : Nat) = 1
      exact D5.S0.Tower.Champions.CodingFingerprint.binary_first_place_decode
  | zeckendorf =>
      change D5.S0.Conventions.wValue 0 = 1
      exact D5.S0.Tower.Champions.CodingFingerprint.zeckendorf_first_place_decode
  | tribonacci =>
      change
        D5.S0.Tower.Tribonacci.Representation.decode
          D5.S0.Tower.Champions.CodingFingerprint.tribonacciFirstDigitName = 1
      exact D5.S0.Tower.Champions.CodingFingerprint.tribonacci_first_place_decode

end D5.S0.Tower.Champions.EncodingSensitivity
