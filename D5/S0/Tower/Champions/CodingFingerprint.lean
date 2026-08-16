/- GID: D5/S0/Tower/Champions/CodingFingerprint
   generality: I
   mirror-B: D5/B/S0/Tower/Champions/CodingFingerprint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary, Zeckendorf, and Tribonacci coding fingerprints have distinct exact values. -/

import D5.S0.Tower.GoldenNames
import D5.S0.Tower.Tribonacci.Binet
import D5.S0.Tower.Tribonacci.Representation

/- Library-search audit trail (2026-08-16):
   * Repository search found the frozen Zeckendorf first weight `wValue`, the
     Tribonacci `decode` carrier, `tribonacciConstant`, and
     `tribonacciBinetCoefficient` with its `t^n` normalization.
   * Pinned mathlib supplies exact Fibonacci Binet formula `Real.coe_fib_eq`,
     golden-ratio identities, ordered-field division lemmas, and `nlinarith`.
     These exact hits suffice; no third-party theorem is imported. -/

namespace D5.S0.Tower.Champions.CodingFingerprint

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant
local notation "phi" => Real.goldenRatio

/-- The scale-independent coding fingerprint is the leading expansion main term
divided by the decoded value represented by that term. -/
noncomputable def codingFingerprint
    (leadingExpansionMainTerm decodedValue : Real) : Real :=
  leadingExpansionMainTerm / decodedValue

/-- A common nonzero rescaling of the expansion and decoding conventions leaves
the coding fingerprint unchanged. -/
theorem coding_fingerprint_scale_invariant
    (leadingExpansionMainTerm decodedValue scale : Real) (hscale : Ne scale 0) :
    codingFingerprint (scale * leadingExpansionMainTerm) (scale * decodedValue) =
      codingFingerprint leadingExpansionMainTerm decodedValue := by
  exact mul_div_mul_left leadingExpansionMainTerm decodedValue hscale

/-- The one-place Tribonacci word whose only digit is occupied. -/
def tribonacciFirstDigitName :
    D5.S0.Tower.Tribonacci.Names.TribonacciName 1 :=
  { val := fun _ => true
    property := trivial }

/-- The first binary positional weight decodes to one. -/
theorem binary_first_place_decode : (2 ^ 0 : Nat) = 1 := by
  norm_num

/-- The first Zeckendorf positional weight decodes to one. -/
theorem zeckendorf_first_place_decode : D5.S0.Conventions.wValue 0 = 1 := by
  norm_num [D5.S0.Conventions.wValue, Nat.fib]

/-- The occupied first Tribonacci digit decodes through the frozen carrier to one. -/
theorem tribonacci_first_place_decode :
    D5.S0.Tower.Tribonacci.Representation.decode tribonacciFirstDigitName = 1 := by
  norm_num [D5.S0.Tower.Tribonacci.Representation.decode,
    tribonacciFirstDigitName, D5.S0.Tower.Tribonacci.Names.tribonacci]

/-- The binary fingerprint uses its first geometric main term and decoded weight. -/
noncomputable def binaryCodingFingerprint : Real :=
  codingFingerprint 1 ((2 ^ 0 : Nat) : Real)

/-- The Zeckendorf first-place main term is the Perron part of `Fib(2)`. -/
noncomputable def zeckendorfCodingFingerprint : Real :=
  codingFingerprint (phi ^ 2 / Real.sqrt 5)
    (D5.S0.Conventions.wValue 0 : Real)

/-- The Tribonacci fingerprint uses the derivative-form shifted Binet main term
and the frozen integer decoding of the occupied first digit. -/
noncomputable def tribonacciCodingFingerprint : Real :=
  codingFingerprint
    ((D5.S0.Tower.Tribonacci.Binet.tribonacciBinetCoefficient * t) * t ^ 2)
    (D5.S0.Tower.Tribonacci.Representation.decode tribonacciFirstDigitName : Real)

/-- The source's shifted coefficient `a'` is the frozen coefficient `a` times
the Tribonacci Perron root; no second coefficient is introduced. -/
theorem tribonacci_binet_normalization_bridge :
    t ^ 2 / (3 * t ^ 2 - 2 * t - 1) =
      D5.S0.Tower.Tribonacci.Binet.tribonacciBinetCoefficient * t := by
  have htPos : 0 < t := D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos
  have htNe : Ne t 0 := D5.S0.Tower.Tribonacci.Values.tribonacciConstant_ne_zero
  have hshiftedDenomPos : 0 < 3 * t ^ 2 - 2 * t - 1 := by
    calc
      3 * t ^ 2 - 2 * t - 1 = (3 * t + 1) * (t - 1) := by ring
      _ > 0 := mul_pos (by nlinarith)
        (sub_pos.mpr D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant)
  have hdenomIdentity :
      (3 * t ^ 2 - 2 * t - 1) * t = t ^ 2 + 2 * t + 3 := by
    nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
  rw [D5.S0.Tower.Tribonacci.Binet.tribonacciBinetCoefficient]
  calc
    t ^ 2 / (3 * t ^ 2 - 2 * t - 1) =
        (t ^ 2 * t) / ((3 * t ^ 2 - 2 * t - 1) * t) := by
      field_simp [hshiftedDenomPos.ne', htNe]
    _ = (t ^ 2 * t) / (t ^ 2 + 2 * t + 3) := by rw [hdenomIdentity]
    _ = t ^ 2 / (t ^ 2 + 2 * t + 3) * t := by ring

/-- The exact binary coding fingerprint is one. -/
theorem binary_coding_fingerprint_value : binaryCodingFingerprint = 1 := by
  norm_num [binaryCodingFingerprint, codingFingerprint]

/-- The exact Zeckendorf coding fingerprint is `phi^2 / sqrt(5)`. -/
theorem zeckendorf_coding_fingerprint_value :
    zeckendorfCodingFingerprint = phi ^ 2 / Real.sqrt 5 := by
  norm_num [zeckendorfCodingFingerprint, codingFingerprint,
    D5.S0.Conventions.wValue, Nat.fib]

/-- The exact Tribonacci coding fingerprint is the shifted derivative-form
Binet coefficient times `t^2`. -/
theorem tribonacci_coding_fingerprint_value :
    tribonacciCodingFingerprint =
      (t ^ 2 / (3 * t ^ 2 - 2 * t - 1)) * t ^ 2 := by
  rw [tribonacciCodingFingerprint, codingFingerprint,
    tribonacci_first_place_decode]
  simp only [Nat.cast_one, div_one]
  exact congrArg (fun coefficient : Real => coefficient * t ^ 2)
    tribonacci_binet_normalization_bridge.symm

theorem binary_lt_zeckendorf_coding_fingerprint :
    binaryCodingFingerprint < zeckendorfCodingFingerprint := by
  rw [binary_coding_fingerprint_value, zeckendorf_coding_fingerprint_value]
  have hsqrtPos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt : Real.sqrt 5 = 2 * phi - 1 := by
    nlinarith [Real.goldenRatio_sub_goldenConj,
      Real.goldenRatio_add_goldenConj]
  rw [one_lt_div hsqrtPos, Real.goldenRatio_sq, hsqrt]
  nlinarith [Real.goldenRatio_lt_two]

theorem zeckendorf_coding_fingerprint_lt_two :
    zeckendorfCodingFingerprint < 2 := by
  rw [zeckendorf_coding_fingerprint_value]
  have hsqrtPos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt : Real.sqrt 5 = 2 * phi - 1 := by
    nlinarith [Real.goldenRatio_sub_goldenConj,
      Real.goldenRatio_add_goldenConj]
  rw [div_lt_iff₀ hsqrtPos, Real.goldenRatio_sq, hsqrt]
  nlinarith [Real.one_lt_goldenRatio]

theorem two_lt_tribonacci_coding_fingerprint :
    2 < tribonacciCodingFingerprint := by
  have htPos : 0 < t := D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos
  have hdenomPos : 0 < t ^ 2 + 2 * t + 3 := by positivity
  have hfactor :
      (t - 7 / 4) *
          (t ^ 2 + (7 / 4) * t + (7 / 4) ^ 2 - t - 7 / 4 - 1) =
        (29 / 64 : Real) := by
    nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
  have hfactorPos :
      0 < t ^ 2 + (7 / 4) * t + (7 / 4) ^ 2 - t - 7 / 4 - 1 := by
    nlinarith [sq_nonneg t]
  have hproductPos :
      0 < (t - 7 / 4) *
        (t ^ 2 + (7 / 4) * t + (7 / 4) ^ 2 - t - 7 / 4 - 1) := by
    rw [hfactor]
    norm_num
  have htLower : (7 / 4 : Real) < t := by
    rcases (mul_pos_iff.mp hproductPos) with hpositive | hnegative
    · exact sub_pos.mp hpositive.1
    · exact False.elim (not_lt_of_ge hfactorPos.le hnegative.2)
  have hquadratic : 0 < 2 * t ^ 2 - t - 4 := by
    nlinarith [sq_nonneg (t - 7 / 4)]
  have htFour : t ^ 4 = 2 * t ^ 2 + 2 * t + 1 := by
    have hscaled := congrArg (fun x : Real => t * x)
      D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic
    nlinarith [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic, hscaled]
  have htFive : t ^ 5 = 4 * t ^ 2 + 3 * t + 2 := by
    calc
      t ^ 5 = t * t ^ 4 := by ring
      _ = 2 * t ^ 3 + 2 * t ^ 2 + t := by rw [htFour]; ring
      _ = 4 * t ^ 2 + 3 * t + 2 := by
        rw [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
        ring
  rw [tribonacci_coding_fingerprint_value,
    tribonacci_binet_normalization_bridge,
    D5.S0.Tower.Tribonacci.Binet.tribonacciBinetCoefficient]
  rw [show (t ^ 2 / (t ^ 2 + 2 * t + 3) * t) * t ^ 2 =
      t ^ 5 / (t ^ 2 + 2 * t + 3) by ring]
  rw [lt_div_iff₀ hdenomPos, htFive]
  nlinarith

/-- The binary, Zeckendorf, and Tribonacci fingerprints are pairwise distinct. -/
theorem coding_fingerprint_values_pairwise_distinct :
    And (Ne binaryCodingFingerprint zeckendorfCodingFingerprint)
      (And (Ne binaryCodingFingerprint tribonacciCodingFingerprint)
        (Ne zeckendorfCodingFingerprint tribonacciCodingFingerprint)) := by
  have hzeckTribonacci :
      zeckendorfCodingFingerprint < tribonacciCodingFingerprint :=
    lt_trans zeckendorf_coding_fingerprint_lt_two
      two_lt_tribonacci_coding_fingerprint
  exact And.intro (ne_of_lt binary_lt_zeckendorf_coding_fingerprint)
    (And.intro
      (ne_of_lt (lt_trans binary_lt_zeckendorf_coding_fingerprint hzeckTribonacci))
      (ne_of_lt hzeckTribonacci))

end D5.S0.Tower.Champions.CodingFingerprint
