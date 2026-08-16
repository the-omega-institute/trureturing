/- GID: D5/S0/Tower/Champions/DecimalBounds
   generality: I
   mirror-B: D5/B/S0/Tower/Champions/DecimalBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four frozen exact constants certify their source decimal roundings. -/

import D5.S0.Tower.Champions.CodingFingerprint

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen Tribonacci cubic and unique-root
     characterization, Binet coefficient and normalization bridge, and both
     exact coding-fingerprint values used below.
   * Pinned mathlib supplies `intermediate_value_Icc`, `Real.sq_sqrt`,
     ordered-field division lemmas, `norm_num`, and `nlinarith`. These exact
     hits suffice; no third-party theorem is imported. -/

namespace D5.S0.Tower.Champions.DecimalBounds

local notation "t" => D5.S0.Tower.Tribonacci.Values.tribonacciConstant

/-- The source decimal `1.839287` rounds the frozen Tribonacci Perron root
with error strictly below half a unit in the seventh decimal place. -/
theorem tribonacci_constant_rounding_bound :
    |t - 1.839287| < (0.0000005 : Real) := by
  let f : Real → Real := fun x => x ^ 3 - x ^ 2 - x - 1
  have hcontinuous : Continuous f := by fun_prop
  have hlower : f 1.8392865 < 0 := by norm_num [f]
  have hupper : 0 < f 1.8392875 := by norm_num [f]
  have hzero : (0 : Real) ∈ Set.Icc (f 1.8392865) (f 1.8392875) :=
    ⟨hlower.le, hupper.le⟩
  have himage := intermediate_value_Icc
    (show (1.8392865 : Real) ≤ 1.8392875 by norm_num)
    hcontinuous.continuousOn hzero
  obtain ⟨x, hx, hfx⟩ :=
    (Set.mem_image f (Set.Icc (1.8392865 : Real) 1.8392875) 0).mp himage
  have hxroot : x ^ 3 = x ^ 2 + x + 1 := by
    dsimp [f] at hfx
    nlinarith
  have hxlower : (1.8392865 : Real) < x :=
    lt_of_le_of_ne hx.1 (by
      intro heq
      rw [heq] at hlower
      linarith)
  have hxupper : x < (1.8392875 : Real) :=
    lt_of_le_of_ne hx.2 (by
      intro heq
      rw [← heq] at hupper
      linarith)
  have hidentification : x = t :=
    D5.S0.Tower.Tribonacci.PerronRoot.eq_tribonacciConstant_iff.mpr
      ⟨by nlinarith, by nlinarith, hxroot⟩
  rw [← hidentification, abs_lt]
  constructor <;> nlinarith

/-- The source's shifted Binet coefficient `a' = a * t` rounds to
`0.618420` with error strictly below half a unit in the seventh decimal place. -/
theorem tribonacci_shifted_binet_coefficient_rounding_bound :
    |D5.S0.Tower.Tribonacci.Binet.tribonacciBinetCoefficient * t - 0.618420| <
      (0.0000005 : Real) := by
  have htBounds := abs_lt.mp tribonacci_constant_rounding_bound
  have htLower : (1.8392865 : Real) < t := by nlinarith
  have htUpper : t < (1.8392875 : Real) := by nlinarith
  have htDenomPos : 0 < t ^ 2 + 2 * t + 3 := by
    nlinarith [sq_nonneg (t + 1)]
  have hvalue :
      D5.S0.Tower.Tribonacci.Binet.tribonacciBinetCoefficient * t =
        (t ^ 2 + t + 1) / (t ^ 2 + 2 * t + 3) := by
    calc
      D5.S0.Tower.Tribonacci.Binet.tribonacciBinetCoefficient * t =
          t ^ 3 / (t ^ 2 + 2 * t + 3) := by
        rw [D5.S0.Tower.Tribonacci.Binet.tribonacciBinetCoefficient]
        ring
      _ = (t ^ 2 + t + 1) / (t ^ 2 + 2 * t + 3) := by
        rw [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
  have hLowerDenomPos :
      0 < (1.8392865 : Real) ^ 2 + 2 * 1.8392865 + 3 := by norm_num
  have hUpperDenomPos :
      0 < (1.8392875 : Real) ^ 2 + 2 * 1.8392875 + 3 := by norm_num
  have hLowerProduct :
      0 < (t - 1.8392865) *
        (t * 1.8392865 + 2 * t + 2 * 1.8392865 + 1) := by
    exact mul_pos (sub_pos.mpr htLower) (by positivity)
  have hLowerFactor :
      (t ^ 2 + t + 1) *
          ((1.8392865 : Real) ^ 2 + 2 * 1.8392865 + 3) -
        ((1.8392865 : Real) ^ 2 + 1.8392865 + 1) *
          (t ^ 2 + 2 * t + 3) =
        (t - 1.8392865) *
          (t * 1.8392865 + 2 * t + 2 * 1.8392865 + 1) := by
    ring
  have hLowerMonotone :
      ((1.8392865 : Real) ^ 2 + 1.8392865 + 1) /
          ((1.8392865 : Real) ^ 2 + 2 * 1.8392865 + 3) <
        (t ^ 2 + t + 1) / (t ^ 2 + 2 * t + 3) := by
    rw [div_lt_div_iff₀ hLowerDenomPos htDenomPos]
    nlinarith
  have hUpperProduct :
      0 < (1.8392875 - t) *
        (1.8392875 * t + 2 * 1.8392875 + 2 * t + 1) := by
    exact mul_pos (sub_pos.mpr htUpper) (by positivity)
  have hUpperFactor :
      ((1.8392875 : Real) ^ 2 + 1.8392875 + 1) *
          (t ^ 2 + 2 * t + 3) -
        (t ^ 2 + t + 1) *
          ((1.8392875 : Real) ^ 2 + 2 * 1.8392875 + 3) =
        (1.8392875 - t) *
          (1.8392875 * t + 2 * 1.8392875 + 2 * t + 1) := by
    ring
  have hUpperMonotone :
      (t ^ 2 + t + 1) / (t ^ 2 + 2 * t + 3) <
        ((1.8392875 : Real) ^ 2 + 1.8392875 + 1) /
          ((1.8392875 : Real) ^ 2 + 2 * 1.8392875 + 3) := by
    rw [div_lt_div_iff₀ htDenomPos hUpperDenomPos]
    nlinarith
  have hEndpointLower :
      (0.6184195 : Real) <
        ((1.8392865 : Real) ^ 2 + 1.8392865 + 1) /
          ((1.8392865 : Real) ^ 2 + 2 * 1.8392865 + 3) := by
    norm_num
  have hEndpointUpper :
      ((1.8392875 : Real) ^ 2 + 1.8392875 + 1) /
          ((1.8392875 : Real) ^ 2 + 2 * 1.8392875 + 3) <
        (0.6184205 : Real) := by
    norm_num
  rw [hvalue, abs_lt]
  constructor <;> nlinarith

/-- The exact Zeckendorf coding fingerprint rounds to the source decimal
`1.170820` with error strictly below half a unit in the seventh decimal place. -/
theorem zeckendorf_coding_fingerprint_rounding_bound :
    |D5.S0.Tower.Champions.CodingFingerprint.zeckendorfCodingFingerprint -
        1.170820| < (0.0000005 : Real) := by
  rw [D5.S0.Tower.Champions.CodingFingerprint.zeckendorf_coding_fingerprint_value]
  have hsqrtPos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hLowerScaled :
      (2 * (1.1708195 : Real) - 1) * Real.sqrt 5 < 3 := by
    apply (sq_lt_sq₀ (mul_nonneg (by norm_num) hsqrtPos.le) (by norm_num)).mp
    rw [mul_pow, hsqrtSq]
    norm_num
  have hUpperScaled :
      3 < (2 * (1.1708205 : Real) - 1) * Real.sqrt 5 := by
    apply (sq_lt_sq₀ (by norm_num)
      (mul_nonneg (by norm_num) hsqrtPos.le)).mp
    rw [mul_pow, hsqrtSq]
    norm_num
  have hLower :
      (1.1708195 : Real) < Real.goldenRatio ^ 2 / Real.sqrt 5 := by
    rw [lt_div_iff₀ hsqrtPos, Real.goldenRatio_sq]
    change 1.1708195 * Real.sqrt 5 < (1 + Real.sqrt 5) / 2 + 1
    nlinarith
  have hUpper :
      Real.goldenRatio ^ 2 / Real.sqrt 5 < (1.1708205 : Real) := by
    rw [div_lt_iff₀ hsqrtPos, Real.goldenRatio_sq]
    change (1 + Real.sqrt 5) / 2 + 1 < 1.1708205 * Real.sqrt 5
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith

/-- The exact Tribonacci coding fingerprint rounds to the source decimal
`2.092100` with error strictly below half a unit in the seventh decimal place. -/
theorem tribonacci_coding_fingerprint_rounding_bound :
    |D5.S0.Tower.Champions.CodingFingerprint.tribonacciCodingFingerprint -
        2.092100| < (0.0000005 : Real) := by
  have htDenomPos : 0 < t ^ 2 + 2 * t + 3 := by
    nlinarith [sq_nonneg (t + 1)]
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
  have hvalue :
      D5.S0.Tower.Champions.CodingFingerprint.tribonacciCodingFingerprint =
        (4 * t ^ 2 + 3 * t + 2) / (t ^ 2 + 2 * t + 3) := by
    rw [D5.S0.Tower.Champions.CodingFingerprint.tribonacci_coding_fingerprint_value,
      D5.S0.Tower.Champions.CodingFingerprint.tribonacci_binet_normalization_bridge,
      D5.S0.Tower.Tribonacci.Binet.tribonacciBinetCoefficient]
    rw [show (t ^ 2 / (t ^ 2 + 2 * t + 3) * t) * t ^ 2 =
      t ^ 5 / (t ^ 2 + 2 * t + 3) by ring, htFive]
  have htSharpLower : (1.83928675 : Real) < t := by
    have hfactorPos :
        0 < t ^ 2 + t * 1.83928675 + (1.83928675 : Real) ^ 2 -
          t - 1.83928675 - 1 := by
      have htTerm : 0 < t * (t - 1) :=
        mul_pos D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos
          (sub_pos.mpr
            D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant)
      have hcross : 0 < t * (1.83928675 : Real) :=
        mul_pos D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos (by norm_num)
      have hconstant :
          0 < (1.83928675 : Real) ^ 2 - 1.83928675 - 1 := by
        norm_num
      nlinarith
    have hproductEq :
        (t - 1.83928675) *
            (t ^ 2 + t * 1.83928675 + (1.83928675 : Real) ^ 2 -
              t - 1.83928675 - 1) =
          -((1.83928675 : Real) ^ 3 - 1.83928675 ^ 2 - 1.83928675 - 1) := by
      calc
        (t - 1.83928675) *
            (t ^ 2 + t * 1.83928675 + (1.83928675 : Real) ^ 2 -
              t - 1.83928675 - 1) =
            (t ^ 3 - t ^ 2 - t - 1) -
              ((1.83928675 : Real) ^ 3 - 1.83928675 ^ 2 - 1.83928675 - 1) := by
          ring
        _ = -((1.83928675 : Real) ^ 3 - 1.83928675 ^ 2 - 1.83928675 - 1) := by
          rw [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
          ring
    have hproductPos :
        0 < (t - 1.83928675) *
          (t ^ 2 + t * 1.83928675 + (1.83928675 : Real) ^ 2 -
            t - 1.83928675 - 1) := by
      rw [hproductEq]
      norm_num
    rcases mul_pos_iff.mp hproductPos with hpositive | hnegative
    · exact sub_pos.mp hpositive.1
    · exact False.elim (not_lt_of_ge hfactorPos.le hnegative.2)
  have htSharpUpper : t < (1.83928676 : Real) := by
    have hfactorPos :
        0 < (1.83928676 : Real) ^ 2 + 1.83928676 * t + t ^ 2 -
          1.83928676 - t - 1 := by
      have htTerm : 0 < t * (t - 1) :=
        mul_pos D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos
          (sub_pos.mpr
            D5.S0.Tower.Tribonacci.Values.one_lt_tribonacciConstant)
      have hcross : 0 < (1.83928676 : Real) * t :=
        mul_pos (by norm_num)
          D5.S0.Tower.Tribonacci.Values.tribonacciConstant_pos
      have hconstant :
          0 < (1.83928676 : Real) ^ 2 - 1.83928676 - 1 := by
        norm_num
      nlinarith
    have hproductEq :
        (1.83928676 - t) *
            ((1.83928676 : Real) ^ 2 + 1.83928676 * t + t ^ 2 -
              1.83928676 - t - 1) =
          (1.83928676 : Real) ^ 3 - 1.83928676 ^ 2 - 1.83928676 - 1 := by
      calc
        (1.83928676 - t) *
            ((1.83928676 : Real) ^ 2 + 1.83928676 * t + t ^ 2 -
              1.83928676 - t - 1) =
            ((1.83928676 : Real) ^ 3 - 1.83928676 ^ 2 - 1.83928676 - 1) -
              (t ^ 3 - t ^ 2 - t - 1) := by
          ring
        _ = (1.83928676 : Real) ^ 3 - 1.83928676 ^ 2 - 1.83928676 - 1 := by
          rw [D5.S0.Tower.Tribonacci.Values.tribonacciConstant_cubic]
          ring
    have hproductPos :
        0 < (1.83928676 - t) *
          ((1.83928676 : Real) ^ 2 + 1.83928676 * t + t ^ 2 -
            1.83928676 - t - 1) := by
      rw [hproductEq]
      norm_num
    rcases mul_pos_iff.mp hproductPos with hpositive | hnegative
    · exact sub_pos.mp hpositive.1
    · exact False.elim (not_lt_of_ge hfactorPos.le hnegative.2)
  have hLowerDenomPos :
      0 < (1.83928675 : Real) ^ 2 + 2 * 1.83928675 + 3 := by norm_num
  have hUpperDenomPos :
      0 < (1.83928676 : Real) ^ 2 + 2 * 1.83928676 + 3 := by norm_num
  have hLowerProduct :
      0 < 5 * (t - 1.83928675) *
        (t * 1.83928675 + 2 * t + 2 * 1.83928675 + 1) := by
    positivity
  have hLowerFactor :
      (4 * t ^ 2 + 3 * t + 2) *
          ((1.83928675 : Real) ^ 2 + 2 * 1.83928675 + 3) -
        (4 * (1.83928675 : Real) ^ 2 + 3 * 1.83928675 + 2) *
          (t ^ 2 + 2 * t + 3) =
        5 * (t - 1.83928675) *
          (t * 1.83928675 + 2 * t + 2 * 1.83928675 + 1) := by
    ring
  have hLowerMonotone :
      (4 * (1.83928675 : Real) ^ 2 + 3 * 1.83928675 + 2) /
          ((1.83928675 : Real) ^ 2 + 2 * 1.83928675 + 3) <
        (4 * t ^ 2 + 3 * t + 2) / (t ^ 2 + 2 * t + 3) := by
    rw [div_lt_div_iff₀ hLowerDenomPos htDenomPos]
    nlinarith
  have hUpperProduct :
      0 < 5 * (1.83928676 - t) *
        (1.83928676 * t + 2 * 1.83928676 + 2 * t + 1) := by
    positivity
  have hUpperFactor :
      (4 * (1.83928676 : Real) ^ 2 + 3 * 1.83928676 + 2) *
          (t ^ 2 + 2 * t + 3) -
        (4 * t ^ 2 + 3 * t + 2) *
          ((1.83928676 : Real) ^ 2 + 2 * 1.83928676 + 3) =
        5 * (1.83928676 - t) *
          (1.83928676 * t + 2 * 1.83928676 + 2 * t + 1) := by
    ring
  have hUpperMonotone :
      (4 * t ^ 2 + 3 * t + 2) / (t ^ 2 + 2 * t + 3) <
        (4 * (1.83928676 : Real) ^ 2 + 3 * 1.83928676 + 2) /
          ((1.83928676 : Real) ^ 2 + 2 * 1.83928676 + 3) := by
    rw [div_lt_div_iff₀ htDenomPos hUpperDenomPos]
    nlinarith
  have hEndpointLower :
      (2.0920995 : Real) <
        (4 * (1.83928675 : Real) ^ 2 + 3 * 1.83928675 + 2) /
          ((1.83928675 : Real) ^ 2 + 2 * 1.83928675 + 3) := by
    norm_num
  have hEndpointUpper :
      (4 * (1.83928676 : Real) ^ 2 + 3 * 1.83928676 + 2) /
          ((1.83928676 : Real) ^ 2 + 2 * 1.83928676 + 3) <
        (2.0921005 : Real) := by
    norm_num
  rw [hvalue, abs_lt]
  constructor <;> nlinarith

end D5.S0.Tower.Champions.DecimalBounds
