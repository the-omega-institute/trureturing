/- GID: D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate
   generality: I
   mirror-B: D5/B/S3/Constants/Irrationality/TribonacciDeficitScanCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The source-normalized Tribonacci deficit has an exact finite scan certificate. -/

import D5.S3.Constants.Irrationality.TribonacciDeficitScan

namespace D5.S3.Constants.Irrationality.TribonacciDeficitScan

set_option maxRecDepth 500000

open D5.S0.Tower.Tribonacci.Values
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator

local notation "t" => tribonacciConstant

set_option maxHeartbeats 750000 in
-- The closed row block contains 8,775 pairs and needs additional reduction.
/-- Kernel certificate for rows 1 through 50. -/
theorem tribonacci_nonintegral_row_count_1_50 :
    ∑ v₁ ∈ Finset.Icc 1 50, tribonacciNonintegralRowCount v₁ = 3820 := by
  decide

set_option maxHeartbeats 750000 in
-- The closed row block contains 6,275 pairs and needs additional reduction.
/-- Kernel certificate for rows 51 through 100. -/
theorem tribonacci_nonintegral_row_count_51_100 :
    ∑ v₁ ∈ Finset.Icc 51 100, tribonacciNonintegralRowCount v₁ = 2912 := by
  decide

set_option maxHeartbeats 750000 in
-- The closed row block contains 3,775 pairs and needs additional reduction.
/-- Kernel certificate for rows 101 through 150. -/
theorem tribonacci_nonintegral_row_count_101_150 :
    ∑ v₁ ∈ Finset.Icc 101 150, tribonacciNonintegralRowCount v₁ = 1654 := by
  decide

set_option maxHeartbeats 750000 in
-- The closed row block contains 1,275 pairs and needs additional reduction.
/-- Kernel certificate for rows 151 through 200. -/
theorem tribonacci_nonintegral_row_count_151_200 :
    ∑ v₁ ∈ Finset.Icc 151 200, tribonacciNonintegralRowCount v₁ = 548 := by
  decide

/-- Exactly 8,934 of the 20,100 scanned deficits have a nonzero quadratic
coordinate. -/
theorem tribonacci_nonintegral_scan_count : tribonacciNonintegralScanPairs.card = 8934 := by
  rw [tribonacci_nonintegral_scan_card_eq_row_sum]
  have hsets : Finset.Icc 1 200 =
      Finset.Icc 1 50 ∪
        (Finset.Icc 51 100 ∪ (Finset.Icc 101 150 ∪ Finset.Icc 151 200)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [hsets, Finset.sum_union, Finset.sum_union, Finset.sum_union,
    tribonacci_nonintegral_row_count_1_50,
    tribonacci_nonintegral_row_count_51_100,
    tribonacci_nonintegral_row_count_101_150,
    tribonacci_nonintegral_row_count_151_200]
  · norm_num
  all_goals
    apply Finset.disjoint_left.mpr
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega

set_option maxHeartbeats 750000 in
-- The closed row block contains 8,775 pairs and needs additional reduction.
/-- Spectrum inclusion certificate for rows 1 through 50. -/
theorem tribonacci_scan_spectrum_mem_1_50 :
    ∀ v₁ ∈ Finset.Icc 1 50, ∀ v₂ ∈ Finset.Icc v₁ 200,
      tribonacciScaledNumerator (tribonacciIntegralDeficit10 v₁ v₂) ∈
        tribonacciScanNumeratorSpectrum := by
  decide

set_option maxHeartbeats 750000 in
-- The closed row block contains 6,275 pairs and needs additional reduction.
/-- Spectrum inclusion certificate for rows 51 through 100. -/
theorem tribonacci_scan_spectrum_mem_51_100 :
    ∀ v₁ ∈ Finset.Icc 51 100, ∀ v₂ ∈ Finset.Icc v₁ 200,
      tribonacciScaledNumerator (tribonacciIntegralDeficit10 v₁ v₂) ∈
        tribonacciScanNumeratorSpectrum := by
  decide

set_option maxHeartbeats 750000 in
-- The closed row block contains 3,775 pairs and needs additional reduction.
/-- Spectrum inclusion certificate for rows 101 through 150. -/
theorem tribonacci_scan_spectrum_mem_101_150 :
    ∀ v₁ ∈ Finset.Icc 101 150, ∀ v₂ ∈ Finset.Icc v₁ 200,
      tribonacciScaledNumerator (tribonacciIntegralDeficit10 v₁ v₂) ∈
        tribonacciScanNumeratorSpectrum := by
  decide

set_option maxHeartbeats 750000 in
-- The closed row block contains 1,275 pairs and needs additional reduction.
/-- Spectrum inclusion certificate for rows 151 through 200. -/
theorem tribonacci_scan_spectrum_mem_151_200 :
    ∀ v₁ ∈ Finset.Icc 151 200, ∀ v₂ ∈ Finset.Icc v₁ 200,
      tribonacciScaledNumerator (tribonacciIntegralDeficit10 v₁ v₂) ∈
        tribonacciScanNumeratorSpectrum := by
  decide

theorem tribonacci_scan_code_mem_numerator_spectrum {pair : Nat × Nat}
    (hpair : pair ∈ tribonacciScanPairs) :
    tribonacciScaledNumerator (tribonacciIntegralDeficit10 pair.1 pair.2) ∈
      tribonacciScanNumeratorSpectrum := by
  have hbounds := mem_tribonacciScanPairs_iff.mp hpair
  have hsecond : pair.2 ∈ Finset.Icc pair.1 200 := by
    simp only [Finset.mem_Icc]
    exact ⟨hbounds.2.1, hbounds.2.2⟩
  by_cases h50 : pair.1 ≤ 50
  · exact tribonacci_scan_spectrum_mem_1_50 pair.1 (by
      simp only [Finset.mem_Icc]
      exact ⟨hbounds.1, h50⟩) pair.2 hsecond
  by_cases h100 : pair.1 ≤ 100
  · exact tribonacci_scan_spectrum_mem_51_100 pair.1 (by
      simp only [Finset.mem_Icc]
      omega) pair.2 hsecond
  by_cases h150 : pair.1 ≤ 150
  · exact tribonacci_scan_spectrum_mem_101_150 pair.1 (by
      simp only [Finset.mem_Icc]
      omega) pair.2 hsecond
  · exact tribonacci_scan_spectrum_mem_151_200 pair.1 (by
      simp only [Finset.mem_Icc]
      omega) pair.2 hsecond

/-- Every listed numerator code has an explicit witness in the scan. -/
theorem tribonacci_numerator_spectrum_subset_scan_image :
    tribonacciScanNumeratorSpectrum ⊆
      tribonacciScanPairs.image (fun pair =>
        tribonacciScaledNumerator (tribonacciIntegralDeficit10 pair.1 pair.2)) := by
  intro x hx
  simp only [tribonacciScanNumeratorSpectrum, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨(185, 185), by decide, by decide⟩
  · exact Finset.mem_image.mpr ⟨(4, 5), by decide, by decide⟩
  · exact Finset.mem_image.mpr ⟨(1, 1), by decide, by decide⟩
  · exact Finset.mem_image.mpr ⟨(4, 4), by decide, by decide⟩
  · exact Finset.mem_image.mpr ⟨(1, 2), by decide, by decide⟩
  · exact Finset.mem_image.mpr ⟨(1, 3), by decide, by decide⟩
  · exact Finset.mem_image.mpr ⟨(2, 6), by decide, by decide⟩
  · exact Finset.mem_image.mpr ⟨(2, 2), by decide, by decide⟩

/-- The integer scan image is the denominator-free eight-point spectrum. -/
theorem tribonacci_scan_numerator_spectrum_exact :
    tribonacciScanPairs.image (fun pair =>
      tribonacciScaledNumerator (tribonacciIntegralDeficit10 pair.1 pair.2)) =
      tribonacciScanNumeratorSpectrum := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp hx
    exact tribonacci_scan_code_mem_numerator_spectrum hpair
  · exact tribonacci_numerator_spectrum_subset_scan_image

theorem tribonacci_scan_numerator_spectrum_to_cubic :
    tribonacciScanNumeratorSpectrum.image tribonacciNumeratorToCubic =
      tribonacciScanSpectrum := by
  norm_num [tribonacciScanNumeratorSpectrum, tribonacciNumeratorToCubic,
    tribonacciIntegralCodeZero, tribonacciScanSpectrum, tribonacciCodeZero]

/-- The exact code image of the scan is the stated eight-point spectrum. -/
theorem tribonacci_scan_spectrum_exact :
    tribonacciScanPairs.image (fun pair => tribonacciDeficitCodeAt 10 pair.1 pair.2) =
      tribonacciScanSpectrum := by
  rw [← tribonacci_scan_numerator_spectrum_to_cubic,
    ← tribonacci_scan_numerator_spectrum_exact, Finset.image_image]
  apply Finset.image_congr
  intro pair hpair
  simp only [Function.comp_apply]
  rw [tribonacci_deficit_code_eq_numerator, ← tribonacci_integral_deficit_10_eq]

theorem tribonacci_scan_deficit_eq_code {pair : Nat × Nat}
    (hpair : pair ∈ tribonacciScanPairs) :
    tribonacciDeficit pair.1 pair.2 =
      tribonacciCodeValue (tribonacciDeficitCodeAt 10 pair.1 pair.2) := by
  have hp := Finset.mem_filter.mp hpair
  have hrange := Finset.mem_product.mp hp.1
  have hv₁ : pair.1 ≤ 200 := by
    have := Finset.mem_range.mp hrange.1
    omega
  have hv₂ : pair.2 ≤ 200 := by
    have := Finset.mem_range.mp hrange.2
    omega
  have hsum : pair.1 + pair.2 ≤ 400 := by omega
  have hv₁Scan : pair.1 ≤ 400 := by omega
  have hv₂Scan : pair.2 ≤ 400 := by omega
  rw [tribonacciDeficit, tribonacci_beta_real_eq_scan_code hv₁Scan,
    tribonacci_beta_real_eq_scan_code hv₂Scan,
    tribonacci_beta_real_eq_scan_code hsum]
  unfold tribonacciDeficitCodeAt
  simp_rw [tribonacci_code_value_mul, tribonacci_code_value_sub,
    tribonacci_code_value_add]
  ring

/-- Membership in the exact filtered scan certifies genuine real
nonintegrality, not merely a nonzero symbolic coordinate. -/
theorem tribonacci_nonintegral_of_mem_scan {pair : Nat × Nat}
    (hpair : pair ∈ tribonacciNonintegralScanPairs) :
    ¬ ∃ z : Int, tribonacciDeficit pair.1 pair.2 = (z : Real) := by
  have hfilter := Finset.mem_filter.mp hpair
  rw [tribonacci_scan_deficit_eq_code hfilter.1]
  apply tribonacci_code_value_not_integer_of_quadratic_ne_zero
  rw [tribonacci_deficit_code_eq_numerator, ← tribonacci_integral_deficit_10_eq]
  norm_num [tribonacciNumeratorToCubic]
  exact hfilter.2

/-- On this scan, zero quadratic coordinate means the entire exact code is
zero.  Thus the filtered count is exactly the count of nonintegral deficits. -/
theorem tribonacci_integral_scan_code_is_zero {pair : Nat × Nat}
    (hpair : pair ∈ tribonacciScanPairs)
    (hquadratic : (tribonacciScaledNumerator
      (tribonacciIntegralDeficit10 pair.1 pair.2)).quadratic = 0) :
    tribonacciDeficitCodeAt 10 pair.1 pair.2 = tribonacciCodeZero := by
  let x := tribonacciScaledNumerator
    (tribonacciIntegralDeficit10 pair.1 pair.2)
  have hxmem : x ∈ tribonacciScanNumeratorSpectrum := by
    rw [← tribonacci_scan_numerator_spectrum_exact]
    exact Finset.mem_image.mpr ⟨pair, hpair, rfl⟩
  change x.quadratic = 0 at hquadratic
  have hxzero : x = tribonacciIntegralCodeZero := by
    simp only [tribonacciScanNumeratorSpectrum, Finset.mem_insert,
      Finset.mem_singleton] at hxmem
    rcases hxmem with h | h | h | h | h | h | h | h
    · rw [h] at hquadratic
      norm_num at hquadratic
    · rw [h] at hquadratic
      norm_num at hquadratic
    · rw [h] at hquadratic
      norm_num at hquadratic
    · rw [h] at hquadratic
      norm_num at hquadratic
    · exact h
    · rw [h] at hquadratic
      norm_num at hquadratic
    · rw [h] at hquadratic
      norm_num at hquadratic
    · rw [h] at hquadratic
      norm_num at hquadratic
  rw [tribonacci_deficit_code_eq_numerator, ← tribonacci_integral_deficit_10_eq]
  change tribonacciNumeratorToCubic x = tribonacciCodeZero
  rw [hxzero]
  norm_num [tribonacciNumeratorToCubic, tribonacciIntegralCodeZero,
    tribonacciCodeZero]

theorem tribonacci_integral_of_mem_scan_complement {pair : Nat × Nat}
    (hpair : pair ∈ tribonacciScanPairs)
    (hnot : pair ∉ tribonacciNonintegralScanPairs) :
    ∃ z : Int, tribonacciDeficit pair.1 pair.2 = (z : Real) := by
  have hquadratic : (tribonacciScaledNumerator
      (tribonacciIntegralDeficit10 pair.1 pair.2)).quadratic = 0 := by
    simpa [tribonacciNonintegralScanPairs, hpair] using hnot
  refine ⟨0, ?_⟩
  rw [tribonacci_scan_deficit_eq_code hpair,
    tribonacci_integral_scan_code_is_zero hpair hquadratic]
  norm_num [tribonacciCodeValue, tribonacciCodeZero]

/-- The exact fraction lies in the interval that rounds to 44.4 percent at one
decimal place. -/
theorem tribonacci_nonintegral_scan_percentage_rounds_to_44_4 :
    (4435 : Rat) / 10000 ≤ (8934 : Rat) / 20100 ∧
      (8934 : Rat) / 20100 < 4445 / 10000 := by
  norm_num

/-- Every exact spectral value lies strictly between `-0.955` and `0.955`. -/
theorem tribonacci_scan_spectrum_bound (x : TribonacciCubicCode)
    (hx : x ∈ tribonacciScanSpectrum) :
    |tribonacciCodeValue x| < (955 : Real) / 1000 := by
  have ht := abs_lt.mp
    D5.S0.Tower.Champions.DecimalBounds.tribonacci_constant_rounding_bound
  have htLower : (1.8392865 : Real) < t := by nlinarith
  have htUpper : t < (1.8392875 : Real) := by nlinarith
  have htSqLower : (1.8392865 : Real) ^ 2 < t ^ 2 := by nlinarith [sq_nonneg (t - 1.8392865)]
  have htSqUpper : t ^ 2 < (1.8392875 : Real) ^ 2 := by
    nlinarith [sq_nonneg (1.8392875 - t)]
  simp only [tribonacciScanSpectrum, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [abs_lt] <;>
    constructor <;>
    norm_num [tribonacciCodeValue, tribonacciCodeZero] <;>
    nlinarith

/-- The real Tribonacci deficit has the certified source bound throughout the
triangular scan. -/
theorem tribonacci_deficit_scan_bound {pair : Nat × Nat}
    (hpair : pair ∈ tribonacciScanPairs) :
    |tribonacciDeficit pair.1 pair.2| < (955 : Real) / 1000 := by
  rw [tribonacci_scan_deficit_eq_code hpair]
  apply tribonacci_scan_spectrum_bound
  rw [← tribonacci_scan_spectrum_exact]
  exact Finset.mem_image.mpr ⟨pair, hpair, rfl⟩

end D5.S3.Constants.Irrationality.TribonacciDeficitScan
