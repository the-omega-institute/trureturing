/- GID: D5/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeBandCertificates
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/Effective/EffectivePrimeBandCertificates
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Explicit prime bands cover every real cutoff from one hundred to ten thousand. -/

import D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus
import D5.S3.Arith.GoldenResource.RobinRationalBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeBandCertificates

open Finset
open D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus
open D5.S3.Arith.GoldenResource.RobinRationalBasis

private theorem primeBandWeight_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ primeBandWeight p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold primeBandWeight
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hp0 : 0 < (p : ℝ) := by linarith
  exact div_nonneg (sub_nonneg.mpr hp2) (by positivity)

/-- A single rational certificate covers the entire closed real cutoff interval. -/
theorem interval_certificate {L U r : ℕ} {ell z : ℝ} (hL : 100 ≤ L)
    (hLz : (L : ℝ) ≤ z) (hzU : z ≤ U)
    (hr : 0 < r) (hroot : r^2 ≤ L) (hell : 0 < ell)
    (hlog : ell ≤ Real.log (L : ℝ))
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime ∧ p ≤ L ∧ 2*U < p^2)
    (hcalc : (1/20 : ℝ)*(1+1/ell) + 2/(r : ℝ) +
        (1+1/ell)/(8*(L : ℝ)*(r : ℝ)) <
      (r : ℝ)*ell*∑ p ∈ B, primeBandWeight p) :
    neededReserve z < normalizedPrimeBand z := by
  classical
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hz0 : 0 < z := hL0.trans_le hLz
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hrz : (r : ℝ) ≤ Real.sqrt z := Real.le_sqrt_of_sq_le
    ((by exact_mod_cast hroot : (r : ℝ)^2 ≤ L).trans hLz)
  have hlogz : ell ≤ Real.log z := hlog.trans (Real.log_le_log hL0 hLz)
  have hD : (r : ℝ)*ell ≤ D z :=
    mul_le_mul hrz hlogz hell.le (Real.sqrt_nonneg _)
  have hsub : B ⊆ primeBand z := by
    intro p hp
    obtain ⟨hpp,hpL,hp2⟩ := hB p hp
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor
      ((by exact_mod_cast hpL : (p : ℝ) ≤ L).trans hLz),hpp⟩,?_⟩
    have hpp2 : 2*(U : ℝ) < (p : ℝ)^2 := by exact_mod_cast hp2
    linarith only [hzU,hpp2]
  have hsum0 : 0 ≤ ∑ p ∈ B, primeBandWeight p :=
    Finset.sum_nonneg fun p hp => primeBandWeight_nonneg (hB p hp).1
  have hsum : (∑ p ∈ B, primeBandWeight p) ≤ ∑ p ∈ primeBand z, primeBandWeight p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    exact primeBandWeight_nonneg (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  have hbudget :
      neededReserve z ≤ (1/20 : ℝ)*(1+1/ell) + 2/(r : ℝ) +
        (1+1/ell)/(8*(L : ℝ)*(r : ℝ)) := by
    unfold neededReserve
    have hlog0 : 0 < Real.log z := hell.trans_le hlogz
    have hroot0 : 0 < Real.sqrt z := hr0.trans_le hrz
    gcongr
  exact hbudget.trans_lt (hcalc.trans_le
    (mul_le_mul hD hsum hsum0 (mul_nonneg (Real.sqrt_nonneg _) (hell.trans_le hlogz).le)))

private theorem band1 {z : ℝ} (hL : 100 ≤ z) (hU : z ≤ 144) :
    neededReserve z < normalizedPrimeBand z := by
  let B : Finset ℕ := {17, 19, 23, 29, 31, 37, 41, 43}
  have hlog := rational_log_bounds 100 (25 / 16) (115129 / 25000) (460519 / 100000) 6 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  apply interval_certificate (L := 100) (U := 144) (r := 10) (ell := (115129 / 25000))
    (by norm_num) (by exact hL) (by exact hU)
    (by norm_num) (by norm_num) (by norm_num) hlog.1.le B
  · decide
  · norm_num [B, primeBandWeight, Finset.sum_insert]

private theorem band2 {z : ℝ} (hL : 144 ≤ z) (hU : z ≤ 264) :
    neededReserve z < normalizedPrimeBand z := by
  let B : Finset ℕ := {23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73}
  have hlog := rational_log_bounds 144 (9 / 8) (24849 / 5000) (496983 / 100000) 7 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  apply interval_certificate (L := 144) (U := 264) (r := 12) (ell := (24849 / 5000))
    (by norm_num) (by exact hL) (by exact hU)
    (by norm_num) (by norm_num) (by norm_num) hlog.1.le B
  · decide
  · norm_num [B, primeBandWeight, Finset.sum_insert]

private theorem band3 {z : ℝ} (hL : 264 ≤ z) (hU : z ≤ 800) :
    neededReserve z < normalizedPrimeBand z := by
  let B : Finset ℕ := {41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137}
  have hlog := rational_log_bounds 264 (33 / 32) (557593 / 100000) (139399 / 25000) 8 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  apply interval_certificate (L := 264) (U := 800) (r := 16) (ell := (557593 / 100000))
    (by norm_num) (by exact hL) (by exact hU)
    (by norm_num) (by norm_num) (by norm_num) hlog.1.le B
  · decide
  · norm_num [B, primeBandWeight, Finset.sum_insert]

private theorem band4 {z : ℝ} (hL : 800 ≤ z) (hU : z ≤ 2000) :
    neededReserve z < normalizedPrimeBand z := by
  let B : Finset ℕ := {67, 71, 73, 79, 83, 89, 97, 101, 103, 107}
  have hlog := rational_log_bounds 800 (25 / 16) (33423 / 5000) (668463 / 100000) 9 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  apply interval_certificate (L := 800) (U := 2000) (r := 28) (ell := (33423 / 5000))
    (by norm_num) (by exact hL) (by exact hU)
    (by norm_num) (by norm_num) (by norm_num) hlog.1.le B
  · decide
  · norm_num [B, primeBandWeight, Finset.sum_insert]

private theorem band5 {z : ℝ} (hL : 2000 ≤ z) (hU : z ≤ 10000) :
    neededReserve z < normalizedPrimeBand z := by
  let B : Finset ℕ := {149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277}
  have hlog := rational_log_bounds 2000 (125 / 64) (760089 / 100000) (190023 / 25000) 10 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  apply interval_certificate (L := 2000) (U := 10000) (r := 44) (ell := (760089 / 100000))
    (by norm_num) (by exact hL) (by exact hU)
    (by norm_num) (by norm_num) (by norm_num) hlog.1.le B
  · decide
  · norm_num [B, primeBandWeight, Finset.sum_insert]

/-- Every actual real cutoff in the finite analytic bridge is certified. -/
theorem normalized_prime_band_finite {z : ℝ} (hz : 100 ≤ z) (hU : z ≤ 10000) :
    neededReserve z < normalizedPrimeBand z := by
  by_cases h1 : z ≤ 144
  · exact band1 hz h1
  · by_cases h2 : z ≤ 264
    · exact band2 (le_of_lt (lt_of_not_ge h1)) h2
    · by_cases h3 : z ≤ 800
      · exact band3 (le_of_lt (lt_of_not_ge h2)) h3
      · by_cases h4 : z ≤ 2000
        · exact band4 (le_of_lt (lt_of_not_ge h3)) h4
        · exact band5 (le_of_lt (lt_of_not_ge h4)) hU

end D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeBandCertificates
