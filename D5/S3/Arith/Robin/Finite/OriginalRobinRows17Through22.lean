/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinRows17Through22
   generality: I
   mirror-B: none(waiver:internal-row-certificate)
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Consecutive original-price Robin rows certify an exact interval of logarithmic heights. -/

import D5.S3.Arith.Robin.Finite.OriginalRobinProductCertificates
import D5.S3.Arith.Robin.Finite.OriginalRobinRows11Through16


/-! Rows from the exact rational interval data in Jonas Whidden's Robin1984,
pinned at 5ce18bf3487c68d9353276ef5811057f60d17808. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate

open D5.S3.Weil.GronwallLowerEnvelope
open KernelProducts

set_option maxRecDepth 8192
set_option maxHeartbeats 40000000

def pinnedRow17 : Row where
  lo := (1248690297 / 250000)
  hi := (3045165617 / 500000)
  price := (20930175389 / 1000000000000000)
  gainUpper := (15346057284307 / 1000000000000)
  heightMantissa := (33170835240659712169 / 18446744073709551616)
  logLoLower := (4258072439 / 500000000)
  logHiLower := (2178614437 / 250000000)
  heightExponent := 8057
  cuts := [5542, 101, 24, 11, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow17_checks : Checks pinnedRow17 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 15346057284307) (den := 1000000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 33170835240659712169) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow18 : Row where
  lo := (3045165617 / 500000)
  hi := (458996953 / 62500)
  price := (16893531041 / 1000000000000000)
  gainUpper := (392261124867 / 25000000000)
  heightMantissa := (14408981146089932433 / 9223372036854775808)
  logLoLower := (2178614437 / 250000000)
  logHiLower := (2225408073 / 250000000)
  heightExponent := 9763
  cuts := [6716, 111, 25, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow18_checks : Checks pinnedRow18 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 392261124867) (den := 25000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 14408981146089932433) (den := 9223372036854775808)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow19 : Row where
  lo := (458996953 / 62500)
  hi := (4387795691 / 500000)
  price := (13794103247 / 1000000000000000)
  gainUpper := (16008228581683 / 1000000000000)
  heightMantissa := (18714211614409075569 / 18446744073709551616)
  logLoLower := (2225408073 / 250000000)
  logHiLower := (9079729439 / 1000000000)
  heightExponent := 11659
  cuts := [8059, 122, 27, 12, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow19_checks : Checks pinnedRow19 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 16008228581683) (den := 1000000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 18714211614409075569) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow20 : Row where
  lo := (4387795691 / 500000)
  hi := (10433152137 / 1000000)
  price := (11354367573 / 1000000000000000)
  gainUpper := (4081742288033 / 250000000000)
  heightMantissa := (35268474367176998613 / 18446744073709551616)
  logLoLower := (9079729439 / 1000000000)
  logHiLower := (9252743719 / 1000000000)
  heightExponent := 13935
  cuts := [9603, 133, 29, 13, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow20_checks : Checks pinnedRow20 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 4081742288033) (den := 250000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 35268474367176998613) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow21 : Row where
  lo := (10433152137 / 1000000)
  hi := (12279993269 / 1000000)
  price := (2357543377 / 250000000000000)
  gainUpper := (16624666370647 / 1000000000000)
  heightMantissa := (24285045387506838059 / 18446744073709551616)
  logLoLower := (9252743719 / 1000000000)
  logHiLower := (2353931663 / 250000000)
  heightExponent := 16454
  cuts := [11356, 145, 31, 13, 8, 6, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow21_checks : Checks pinnedRow21 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 16624666370647) (den := 1000000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 24285045387506838059) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow22 : Row where
  lo := (12279993269 / 1000000)
  hi := (179906601 / 12500)
  price := (1973616211 / 250000000000000)
  gainUpper := (16913595913191 / 1000000000000)
  heightMantissa := (9963771420256332031 / 9223372036854775808)
  logLoLower := (2353931663 / 250000000)
  logHiLower := (4787232233 / 500000000)
  heightExponent := 19344
  cuts := [13335, 157, 32, 14, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow22_checks : Checks pinnedRow22 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 16913595913191) (den := 1000000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 9963771420256332031) (den := 9223372036854775808)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

theorem robin_margin_through_pinned_row22 {n : ℕ} (hn : 5040 < n)
    (hhi : Real.log (n : ℝ) ≤ (pinnedRow22.hi : ℝ)) : 0 < robinLogMargin n := by
  have h16 : Real.log (n : ℝ) ≤ (pinnedRow16.hi : ℝ) → 0 < robinLogMargin n :=
    robin_margin_through_pinned_row16 hn
  have h17 : Real.log (n : ℝ) ≤ (pinnedRow17.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow17_checks.extend (by omega)
      (by simpa [pinnedRow17, pinnedRow16] using h16) height
  have h18 : Real.log (n : ℝ) ≤ (pinnedRow18.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow18_checks.extend (by omega)
      (by simpa [pinnedRow18, pinnedRow17] using h17) height
  have h19 : Real.log (n : ℝ) ≤ (pinnedRow19.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow19_checks.extend (by omega)
      (by simpa [pinnedRow19, pinnedRow18] using h18) height
  have h20 : Real.log (n : ℝ) ≤ (pinnedRow20.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow20_checks.extend (by omega)
      (by simpa [pinnedRow20, pinnedRow19] using h19) height
  have h21 : Real.log (n : ℝ) ≤ (pinnedRow21.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow21_checks.extend (by omega)
      (by simpa [pinnedRow21, pinnedRow20] using h20) height
  have h22 : Real.log (n : ℝ) ≤ (pinnedRow22.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow22_checks.extend (by omega)
      (by simpa [pinnedRow22, pinnedRow21] using h21) height
  exact h22 hhi

end D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate
