/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinRows11Through16
   generality: I
   mirror-B: none(waiver:internal-row-certificate)
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Consecutive original-price Robin rows certify an exact interval of logarithmic heights. -/

import D5.S3.Arith.Robin.Finite.OriginalRobinProductCertificates
import D5.S3.Arith.Robin.Finite.OriginalRobinRows06Through10


/-! Rows from the exact rational interval data in Jonas Whidden's Robin1984,
pinned at 5ce18bf3487c68d9353276ef5811057f60d17808. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate

open D5.S3.Weil.GronwallLowerEnvelope
open KernelProducts

set_option maxRecDepth 8192
set_option maxHeartbeats 40000000

def pinnedRow11 : Row where
  lo := (240770673 / 200000)
  hi := (63176719 / 40000)
  price := (99275427189 / 1000000000000000)
  gainUpper := (6429631547689 / 500000000000)
  heightMantissa := (2443405932771137419 / 2305843009213693952)
  logLoLower := (7093282827 / 1000000000)
  logHiLower := (3682405843 / 500000000)
  heightExponent := 2017
  cuts := [1391, 50, 15, 8, 5, 4, 3, 2, 2, 2, 2, 2]

theorem pinnedRow11_checks : Checks pinnedRow11 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 6429631547689) (den := 500000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 2443405932771137419) (den := 2305843009213693952)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow12 : Row where
  lo := (63176719 / 40000)
  hi := (2035337871 / 1000000)
  price := (73775311097 / 1000000000000000)
  gainUpper := (6672846362753 / 500000000000)
  heightMantissa := (19729626364661406045 / 18446744073709551616)
  logLoLower := (3682405843 / 500000000)
  logHiLower := (7618417113 / 1000000000)
  heightExponent := 2642
  cuts := [1806, 57, 16, 8, 5, 4, 3, 3, 2, 2, 2, 2, 2]

theorem pinnedRow12_checks : Checks pinnedRow12 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 6672846362753) (den := 500000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 19729626364661406045) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow13 : Row where
  lo := (2035337871 / 1000000)
  hi := (518900301 / 200000)
  price := (11152011487 / 200000000000000)
  gainUpper := (13784169975911 / 1000000000000)
  heightMantissa := (29021999988660336459 / 18446744073709551616)
  logLoLower := (7618417113 / 1000000000)
  logHiLower := (7861149677 / 1000000000)
  heightExponent := 3373
  cuts := [2314, 65, 18, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2]

theorem pinnedRow13_checks : Checks pinnedRow13 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 13784169975911) (den := 1000000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 29021999988660336459) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow14 : Row where
  lo := (518900301 / 200000)
  hi := (815385537 / 250000)
  price := (42786768497 / 1000000000000000)
  gainUpper := (1421791828229 / 100000000000)
  heightMantissa := (12095416622684725185 / 9223372036854775808)
  logLoLower := (7861149677 / 1000000000)
  logHiLower := (8089955413 / 1000000000)
  heightExponent := 4294
  cuts := [2927, 73, 19, 9, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow14_checks : Checks pinnedRow14 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 1421791828229) (den := 100000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 12095416622684725185) (den := 9223372036854775808)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow15 : Row where
  lo := (815385537 / 250000)
  hi := (406392661 / 100000)
  price := (6654185407 / 200000000000000)
  gainUpper := (91279065703 / 6250000000)
  heightMantissa := (97982466908525699 / 72057594037927936)
  logLoLower := (8089955413 / 1000000000)
  logHiLower := (8309904929 / 1000000000)
  heightExponent := 5329
  cuts := [3662, 82, 21, 10, 6, 4, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow15_checks : Checks pinnedRow15 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 91279065703) (den := 6250000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 97982466908525699) (den := 72057594037927936)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow16 : Row where
  lo := (406392661 / 100000)
  hi := (1248690297 / 250000)
  price := (2622639723 / 100000000000000)
  gainUpper := (7493566089191 / 500000000000)
  heightMantissa := (32862165079507178585 / 18446744073709551616)
  logLoLower := (8309904929 / 1000000000)
  logHiLower := (4258072439 / 500000000)
  heightExponent := 6593
  cuts := [4528, 91, 22, 10, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2]

theorem pinnedRow16_checks : Checks pinnedRow16 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 7493566089191) (den := 500000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 32862165079507178585) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

theorem robin_margin_through_pinned_row16 {n : ℕ} (hn : 5040 < n)
    (hhi : Real.log (n : ℝ) ≤ (pinnedRow16.hi : ℝ)) : 0 < robinLogMargin n := by
  have h10 : Real.log (n : ℝ) ≤ (pinnedRow10.hi : ℝ) → 0 < robinLogMargin n :=
    robin_margin_through_pinned_row10 hn
  have h11 : Real.log (n : ℝ) ≤ (pinnedRow11.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow11_checks.extend (by omega)
      (by simpa [pinnedRow11, pinnedRow10] using h10) height
  have h12 : Real.log (n : ℝ) ≤ (pinnedRow12.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow12_checks.extend (by omega)
      (by simpa [pinnedRow12, pinnedRow11] using h11) height
  have h13 : Real.log (n : ℝ) ≤ (pinnedRow13.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow13_checks.extend (by omega)
      (by simpa [pinnedRow13, pinnedRow12] using h12) height
  have h14 : Real.log (n : ℝ) ≤ (pinnedRow14.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow14_checks.extend (by omega)
      (by simpa [pinnedRow14, pinnedRow13] using h13) height
  have h15 : Real.log (n : ℝ) ≤ (pinnedRow15.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow15_checks.extend (by omega)
      (by simpa [pinnedRow15, pinnedRow14] using h14) height
  have h16 : Real.log (n : ℝ) ≤ (pinnedRow16.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow16_checks.extend (by omega)
      (by simpa [pinnedRow16, pinnedRow15] using h15) height
  exact h16 hhi

end D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate
