/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinRows06Through10
   generality: I
   mirror-B: none(waiver:internal-row-certificate)
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Consecutive original-price Robin rows certify an exact interval of logarithmic heights. -/

import D5.S3.Arith.Robin.Finite.OriginalRobinProductCertificates


/-! Rows from the exact rational interval data in Jonas Whidden's Robin1984,
pinned at 5ce18bf3487c68d9353276ef5811057f60d17808. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate

open D5.S3.Weil.GronwallLowerEnvelope
open KernelProducts

set_option maxRecDepth 8192
set_option maxHeartbeats 40000000

def pinnedRow06 : Row where
  lo := (111686563 / 500000)
  hi := (163594351 / 500000)
  price := (80829194299 / 125000000000000)
  gainUpper := (9985855626483 / 1000000000000)
  heightMantissa := (9719554276707939449 / 9223372036854775808)
  logLoLower := (2704421791 / 500000000)
  logHiLower := (5790537073 / 1000000000)
  heightExponent := 412
  cuts := [274, 21, 8, 5, 3, 3, 2, 2, 2, 2]

theorem pinnedRow06_checks : Checks pinnedRow06 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 9985855626483) (den := 1000000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 9719554276707939449) (den := 9223372036854775808)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow07 : Row where
  lo := (163594351 / 500000)
  hi := (464815043 / 1000000)
  price := (422180858753 / 1000000000000000)
  gainUpper := (5297643593427 / 500000000000)
  heightMantissa := (30938683420670908437 / 18446744073709551616)
  logLoLower := (5790537073 / 1000000000)
  logHiLower := (383852473 / 62500000)
  heightExponent := 575
  cuts := [395, 26, 9, 5, 4, 3, 2, 2, 2, 2]

theorem pinnedRow07_checks : Checks pinnedRow07 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 5297643593427) (den := 500000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 30938683420670908437) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow08 : Row where
  lo := (464815043 / 1000000)
  hi := (130165559 / 200000)
  price := (70868018799 / 250000000000000)
  gainUpper := (11213775422259 / 1000000000000)
  heightMantissa := (31050297113955205021 / 18446744073709551616)
  logLoLower := (383852473 / 62500000)
  logHiLower := (3239122541 / 500000000)
  heightExponent := 811
  cuts := [557, 31, 11, 6, 4, 3, 2, 2, 2, 2, 2]

theorem pinnedRow08_checks : Checks pinnedRow08 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 11213775422259) (den := 1000000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 31050297113955205021) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow09 : Row where
  lo := (130165559 / 200000)
  hi := (893036263 / 1000000)
  price := (38967393937 / 200000000000000)
  gainUpper := (11822336604089 / 1000000000000)
  heightMantissa := (33931930940556882121 / 18446744073709551616)
  logLoLower := (3239122541 / 500000000)
  logHiLower := (6794627187 / 1000000000)
  heightExponent := 1136
  cuts := [771, 37, 12, 6, 4, 3, 3, 2, 2, 2, 2]

theorem pinnedRow09_checks : Checks pinnedRow09 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 11822336604089) (den := 1000000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 33931930940556882121) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow10 : Row where
  lo := (893036263 / 1000000)
  hi := (240770673 / 200000)
  price := (137136588803 / 1000000000000000)
  gainUpper := (2474097213021 / 200000000000)
  heightMantissa := (15720314978617663807 / 9223372036854775808)
  logLoLower := (6794627187 / 1000000000)
  logHiLower := (7093282827 / 1000000000)
  heightExponent := 1540
  cuts := [1048, 43, 13, 7, 5, 3, 3, 2, 2, 2, 2, 2]

theorem pinnedRow10_checks : Checks pinnedRow10 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 2474097213021) (den := 200000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 15720314978617663807) (den := 9223372036854775808)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

theorem robin_margin_through_pinned_row10 {n : ℕ} (hn : 5040 < n)
    (hhi : Real.log (n : ℝ) ≤ (pinnedRow10.hi : ℝ)) : 0 < robinLogMargin n := by
  have h05 : Real.log (n : ℝ) ≤ (pinnedRow05.hi : ℝ) → 0 < robinLogMargin n :=
    robin_margin_through_pinned_row05 hn
  have h06 : Real.log (n : ℝ) ≤ (pinnedRow06.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow06_checks.extend (by omega)
      (by simpa [pinnedRow06, pinnedRow05] using h05) height
  have h07 : Real.log (n : ℝ) ≤ (pinnedRow07.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow07_checks.extend (by omega)
      (by simpa [pinnedRow07, pinnedRow06] using h06) height
  have h08 : Real.log (n : ℝ) ≤ (pinnedRow08.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow08_checks.extend (by omega)
      (by simpa [pinnedRow08, pinnedRow07] using h07) height
  have h09 : Real.log (n : ℝ) ≤ (pinnedRow09.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow09_checks.extend (by omega)
      (by simpa [pinnedRow09, pinnedRow08] using h08) height
  have h10 : Real.log (n : ℝ) ≤ (pinnedRow10.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow10_checks.extend (by omega)
      (by simpa [pinnedRow10, pinnedRow09] using h09) height
  exact h10 hhi

end D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate
