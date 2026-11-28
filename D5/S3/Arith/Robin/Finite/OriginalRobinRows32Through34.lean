/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinRows32Through34
   generality: I
   mirror-B: none(waiver:internal-row-certificate)
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Consecutive original-price Robin rows certify an exact interval of logarithmic heights. -/

import D5.S3.Arith.Robin.Finite.OriginalRobinProductCertificates
import D5.S3.Arith.Robin.Finite.OriginalRobinRows28Through31


/-! Rows from the exact rational interval data in Jonas Whidden's Robin1984,
pinned at 5ce18bf3487c68d9353276ef5811057f60d17808. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate

open D5.S3.Weil.GronwallLowerEnvelope
open KernelProducts

set_option maxRecDepth 8192
set_option maxHeartbeats 40000000

def pinnedRow32 : Row where
  lo := (48110318623 / 1000000)
  hi := (10789326747 / 200000)
  price := (1807809003 / 1000000000000000)
  gainUpper := (9651034107219 / 500000000000)
  heightMantissa := (14266740078647197633 / 9223372036854775808)
  logLoLower := (2695312989 / 250000000)
  logHiLower := (10895750571 / 1000000000)
  heightExponent := 73685
  cuts := [51028, 310, 51, 20, 11, 7, 5, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]

theorem pinnedRow32_checks : Checks pinnedRow32 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 9651034107219) (den := 500000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 14266740078647197633) (den := 9223372036854775808)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow33 : Row where
  lo := (10789326747 / 200000)
  hi := (30165067587 / 500000)
  price := (1597827091 / 1000000000000000)
  gainUpper := (19507473855129 / 1000000000000)
  heightMantissa := (9344333232307084435 / 9223372036854775808)
  logLoLower := (10895750571 / 1000000000)
  logHiLower := (11007587011 / 1000000000)
  heightExponent := 82678
  cuts := [57137, 328, 53, 21, 11, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]

theorem pinnedRow33_checks : Checks pinnedRow33 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 19507473855129) (den := 1000000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 9344333232307084435) (den := 9223372036854775808)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow34 : Row where
  lo := (30165067587 / 500000)
  hi := (33566442549 / 500000)
  price := (1418388113 / 1000000000000000)
  gainUpper := (4925509389567 / 250000000000)
  heightMantissa := (5698791309671685549 / 4611686018427387904)
  logLoLower := (11007587011 / 1000000000)
  logHiLower := (2778607323 / 250000000)
  heightExponent := 92192
  cuts := [63731, 346, 55, 21, 12, 8, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]

theorem pinnedRow34_checks : Checks pinnedRow34 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 4925509389567) (den := 250000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 5698791309671685549) (den := 4611686018427387904)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

theorem robin_margin_through_pinned_row34 {n : ℕ} (hn : 5040 < n)
    (hhi : Real.log (n : ℝ) ≤ (pinnedRow34.hi : ℝ)) : 0 < robinLogMargin n := by
  have h31 : Real.log (n : ℝ) ≤ (pinnedRow31.hi : ℝ) → 0 < robinLogMargin n :=
    robin_margin_through_pinned_row31 hn
  have h32 : Real.log (n : ℝ) ≤ (pinnedRow32.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow32_checks.extend (by omega)
      (by simpa [pinnedRow32, pinnedRow31] using h31) height
  have h33 : Real.log (n : ℝ) ≤ (pinnedRow33.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow33_checks.extend (by omega)
      (by simpa [pinnedRow33, pinnedRow32] using h32) height
  have h34 : Real.log (n : ℝ) ≤ (pinnedRow34.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow34_checks.extend (by omega)
      (by simpa [pinnedRow34, pinnedRow33] using h33) height
  exact h34 hhi

end D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate
