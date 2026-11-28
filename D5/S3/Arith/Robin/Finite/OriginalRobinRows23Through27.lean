/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinRows23Through27
   generality: I
   mirror-B: none(waiver:internal-row-certificate)
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Consecutive original-price Robin rows certify an exact interval of logarithmic heights. -/

import D5.S3.Arith.Robin.Finite.OriginalRobinProductCertificates
import D5.S3.Arith.Robin.Finite.OriginalRobinRows17Through22


/-! Rows from the exact rational interval data in Jonas Whidden's Robin1984,
pinned at 5ce18bf3487c68d9353276ef5811057f60d17808. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate

open D5.S3.Weil.GronwallLowerEnvelope
open KernelProducts

set_option maxRecDepth 8192
set_option maxHeartbeats 40000000

def pinnedRow23 : Row where
  lo := (179906601 / 12500)
  hi := (16784073643 / 1000000)
  price := (6644793849 / 1000000000000000)
  gainUpper := (8596022645987 / 500000000000)
  heightMantissa := (30742308875954151977 / 18446744073709551616)
  logLoLower := (4787232233 / 500000000)
  logHiLower := (9728185717 / 1000000000)
  heightExponent := 22606
  cuts := [15587, 170, 34, 15, 9, 6, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow23_checks : Checks pinnedRow23 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 8596022645987) (den := 500000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 30742308875954151977) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow24 : Row where
  lo := (16784073643 / 1000000)
  hi := (9718846411 / 500000)
  price := (1126354703 / 200000000000000)
  gainUpper := (4364402569827 / 250000000000)
  heightMantissa := (24737355459205177439 / 18446744073709551616)
  logLoLower := (9728185717 / 1000000000)
  logHiLower := (9874969387 / 1000000000)
  heightExponent := 26225
  cuts := [18110, 184, 36, 15, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow24_checks : Checks pinnedRow24 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 4364402569827) (den := 250000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 24737355459205177439) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow25 : Row where
  lo := (9718846411 / 500000)
  hi := (22433188173 / 1000000)
  price := (1200244709 / 250000000000000)
  gainUpper := (354242307219 / 20000000000)
  heightMantissa := (31629297847177716087 / 18446744073709551616)
  logLoLower := (9874969387 / 1000000000)
  logHiLower := (2003659351 / 200000000)
  heightExponent := 30244
  cuts := [20934, 197, 38, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]

theorem pinnedRow25_checks : Checks pinnedRow25 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 354242307219) (den := 20000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 31629297847177716087) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow26 : Row where
  lo := (22433188173 / 1000000)
  hi := (1287242339 / 50000)
  price := (2057220229 / 500000000000000)
  gainUpper := (3594193175181 / 200000000000)
  heightMantissa := (30201260215318202501 / 18446744073709551616)
  logLoLower := (2003659351 / 200000000)
  logHiLower := (7934367 / 781250)
  heightExponent := 34958
  cuts := [24088, 212, 40, 16, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]

theorem pinnedRow26_checks : Checks pinnedRow26 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 3594193175181) (den := 200000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 30201260215318202501) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow27 : Row where
  lo := (1287242339 / 50000)
  hi := (7349340853 / 250000)
  price := (3547339421 / 1000000000000000)
  gainUpper := (4551087575717 / 250000000000)
  heightMantissa := (7516258340239357411 / 4611686018427387904)
  logLoLower := (7934367 / 781250)
  logHiLower := (2572165067 / 250000000)
  heightExponent := 39837
  cuts := [27570, 227, 41, 17, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]

theorem pinnedRow27_checks : Checks pinnedRow27 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 4551087575717) (den := 250000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 7516258340239357411) (den := 4611686018427387904)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

theorem robin_margin_through_pinned_row27 {n : ℕ} (hn : 5040 < n)
    (hhi : Real.log (n : ℝ) ≤ (pinnedRow27.hi : ℝ)) : 0 < robinLogMargin n := by
  have h22 : Real.log (n : ℝ) ≤ (pinnedRow22.hi : ℝ) → 0 < robinLogMargin n :=
    robin_margin_through_pinned_row22 hn
  have h23 : Real.log (n : ℝ) ≤ (pinnedRow23.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow23_checks.extend (by omega)
      (by simpa [pinnedRow23, pinnedRow22] using h22) height
  have h24 : Real.log (n : ℝ) ≤ (pinnedRow24.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow24_checks.extend (by omega)
      (by simpa [pinnedRow24, pinnedRow23] using h23) height
  have h25 : Real.log (n : ℝ) ≤ (pinnedRow25.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow25_checks.extend (by omega)
      (by simpa [pinnedRow25, pinnedRow24] using h24) height
  have h26 : Real.log (n : ℝ) ≤ (pinnedRow26.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow26_checks.extend (by omega)
      (by simpa [pinnedRow26, pinnedRow25] using h25) height
  have h27 : Real.log (n : ℝ) ≤ (pinnedRow27.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow27_checks.extend (by omega)
      (by simpa [pinnedRow27, pinnedRow26] using h26) height
  exact h27 hhi

end D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate
