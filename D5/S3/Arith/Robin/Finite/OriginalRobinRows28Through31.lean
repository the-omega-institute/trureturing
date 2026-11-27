/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinRows28Through31
   generality: I
   mirror-B: none(waiver:internal-row-certificate)
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Consecutive original-price Robin rows certify an exact interval of logarithmic heights. -/

import D5.S3.Arith.Robin.Finite.OriginalRobinProductCertificates
import D5.S3.Arith.Robin.Finite.OriginalRobinRows23Through27


/-! Rows from the exact rational interval data in Jonas Whidden's Robin1984,
pinned at 5ce18bf3487c68d9353276ef5811057f60d17808. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate

open D5.S3.Weil.GronwallLowerEnvelope
open KernelProducts

set_option maxRecDepth 8192
set_option maxHeartbeats 40000000

def pinnedRow28 : Row where
  lo := (7349340853 / 250000)
  hi := (1338267981 / 40000)
  price := (3072760897 / 1000000000000000)
  gainUpper := (1843931474441 / 100000000000)
  heightMantissa := (15332415054936259621 / 9223372036854775808)
  logLoLower := (2572165067 / 250000000)
  logHiLower := (10418007329 / 1000000000)
  heightExponent := 45443
  cuts := [31426, 242, 43, 18, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2]

theorem pinnedRow28_checks : Checks pinnedRow28 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 1843931474441) (den := 100000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 15332415054936259621) (den := 9223372036854775808)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow29 : Row where
  lo := (1338267981 / 40000)
  hi := (9481137173 / 250000)
  price := (2672852847 / 1000000000000000)
  gainUpper := (9333484697593 / 500000000000)
  heightMantissa := (1323398228959304581 / 1152921504606846976)
  logLoLower := (10418007329 / 1000000000)
  logHiLower := (10543353903 / 1000000000)
  heightExponent := 51624
  cuts := [35690, 258, 45, 18, 10, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2]

theorem pinnedRow29_checks : Checks pinnedRow29 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 9333484697593) (den := 500000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 1323398228959304581) (den := 1152921504606846976)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow30 : Row where
  lo := (9481137173 / 250000)
  hi := (1070418171 / 25000)
  price := (2335546837 / 1000000000000000)
  gainUpper := (9442891043759 / 500000000000)
  heightMantissa := (25881087461094799483 / 18446744073709551616)
  logLoLower := (10543353903 / 1000000000)
  logHiLower := (5332342059 / 500000000)
  heightExponent := 58355
  cuts := [40370, 275, 47, 19, 11, 7, 5, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2]

theorem pinnedRow30_checks : Checks pinnedRow30 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 9442891043759) (den := 500000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 25881087461094799483) (den := 18446744073709551616)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

def pinnedRow31 : Row where
  lo := (1070418171 / 25000)
  hi := (48110318623 / 1000000)
  price := (2050940953 / 1000000000000000)
  gainUpper := (9549440395651 / 500000000000)
  heightMantissa := (6136820303832988357 / 4611686018427387904)
  logLoLower := (5332342059 / 500000000)
  logHiLower := (2695312989 / 250000000)
  heightExponent := 65750
  cuts := [45463, 292, 49, 19, 11, 7, 5, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]

theorem pinnedRow31_checks : Checks pinnedRow31 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row_gain (by decide +kernel) (num := 9549440395651) (den := 500000000000)
    (by decide) rfl (by decide +kernel)
  height := row_height (by decide +kernel) (num := 6136820303832988357) (den := 4611686018427387904)
    (by decide) rfl (by decide +kernel)
  left := by decide +kernel
  right := by decide +kernel

theorem robin_margin_through_pinned_row31 {n : ℕ} (hn : 5040 < n)
    (hhi : Real.log (n : ℝ) ≤ (pinnedRow31.hi : ℝ)) : 0 < robinLogMargin n := by
  have h27 : Real.log (n : ℝ) ≤ (pinnedRow27.hi : ℝ) → 0 < robinLogMargin n :=
    robin_margin_through_pinned_row27 hn
  have h28 : Real.log (n : ℝ) ≤ (pinnedRow28.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow28_checks.extend (by omega)
      (by simpa [pinnedRow28, pinnedRow27] using h27) height
  have h29 : Real.log (n : ℝ) ≤ (pinnedRow29.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow29_checks.extend (by omega)
      (by simpa [pinnedRow29, pinnedRow28] using h28) height
  have h30 : Real.log (n : ℝ) ≤ (pinnedRow30.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow30_checks.extend (by omega)
      (by simpa [pinnedRow30, pinnedRow29] using h29) height
  have h31 : Real.log (n : ℝ) ≤ (pinnedRow31.hi : ℝ) → 0 < robinLogMargin n := by
    intro height
    exact pinnedRow31_checks.extend (by omega)
      (by simpa [pinnedRow31, pinnedRow30] using h30) height
  exact h31 hhi

end D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate
