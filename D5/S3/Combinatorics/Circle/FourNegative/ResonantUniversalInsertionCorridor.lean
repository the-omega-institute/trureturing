/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionCorridor
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Generic two-coordinate corridor and negative-pair orientation lemmas. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionRows

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

def corridorLower (C w : ℤ) (b : Bool) : ℤ :=
  if b then 0 else (C + 1) / 2

def corridorUpper (H C w : ℤ) (b : Bool) : ℤ :=
  if b then H - (w - C) / 2 else H

theorem corridor_iff (H C w x : ℤ) (b : Bool)
    (hC : 0 ≤ C ∧ C ≤ w) :
    (0 ≤ x ∧ x ≤ H ∧
      0 ≤ 2 * x - C + w * (if b then 1 else 0) ∧
      2 * x - C + w * (if b then 1 else 0) ≤ 2 * H + 1) ↔
      (corridorLower C w b ≤ x ∧ x ≤ corridorUpper H C w b) := by
  cases b <;>
    simp only [corridorLower, corridorUpper, Bool.false_eq_true,
      Bool.true_eq, if_false, if_true] <;>
    omega

theorem negative_pair_corridor (H C w c x a p : ℤ) (b : Bool)
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hCc : C + c ≤ w)
    (hx : corridorLower C w b ≤ x ∧ x ≤ corridorUpper H C w b)
    (hz : corridorLower (C + c) w b ≤ x + a + p ∧
      x + a + p ≤ corridorUpper H (C + c) w b)
    (ha : a ≤ 0) (hp : 0 ≤ p) (hroom : p - a ≤ H - w) :
    if x + p ≤ corridorUpper H C w b then
      corridorLower C w b ≤ x + p ∧ x + p ≤ corridorUpper H C w b
    else
      corridorLower (C + c) w b ≤ x + a ∧
        x + a ≤ corridorUpper H (C + c) w b := by
  cases b <;>
    simp only [corridorLower, corridorUpper, Bool.false_eq_true,
      Bool.true_eq, if_false, if_true] at * <;>
    split_ifs <;> omega

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
