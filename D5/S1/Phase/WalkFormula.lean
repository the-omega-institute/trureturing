/- GID: D5/S1/Phase/WalkFormula
   generality: G
   mirror-B: D5/B/S1/Phase/WalkFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Alternating column walks obey exact orientation and endpoint-translation laws. -/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace D5.S1.Phase.WalkFormula

/-- The alternating integer walk `a_1 - a_2 + a_3 - ...`. -/
def alternatingWalk : List ℤ → ℤ
  | [] => 0
  | coefficient :: coefficients => coefficient - alternatingWalk coefficients

/-- Concatenating coefficient blocks changes the sign of the second block
according to the parity of the first block. -/
theorem alternating_walk_append (xs ys : List ℤ) :
    alternatingWalk (xs ++ ys) =
      alternatingWalk xs + (-1 : ℤ) ^ xs.length * alternatingWalk ys := by
  induction xs with
  | nil => simp [alternatingWalk]
  | cons x xs ih =>
      simp only [List.cons_append, alternatingWalk, List.length_cons]
      rw [ih, pow_succ]
      ring

/-- Reversing a coefficient block preserves or reverses its alternating walk
according to the length parity. -/
theorem alternating_walk_reverse (xs : List ℤ) :
    alternatingWalk xs.reverse =
      (-1 : ℤ) ^ (xs.length + 1) * alternatingWalk xs := by
  induction xs with
  | nil => simp [alternatingWalk]
  | cons x xs ih =>
      rw [List.reverse_cons, alternating_walk_append]
      simp only [List.length_reverse, List.length_cons, alternatingWalk]
      rw [ih]
      simp only [pow_succ]
      ring

/-- An endpoint correction is an integer whenever the endpoint difference is
an explicit multiple of the denominator. -/
theorem endpoint_correction_is_integer
    (endpoint endpoint' c translation : ℤ) (hc : c ≠ 0)
    (htranslation : endpoint - endpoint' = c * translation) :
    ((endpoint - endpoint' : ℤ) : ℚ) / (c : ℚ) = (translation : ℚ) := by
  rw [htranslation]
  push_cast
  field_simp [Int.cast_ne_zero.mpr hc]

/-- Translating an endpoint by an integral multiple of the denominator adds
that integer to the W3 endpoint-corrected expression. -/
theorem w3_walk_endpoint_translation
    (alt endpoint endpoint' c : ℚ) (translation : ℤ) (hc : c ≠ 0) :
    3 + alt + ((endpoint + c * (translation : ℚ)) - endpoint') / c =
      (3 + alt + (endpoint - endpoint') / c) + (translation : ℚ) := by
  field_simp [hc]
  ring

end D5.S1.Phase.WalkFormula
