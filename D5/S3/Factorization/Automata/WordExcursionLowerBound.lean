/- GID: D5/S3/Factorization/Automata/WordExcursionLowerBound
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/WordExcursionLowerBound
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: Word length bounds twice the excursion width minus absolute displacement. -/

import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.WordExcursionLowerBound

/-- Unrestricted displacement. -/
def displacement : List Bool → Int
  | [] => 0
  | b :: w => (if b then 1 else -1) + displacement w

/-- Least prefix displacement, including the empty prefix. -/
def low : List Bool → Int
  | [] => 0
  | b :: w => min 0 ((if b then 1 else -1) + low w)

/-- Greatest prefix displacement, including the empty prefix. -/
def high : List Bool → Int
  | [] => 0
  | b :: w => max 0 ((if b then 1 else -1) + high w)

/-- The maximum is the absolute value of the final integer displacement. -/
theorem word_length_lower_bound (w : List Bool) :
    2 * (high w - low w) - max (displacement w) (-displacement w) ≤
      (w.length : Int) := by
  have excursion_bounds : ∀ w : List Bool,
      low w ≤ 0 ∧ 0 ≤ high w ∧ low w ≤ displacement w ∧ displacement w ≤ high w := by
    intro w
    induction w with
    | nil => simp [low, high, displacement]
    | cons b w ih =>
        simp only [low, high, displacement]
        omega
  induction w with
  | nil => simp [high, low, displacement]
  | cons b w ih =>
      rcases excursion_bounds w with ⟨hl, hh, hdlo, hdhi⟩
      cases b <;>
        simp only [List.length_cons, high, low, displacement,
          reduceCtorEq, if_false, if_true, Int.natCast_add, Int.natCast_one] <;>
        omega

end D5.S3.Factorization.Automata.WordExcursionLowerBound
