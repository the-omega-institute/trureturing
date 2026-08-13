/- GID: D5/S0/Asymptotics/FixedPointFreeEscapeProbability
   generality: G
   mirror-B: D5/B/S0/Asymptotics/FixedPointFreeEscapeProbability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed-point-free twist gives uniform escape probability one. -/

import D5.S0.Diagonal.CaptureCount
import Mathlib.Data.Real.Basic

namespace D5.S0.Asymptotics.FixedPointFreeEscapeProbability

open D5.S0.Diagonal.EscapeCount

universe u v

variable {A : Type u} {Y : Type v}

/-- The uniform finite probability of escaping the twisted diagonal. -/
noncomputable def escapeProbability [Fintype A] [Fintype Y] (f : Y → Y) : ℝ :=
  (Nat.cast (Nat.card {g : A → A → Y // IsEscaped f g}) : ℝ) /
    (Nat.cast (Nat.card (A → A → Y)) : ℝ)

/-- A fixed-point-free twist escapes with uniform probability one. -/
theorem fixed_point_free_escape_probability_eq_one [Fintype A] [Fintype Y]
    [Nonempty A] [Nonempty Y] (f : Y → Y)
    (hfix : Nat.card {y : Y // f y = y} = 0) :
    escapeProbability (A := A) f = 1 := by
  classical
  rw [escapeProbability,
    D5.S0.Diagonal.CaptureCount.escaped_card_of_fixfree f hfix]
  have hden : Nat.card (A → A → Y) = Fintype.card Y ^ (Fintype.card A ^ 2) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun]
    simp [pow_two, pow_mul]
  rw [hden]
  have hY : 0 < Fintype.card Y := Fintype.card_pos
  have hPow : 0 < Fintype.card Y ^ (Fintype.card A ^ 2) := pow_pos hY _
  exact div_self (Nat.cast_ne_zero.mpr hPow.ne')

end D5.S0.Asymptotics.FixedPointFreeEscapeProbability
