/- GID: D5/S0/Asymptotics/EscapeProbability/ProbabilityBounds
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/ProbabilityBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform escape probability lies in the closed unit interval. -/

import D5.S0.Asymptotics.FixedPointFreeEscapeProbability
import Mathlib.SetTheory.Cardinal.NatCard

/- Library-search audit trail (2026-08-16):
   * Pinned Mathlib provides `Finite.card_subtype_le`, which is applied to the
     escaped-listing subtype below.
   * Pinned Mathlib provides `div_nonneg` and `div_le_one_of_le₀`; applying
     them handles an empty listing space without a separate nonzero case.
   * Repository searches found no bound theorem for the frozen uniform
     `escapeProbability` outside the independently weighted model. -/

namespace D5.S0.Asymptotics.EscapeProbability.ProbabilityBounds

open D5.S0.Asymptotics.FixedPointFreeEscapeProbability
open D5.S0.Diagonal.EscapeCount

universe u v

variable {A : Type u} {Y : Type v}

/-- Uniform escape probability is between zero and one, including when the
finite listing space is empty. -/
theorem escape_probability_bounds [Fintype A] [Fintype Y] (f : Y -> Y) :
    0 <= escapeProbability (A := A) f /\
      escapeProbability (A := A) f <= 1 := by
  classical
  rw [escapeProbability]
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply div_le_one_of_le₀
    · exact_mod_cast Finite.card_subtype_le
        (fun g : A -> A -> Y => IsEscaped f g)
    · exact Nat.cast_nonneg _

example [Fintype A] [Fintype Y] (f : Y -> Y) :
    0 <= escapeProbability (A := A) f /\
      escapeProbability (A := A) f <= 1 := by
  exact escape_probability_bounds f

example : Fin 1 := 0

example :
    0 <= escapeProbability (A := Fin 1) Bool.not /\
      escapeProbability (A := Fin 1) Bool.not <= 1 := by
  exact escape_probability_bounds Bool.not

#print axioms escape_probability_bounds

end D5.S0.Asymptotics.EscapeProbability.ProbabilityBounds
