/- GID: D5/S0/Tower/NonPisotFrontier/ConjugateBridge
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotFrontier/ConjugateBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The second coordinate is the value minus its conjugate over root thirteen. -/

import D5.S0.Tower.NonPisotFrontier.ExpansionEngine

/- Library-search audit trail (2026-08-18):
   * Repository search found the frontier base, its conjugate, and the
     coordinate step map; nothing relates a coordinate to the gap between the
     two embeddings.
   * Pinned Mathlib has no beta-expansion or Galois-conjugate development to
     reuse at this level of generality; the identity below is elementary. -/

namespace D5.S0.Tower.NonPisotFrontier.ConjugateBridge

open D5.S0.Tower.NonPisotFrontier.BetaThirteen
open D5.S0.Tower.NonPisotFrontier.ExpansionEngine

local notation "β" => betaThirteen
local notation "β'" => betaThirteenConjugate

/-- The two embeddings differ by the square root of thirteen. -/
theorem betaThirteen_sub_conjugate : β - β' = Real.sqrt 13 := by
  simp only [betaThirteen, betaThirteenConjugate]; ring

/-- The bridge: the second coordinate of a value is exactly the gap between that
value and its conjugate, normalised by the square root of thirteen.  A
coordinate is therefore large precisely when the two embeddings are far apart. -/
theorem second_coordinate_is_normalised_conjugate_gap (p q : Real) :
    (p + q * β) - (p + q * β') = q * Real.sqrt 13 := by
  have h := betaThirteen_sub_conjugate
  have hexpand : (p + q * β) - (p + q * β') = q * (β - β') := by ring
  rw [hexpand, h]

/-- One greedy step acts on the conjugate side by the conjugate multiplier.
This is why the conjugate orbit expands: the multiplier has modulus above one. -/
theorem conjugate_step (p q d : Real) :
    β' * (p + q * β') - d = (3 * q - d) + (p + q) * β' := by
  have hq := betaThirteenConjugate_quadratic
  have hexpand : β' * (p + q * β') = p * β' + q * β' ^ 2 := by ring
  rw [hexpand, hq]; ring

/-- The two step maps have the same integer action on coordinates.  Only the
multiplier differs, and only its modulus decides whether the orbit contracts or
expands. -/
theorem same_coordinate_action (p q d : Real) :
    (β * (p + q * β) - d = (3 * q - d) + (p + q) * β) ∧
      (β' * (p + q * β') - d = (3 * q - d) + (p + q) * β') :=
  ⟨beta_step_coordinates p q d, conjugate_step p q d⟩

/-- The frontier statement in the form this module supports: the coordinate map
is shared, the conjugate multiplier has modulus above one, and a coordinate is
the normalised gap between the embeddings.  A coordinate sequence is therefore
bounded exactly when the conjugate orbit is. -/
theorem conjugate_bridge :
    (∀ p q d : Real,
        β * (p + q * β) - d = (3 * q - d) + (p + q) * β ∧
          β' * (p + q * β') - d = (3 * q - d) + (p + q) * β') ∧
      1 < |β'| ∧
      (∀ p q : Real, (p + q * β) - (p + q * β') = q * Real.sqrt 13) :=
  ⟨fun p q d => same_coordinate_action p q d, one_lt_abs_betaThirteenConjugate,
    second_coordinate_is_normalised_conjugate_gap⟩

end D5.S0.Tower.NonPisotFrontier.ConjugateBridge
