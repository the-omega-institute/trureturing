/- GID: D5/S3/ArithUnits/PrimeAdditiveGenerator
   generality: G
   mirror-B: D5/B/S3/ArithUnits/PrimeAdditiveGenerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every nonzero residue modulo a prime generates the additive group. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace D5.S3.ArithUnits.PrimeAdditiveGenerator

/-- Every nonzero residue modulo a prime generates the full additive group. -/
theorem nonzero_generates_additive_group (p : ℕ) (hp : Nat.Prime p) (a : ZMod p)
    (ha : a ≠ 0) : AddSubgroup.zmultiples a = ⊤ := by
  letI : Fact p.Prime := ⟨hp⟩
  apply zmultiples_eq_top_of_prime_card (p := p) ?_ ha
  simp [ZMod.card]

end D5.S3.ArithUnits.PrimeAdditiveGenerator
