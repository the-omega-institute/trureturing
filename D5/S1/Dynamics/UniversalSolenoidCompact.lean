/- GID: D5/S1/Dynamics/UniversalSolenoidCompact
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The universal solenoid is compact as a closed subspace of a compact product. -/

import Mathlib
import D5.S1.Dynamics.UniversalSolenoid

namespace D5.S1.Dynamics.UniversalSolenoid

/-- The universal solenoid is compact because its compatibility equations cut out
a closed subspace of the compact product of unit additive circles. -/
instance : CompactSpace D5.S1.Dynamics.UniversalSolenoid := by
  have hclosed : IsClosed {theta : ℕ+ → AddCircle (1 : ℝ) |
      ∀ m n : ℕ+, n.1 • theta ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩ = theta m} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun m => isClosed_iInter fun n =>
      isClosed_eq (by fun_prop) (by fun_prop)
  exact hclosed.isClosedEmbedding_subtypeVal.compactSpace

end D5.S1.Dynamics.UniversalSolenoid
