/- GID: D5/S0/History/ResidualDiscrepancy
   generality: G
   mirror-B: D5/B/S0/History/ResidualDiscrepancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A discrepancy is residual exactly when observed and expected readings differ. -/

import Mathlib.Algebra.Group.Basic

/- Provenance: thin honest wrapper over pinned mathlib's `sub_ne_zero`. -/

namespace D5.S0.History.ResidualDiscrepancy

/-- The discrepancy between an observed reading and its expected reading. -/
def residualDiscrepancy {G : Type*} [AddGroup G]
    (expected observed : G) : G :=
  observed - expected

/-- A discrepancy is residual when it does not vanish. -/
def IsResidual {G : Type*} [AddGroup G]
    (expected observed : G) : Prop :=
  residualDiscrepancy expected observed ≠ 0

/-- A discrepancy is residual exactly when the observed and expected readings differ. -/
theorem residual_iff_observed_ne_expected {G : Type*} [AddGroup G]
    (expected observed : G) :
    IsResidual expected observed ↔ observed ≠ expected := by
  rw [IsResidual, residualDiscrepancy, sub_ne_zero]

end D5.S0.History.ResidualDiscrepancy
