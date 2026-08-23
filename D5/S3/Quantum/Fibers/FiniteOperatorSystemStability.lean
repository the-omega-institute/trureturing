/- GID: D5/S3/Quantum/Fibers/FiniteOperatorSystemStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/FiniteOperatorSystemStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite operator-system stability at one step persists at every later step. -/

import D5.S3.Quantum.Fibers.OperatorSystemTowerStability

/- Library-search audit trail (2026-08-24):
   * Exact current-tree hit
     `OperatorSystemTowerStability.operator_system_tower_once_stable_permanently`
     already constructs the source tower from a unital completely positive map on
     finite complex matrices and proves the required permanent stability statement.
   * The exact hit is imported and applied directly below. Its canonical
     `MatrixAlgebra`, `MatrixOperatorSystem`, and `predictionTower` definitions are
     reused as the family single source of truth; no sibling primitives are declared.
   * The pinned Mathlib fixed-point result used by the exact hit is
     `Function.iterate_fixed`. Repository and `_eq_` searches found no other
     operator-system tower primitive or distinct theorem requiring reconciliation.
   * `loogle` and `leansearch` executables are absent from PATH on this lane. -/

noncomputable section

open scoped CStarAlgebra ComplexOrder

namespace D5.S3.Quantum.Fibers.FiniteOperatorSystemStability

open D5.S3.Quantum.Fibers.OperatorSystemTowerStability

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- In finite dimension, equality of consecutive stages of the source-constructed
operator-system tower forces equality with every later stage. -/
theorem finite_operator_system_once_stable_permanently
    (heisenberg : MatrixAlgebra d →CP MatrixAlgebra d)
    (heisenbergUnital : heisenberg 1 = 1)
    (initial : MatrixOperatorSystem d) (m : ℕ)
    (hStable : predictionTower heisenberg initial m =
      predictionTower heisenberg initial (m + 1)) :
    ∀ r : ℕ, predictionTower heisenberg initial (m + r) =
      predictionTower heisenberg initial m := by
  exact operator_system_tower_once_stable_permanently
    heisenberg heisenbergUnital initial m hStable

#print axioms finite_operator_system_once_stable_permanently

end D5.S3.Quantum.Fibers.FiniteOperatorSystemStability
