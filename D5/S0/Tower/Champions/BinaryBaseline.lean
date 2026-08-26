/- GID: D5/S0/Tower/Champions/BinaryBaseline
   generality: I
   mirror-B: D5/B/S0/Tower/Champions/BinaryBaseline
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary baseline: order one, dimension one, one root, and fingerprint one. -/

import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Roots
import D5.S0.Tower.Champions.CodingFingerprint

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen binary fingerprint theorem
     `binary_coding_fingerprint_value` and the existing use of mathlib's
     `LinearRecurrence` API for Fibonacci and Tribonacci recurrences.
   * Pinned mathlib supplies `LinearRecurrence.solSpace`, its initial-value
     `basis`, `geom_sol_iff_root_charPoly`, `Module.finrank_eq_card_basis`, and
     `Polynomial.roots_X_sub_C`. These exact hits are used directly; no
     third-party theorem or local replacement recurrence framework is needed. -/

namespace D5.S0.Tower.Champions.BinaryBaseline

/-- The order-one recurrence whose only coefficient is the binary radix two. -/
def binaryGeometricRecurrence : LinearRecurrence Complex where
  order := 1
  coeffs := fun _ => 2

/-- The generated characteristic polynomial is the linear polynomial `X - 2`. -/
theorem binary_characteristic_polynomial :
    binaryGeometricRecurrence.charPoly =
      Polynomial.X - Polynomial.C (2 : Complex) := by
  rw [binaryGeometricRecurrence, LinearRecurrence.charPoly]
  simp [Polynomial.monomial_one_one_eq_X]

/-- The binary recurrence has order one, and its geometric powers form a solution. -/
theorem binary_geometric_recurrence_first_order :
    binaryGeometricRecurrence.order = 1 ∧
      binaryGeometricRecurrence.IsSolution (fun n : Nat => (2 : Complex) ^ n) := by
  constructor
  · norm_num [binaryGeometricRecurrence]
  · rw [LinearRecurrence.geom_sol_iff_root_charPoly,
      binary_characteristic_polynomial]
    simp

/-- One initial complex value parametrizes every solution of the binary recurrence. -/
theorem binary_recurrence_solution_space_finrank :
    Module.finrank Complex binaryGeometricRecurrence.solSpace = 1 := by
  rw [Module.finrank_eq_card_basis binaryGeometricRecurrence.basis]
  change Fintype.card (Fin 1) = 1
  exact Fintype.card_fin 1

/-- The binary characteristic root multiset is exactly the singleton containing two. -/
theorem binary_characteristic_roots :
    binaryGeometricRecurrence.charPoly.roots = {(2 : Complex)} := by
  rw [binary_characteristic_polynomial]
  exact Polynomial.roots_X_sub_C 2

/-- The complete binary baseline: order one, dimension one, one root, and fingerprint one. -/
theorem binary_baseline_package :
    (binaryGeometricRecurrence.order = 1 ∧
      binaryGeometricRecurrence.IsSolution (fun n : Nat => (2 : Complex) ^ n)) ∧
    Module.finrank Complex binaryGeometricRecurrence.solSpace = 1 ∧
    binaryGeometricRecurrence.charPoly.roots = {(2 : Complex)} ∧
    D5.S0.Tower.Champions.CodingFingerprint.binaryCodingFingerprint = 1 := by
  exact ⟨binary_geometric_recurrence_first_order,
    binary_recurrence_solution_space_finrank,
    binary_characteristic_roots,
    D5.S0.Tower.Champions.CodingFingerprint.binary_coding_fingerprint_value⟩

end D5.S0.Tower.Champions.BinaryBaseline
