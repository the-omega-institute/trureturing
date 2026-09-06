/- GID: D5/S3/Quantum/Measurements/HorizontalCasimir
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/HorizontalCasimir
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite positive multiplicity-weighted square sum vanishes exactly coordinatewise. -/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurements.HorizontalCasimir

/-- The horizontal Casimir of a finite orbit window, as defined in source lines 1977-1988. -/
def horizontalCasimir {Orbit : Type*} (T : Finset Orbit)
    (multiplicity : Orbit → ℕ) (weight displacement : Orbit → ℝ) : ℝ :=
  ∑ o ∈ T, (multiplicity o : ℝ) * weight o * displacement o ^ 2

/-- For the source's finite orbit window, right-side representatives, and strictly positive
multiplicities and weights, the horizontal Casimir vanishes exactly when every selected transverse
displacement vanishes (source lines 1556-1565 and 1990-2012). -/
theorem horizontal_casimir_eq_zero_iff {Orbit : Type*} (T : Finset Orbit)
    (multiplicity : Orbit → ℕ) (weight displacement : Orbit → ℝ)
    (multiplicityPositive : ∀ o ∈ T, 0 < multiplicity o)
    (weightPositive : ∀ o ∈ T, 0 < weight o)
    (_displacementPositive : ∀ o ∈ T, 0 < displacement o) :
    horizontalCasimir T multiplicity weight displacement = 0 ↔
      ∀ o ∈ T, displacement o = 0 := by
  fail_if_success rfl
  constructor
  · intro hzero o ho
    have hterm :
        (multiplicity o : ℝ) * weight o * displacement o ^ 2 = 0 := by
      have hterms :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i hi =>
          mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) (weightPositive i hi).le)
            (sq_nonneg _))).mp
          (by simpa only [horizontalCasimir] using hzero)
      exact hterms o ho
    have hfactorPositive : 0 < (multiplicity o : ℝ) * weight o :=
      mul_pos (Nat.cast_pos.mpr (multiplicityPositive o ho)) (weightPositive o ho)
    have hsquare : displacement o ^ 2 = 0 :=
      (mul_eq_zero.mp hterm).resolve_left hfactorPositive.ne'
    exact sq_eq_zero_iff.mp hsquare
  · intro hzero
    unfold horizontalCasimir
    apply Finset.sum_eq_zero
    intro o ho
    simp [hzero o ho]

/-- Reverse probe for CAS assertion A1: the public forward implication exposes every selected
zero displacement. -/
example {Orbit : Type*} (T : Finset Orbit)
    (multiplicity : Orbit → ℕ) (weight displacement : Orbit → ℝ)
    (multiplicityPositive : ∀ o ∈ T, 0 < multiplicity o)
    (weightPositive : ∀ o ∈ T, 0 < weight o)
    (displacementPositive : ∀ o ∈ T, 0 < displacement o)
    (hzero : horizontalCasimir T multiplicity weight displacement = 0) :
    ∀ o ∈ T, displacement o = 0 :=
  (horizontal_casimir_eq_zero_iff T multiplicity weight displacement
    multiplicityPositive weightPositive displacementPositive).mp hzero

/-- Reverse probe for CAS assertion A2: pointwise vanishing gives zero horizontal Casimir. -/
example {Orbit : Type*} (T : Finset Orbit)
    (multiplicity : Orbit → ℕ) (weight displacement : Orbit → ℝ)
    (multiplicityPositive : ∀ o ∈ T, 0 < multiplicity o)
    (weightPositive : ∀ o ∈ T, 0 < weight o)
    (displacementPositive : ∀ o ∈ T, 0 < displacement o)
    (hzero : ∀ o ∈ T, displacement o = 0) :
    horizontalCasimir T multiplicity weight displacement = 0 :=
  (horizontal_casimir_eq_zero_iff T multiplicity weight displacement
    multiplicityPositive weightPositive displacementPositive).mpr hzero

/-- A concrete nonempty window has positive carrier data and a nonzero horizontal Casimir. -/
example :
    0 < horizontalCasimir (Finset.univ : Finset (Fin 1))
      (fun _ => 2) (fun _ => 3) (fun _ => 4) := by
  norm_num [horizontalCasimir]

/-- The same concrete nontrivial data satisfy the public equivalence. -/
example :
    horizontalCasimir (Finset.univ : Finset (Fin 1))
        (fun _ => 2) (fun _ => 3) (fun _ => 4) = 0 ↔
      ∀ o ∈ (Finset.univ : Finset (Fin 1)), (4 : ℝ) = 0 := by
  apply horizontal_casimir_eq_zero_iff
  · simp
  · simp
  · simp

#print axioms horizontal_casimir_eq_zero_iff

end D5.S3.Quantum.Measurements.HorizontalCasimir
