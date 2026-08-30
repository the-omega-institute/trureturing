/- GID: D5/S3/Analytic/Zeta/GoldenEuler/GoldenLocalEulerFactorTrichotomy
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/GoldenEuler/GoldenLocalEulerFactorTrichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The neutral Euler channel multiplied by a quadratic charge channel gives the split, inert, and ramified local factors for charge values one, minus one, and zero. -/

import Mathlib

/- Library-search audit trail (2026-08-30):
   * Repository searches for a single owner packaging the split, inert, and
     ramified quadratic local-factor identities found no exact hit.
   * `GoldenPrimeClassification` owns the residue-class interpretation of the
     three charge values. This module owns only the universal Euler algebra.
   * Pinned Mathlib supplies field simplification and polynomial normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Zeta.GoldenEuler.GoldenLocalEulerFactorTrichotomy

universe u

variable {K : Type u} [Field K]

/-- Product of the neutral local Euler channel and one quadratic charge
channel. -/
def chargedLocalEulerFactor (charge X : K) : K :=
  1 / ((1 - X) * (1 - charge * X))

/-- A split prime contributes two degree-one local factors. -/
theorem split_local_factor (X : K) :
    chargedLocalEulerFactor (1 : K) X =
      1 / (1 - X) ^ 2 := by
  unfold chargedLocalEulerFactor
  congr 1
  ring

/-- An inert prime contributes one degree-two local factor. -/
theorem inert_local_factor (X : K) :
    chargedLocalEulerFactor (-1 : K) X =
      1 / (1 - X ^ 2) := by
  unfold chargedLocalEulerFactor
  congr 1
  ring

/-- A ramified prime loses the nontrivial quadratic charge factor. -/
theorem ramified_local_factor (X : K) :
    chargedLocalEulerFactor (0 : K) X =
      1 / (1 - X) := by
  simp [chargedLocalEulerFactor]

/-- The three charge values give a complete explicit trichotomy. -/
theorem charged_local_factor_trichotomy (charge X : K)
    (hCharge : charge = 1 ∨ charge = -1 ∨ charge = 0) :
    (charge = 1 ∧ chargedLocalEulerFactor charge X = 1 / (1 - X) ^ 2) ∨
      (charge = -1 ∧ chargedLocalEulerFactor charge X = 1 / (1 - X ^ 2)) ∨
      (charge = 0 ∧ chargedLocalEulerFactor charge X = 1 / (1 - X)) := by
  rcases hCharge with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, split_local_factor X⟩
  · exact Or.inr (Or.inl ⟨rfl, inert_local_factor X⟩)
  · exact Or.inr (Or.inr ⟨rfl, ramified_local_factor X⟩)

/-- Away from the ramified charge, squaring the charge removes the split/inert
sign while retaining that the charge is nonzero. -/
theorem quadratic_charge_square
    {charge : K} (hCharge : charge = 1 ∨ charge = -1) :
    charge ^ 2 = 1 := by
  rcases hCharge with rfl | rfl <;> ring

/-- Concrete probe in the rational-function-free scalar model. -/
example :
    chargedLocalEulerFactor (-(1 : ℚ)) (1 / 3) = 9 / 8 := by
  norm_num [chargedLocalEulerFactor]

#print axioms split_local_factor
#print axioms inert_local_factor
#print axioms ramified_local_factor
#print axioms charged_local_factor_trichotomy
#print axioms quadratic_charge_square

end D5.S3.Analytic.Zeta.GoldenEuler.GoldenLocalEulerFactorTrichotomy
