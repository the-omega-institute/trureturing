/- GID: D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge
   generality: I
   mirror-B: D5/B/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Residues modulo five select the split, inert, and ramified charge values used by the golden local Euler factor. -/

import D5.S3.PrimeForms.GoldenEuler.GoldenLocalEulerTrichotomy
import D5.S3.PrimeForms.GoldenPrimeClassification

/-!
The repository already owns the theorem that prime splitting in the golden
integers is controlled by residues modulo five. This file adds only the typed
bridge from those residue classes to the three charge values used by the local
Euler denominator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.GoldenEuler.GoldenResidueChargeBridge

open D5.S3.PrimeForms.GoldenEuler.GoldenLocalEulerTrichotomy

/-- Quadratic golden charge read from a natural residue modulo five. -/
def goldenResidueCharge (p : ℕ) : ℝ :=
  if p % 5 = 1 ∨ p % 5 = 4 then 1
  else if p % 5 = 2 ∨ p % 5 = 3 then -1
  else 0

/-- Split residues carry positive charge. -/
theorem golden_residue_charge_split {p : ℕ}
    (h : p % 5 = 1 ∨ p % 5 = 4) :
    goldenResidueCharge p = 1 := by
  simp [goldenResidueCharge, h]

/-- Inert residues carry negative charge. -/
theorem golden_residue_charge_inert {p : ℕ}
    (h : p % 5 = 2 ∨ p % 5 = 3) :
    goldenResidueCharge p = -1 := by
  have hNotSplit : ¬ (p % 5 = 1 ∨ p % 5 = 4) := by omega
  simp [goldenResidueCharge, hNotSplit, h]

/-- The ramified prime five carries charge zero. -/
@[simp] theorem golden_residue_charge_five :
    goldenResidueCharge 5 = 0 := by
  norm_num [goldenResidueCharge]

/-- Split residue classes select the split local denominator. -/
theorem split_residue_local_denominator {p : ℕ}
    (h : p % 5 = 1 ∨ p % 5 = 4) (X : ℝ) :
    goldenLocalDenominator (goldenResidueCharge p) X = (1 - X) ^ 2 := by
  rw [golden_residue_charge_split h, split_local_denominator]

/-- Inert residue classes select the inert local denominator. -/
theorem inert_residue_local_denominator {p : ℕ}
    (h : p % 5 = 2 ∨ p % 5 = 3) (X : ℝ) :
    goldenLocalDenominator (goldenResidueCharge p) X = 1 - X ^ 2 := by
  rw [golden_residue_charge_inert h, inert_local_denominator]

/-- The ramified prime selects the ramified local denominator. -/
theorem ramified_five_local_denominator (X : ℝ) :
    goldenLocalDenominator (goldenResidueCharge 5) X = 1 - X := by
  rw [golden_residue_charge_five, ramified_local_denominator]

#print axioms golden_residue_charge_split
#print axioms golden_residue_charge_inert
#print axioms golden_residue_charge_five
#print axioms split_residue_local_denominator
#print axioms inert_residue_local_denominator
#print axioms ramified_five_local_denominator

end D5.S3.PrimeForms.GoldenEuler.GoldenResidueChargeBridge
