/- GID: D5/S0/Certificates/RationalAffineMomentCompression
   generality: G
   mirror-B: D5/B/S0/Certificates/RationalAffineMomentCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Certificates/RationalMomentReplay]
   utility: kind=checker; basis=consumer=D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.checked_affine_causal_witness
   digest: Exact support-local affine reconstruction lets the existing rational replay preserve a full moment family while checking only selected coordinates and their smaller support budget. -/

import D5.S0.Certificates.RationalMomentReplay

/- Library audit (2026-09-06): reuse linearObjective, activeAtoms,
   checkCompression, and checkCompression_sound. A proposed affine coordinate
   presentation is verified pointwise on the original active support, which
   the existing replay cannot enlarge. No rank or linear-independence claim is
   inferred from the number of selected coordinates. No RREF solver is added. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.RationalAffineMomentCompression

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S0.Certificates.RationalMomentElimination
open D5.S0.Certificates.RationalMomentReplay

/-- A rational affine readout of a fixed finite feature vector. -/
def affineCoefficient {n r : Nat} (feature : Fin n → Fin r → ℚ)
    (constant : ℚ) (coefficient : Fin r → ℚ) (i : Fin n) : ℚ :=
  constant + ∑ j, coefficient j * feature i j

/-- For normalized weights, expectation commutes with affine reconstruction. -/
theorem linearObjective_affineCoefficient {n r : Nat}
    (feature : Fin n → Fin r → ℚ) (weight : Fin n → ℚ)
    (total : (∑ i, weight i) = 1) (constant : ℚ) (coefficient : Fin r → ℚ) :
    linearObjective (affineCoefficient feature constant coefficient) weight =
      constant + ∑ j, coefficient j * linearObjective (fun i => feature i j) weight := by
  unfold linearObjective affineCoefficient
  calc
    (∑ i, (constant + ∑ j, coefficient j * feature i j) * weight i) =
        (∑ i, constant * weight i) + ∑ i, ∑ j, (coefficient j * feature i j) * weight i := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    _ = constant + ∑ j, coefficient j * (∑ i, feature i j * weight i) := by
      rw [← Finset.mul_sum, total, mul_one, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Coefficients need only agree at nonzero atoms to have the same expectation. -/
theorem linearObjective_congr_on_active {n : Nat}
    (weight first second : Fin n → ℚ)
    (agree : ∀ i, weight i ≠ 0 → first i = second i) :
    linearObjective first weight = linearObjective second weight := by
  unfold linearObjective
  apply Finset.sum_congr rfl
  intro i _
  by_cases zero : weight i = 0
  · simp only [zero, mul_zero]
  · rw [agree i zero]

/-- Successful replay necessarily started from a probability vector. -/
theorem checkCompression_input_probability {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (weight result : Fin n → ℚ)
    (steps : List (EliminationStep n))
    (accepted : checkCompression feature weight steps = some result) :
    (∀ i, 0 ≤ weight i) ∧ (∑ i, weight i) = 1 := by
  by_contra invalid
  simp only [checkCompression, if_neg invalid] at accepted
  cases accepted

/-- Data-only affine presentation by selected original coordinates. The selected
coordinates may be redundant; this certifies an upper dimension bound only. -/
structure AffinePresentation (d r : Nat) where
  selected : Fin r → Fin d
  offset : Fin d → ℚ
  coefficient : Fin d → Fin r → ℚ

/-- Use actual original coordinates rather than an unrelated reduced feature map. -/
def selectedFeature {n d r : Nat} (feature : Fin n → Fin d → ℚ)
    (presentation : AffinePresentation d r) : Fin n → Fin r → ℚ :=
  fun i j => feature i (presentation.selected j)

/-- Every original feature is reconstructed on the entire original active support. -/
def ValidPresentation {n d r : Nat} (feature : Fin n → Fin d → ℚ)
    (weight : Fin n → ℚ) (presentation : AffinePresentation d r) : Prop :=
  ∀ i, weight i ≠ 0 → ∀ j,
    feature i j = affineCoefficient (selectedFeature feature presentation)
      (presentation.offset j) (presentation.coefficient j) i

/-- Executable pointwise check of the affine presentation. -/
def checkPresentation {n d r : Nat} (feature : Fin n → Fin d → ℚ)
    (weight : Fin n → ℚ) (presentation : AffinePresentation d r) : Bool :=
  @decide (ValidPresentation feature weight presentation)
    (by unfold ValidPresentation; infer_instance)

theorem checkPresentation_eq_true_iff {n d r : Nat}
    (feature : Fin n → Fin d → ℚ) (weight : Fin n → ℚ)
    (presentation : AffinePresentation d r) :
    checkPresentation feature weight presentation = true ↔
      ValidPresentation feature weight presentation := by
  simp only [checkPresentation, decide_eq_true_eq]

/-- Check the presentation, then reuse the existing replay on the selected
coordinates. Its final support threshold is r+1 rather than d+1. -/
def checkAffineCompression {n d r : Nat} (feature : Fin n → Fin d → ℚ)
    (weight : Fin n → ℚ) (presentation : AffinePresentation d r)
    (steps : List (EliminationStep n)) : Option (Fin n → ℚ) :=
  if checkPresentation feature weight presentation = true then
    checkCompression (selectedFeature feature presentation) weight steps
  else none

/-- Acceptance preserves every original moment, including omitted coordinates,
with normalized nonnegative output and no new support atoms. -/
theorem checkAffineCompression_sound {n d r : Nat}
    (feature : Fin n → Fin d → ℚ) (weight result : Fin n → ℚ)
    (presentation : AffinePresentation d r) (steps : List (EliminationStep n))
    (accepted : checkAffineCompression feature weight presentation steps = some result) :
    (∀ i, 0 ≤ result i) ∧ (∑ i, result i) = 1 ∧
    activeAtoms result ⊆ activeAtoms weight ∧
    (activeAtoms result).card ≤ r + 1 ∧
    (∀ j, linearObjective (fun i => feature i j) result =
      linearObjective (fun i => feature i j) weight) := by
  by_cases checked : checkPresentation feature weight presentation = true
  · have valid := (checkPresentation_eq_true_iff feature weight presentation).mp checked
    have replay : checkCompression (selectedFeature feature presentation) weight steps = some result := by
      simpa only [checkAffineCompression, if_pos checked] using accepted
    have input := checkCompression_input_probability _ weight result steps replay
    obtain ⟨nonnegative, total, moments, contained, small, _⟩ :=
      checkCompression_sound _ weight result steps replay
    refine ⟨nonnegative, total, contained, small, ?_⟩
    intro j
    have input_eq : linearObjective (fun i => feature i j) weight =
        linearObjective (affineCoefficient (selectedFeature feature presentation)
          (presentation.offset j) (presentation.coefficient j)) weight :=
      linearObjective_congr_on_active weight _ _ (fun i hi => valid i hi j)
    have output_eq : linearObjective (fun i => feature i j) result =
        linearObjective (affineCoefficient (selectedFeature feature presentation)
          (presentation.offset j) (presentation.coefficient j)) result := by
      apply linearObjective_congr_on_active
      intro i hi
      have original := contained (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      exact valid i (Finset.mem_filter.mp original).2 j
    rw [output_eq, input_eq,
      linearObjective_affineCoefficient _ result total,
      linearObjective_affineCoefficient _ weight input.2]
    simp_rw [moments]
  · simp only [checkAffineCompression, if_neg checked] at accepted
    cases accepted

/-- One accepted compression preserves every affine query of the full retained
feature vector, for arbitrary coefficients chosen after the compression. -/
theorem checkAffineCompression_preserves_affine_family {n d r : Nat}
    (feature : Fin n → Fin d → ℚ) (weight result : Fin n → ℚ)
    (presentation : AffinePresentation d r) (steps : List (EliminationStep n))
    (accepted : checkAffineCompression feature weight presentation steps = some result) :
    ∀ (constant : ℚ) (coefficient : Fin d → ℚ),
      linearObjective (affineCoefficient feature constant coefficient) result =
        linearObjective (affineCoefficient feature constant coefficient) weight := by
  obtain ⟨_, total, _, _, moments⟩ :=
    checkAffineCompression_sound feature weight result presentation steps accepted
  have replay : checkCompression (selectedFeature feature presentation) weight steps = some result := by
    by_cases checked : checkPresentation feature weight presentation = true
    · simpa only [checkAffineCompression, if_pos checked] using accepted
    · simp only [checkAffineCompression, if_neg checked] at accepted
      cases accepted
  have input := checkCompression_input_probability _ weight result steps replay
  intro constant coefficient
  rw [linearObjective_affineCoefficient feature result total,
    linearObjective_affineCoefficient feature weight input.2]
  simp_rw [moments]

/-- Three redundant feature coordinates reduce to one certified coordinate.
The uniform four-point law is replayed to two endpoints, preserving all three. -/
theorem affine_reconstruction_replay_example :
    (checkAffineCompression (n := 4) (d := 3) (r := 1)
      (fun i j => if j = 0 then (i.val : ℚ)
        else if j = 1 then 3 + 2 * (i.val : ℚ) else 5 - (i.val : ℚ))
      (fun _ => 1 / 4)
      { selected := fun _ => 0
        offset := fun j => if j = 0 then 0 else if j = 1 then 3 else 5
        coefficient := fun j _ => if j = 0 then 1 else if j = 1 then 2 else -1 }
      [{ direction := fun i => if i = 1 ∨ i = 2 then 1 / 4 else -1 / 4, pivot := 1 }]).map
        (fun weight => (activeAtoms weight).card) = some 2 := by
  decide +kernel

#print axioms checkAffineCompression_sound
#print axioms checkAffineCompression_preserves_affine_family
#print axioms affine_reconstruction_replay_example

end D5.S0.Certificates.RationalAffineMomentCompression
