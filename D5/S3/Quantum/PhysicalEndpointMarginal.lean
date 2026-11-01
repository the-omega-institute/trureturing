/- GID: D5/S3/Quantum/PhysicalEndpointMarginal
   generality: G
   mirror-B: D5/B/S3/Quantum/PhysicalEndpointMarginal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both physical partial traces of an actual compact target encoding on every logical matrix. -/

import D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.PhysicalEndpointMarginal

open D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open Matrix
open scoped BigOperators Matrix

variable {Sector : Type*} [Fintype Sector] [DecidableEq Sector]

def encodedTarget (d : Sector → ℕ) (Y : Matrix Sector Sector ℂ) :
    Matrix (TargetLocal d × TargetLocal d) (TargetLocal d × TargetLocal d) ℂ :=
  targetEncoding d * Y * (targetEncoding d)ᴴ

def targetMarginal (d : Sector → ℕ) (Y : Matrix Sector Sector ℂ) :
    Matrix (TargetLocal d) (TargetLocal d) ℂ :=
  fun x y => if x = y then
    (Y x.1 x.1 : ℂ) * (d x.1 : ℂ)⁻¹ else 0

private lemma inv_sqrt_mul_inv_sqrt (r : ℕ) (_hr : 0 < r) :
    ((Real.sqrt (r : ℝ) : ℂ)⁻¹) * ((Real.sqrt (r : ℝ) : ℂ)⁻¹) =
      (r : ℂ)⁻¹ := by
  have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast (Nat.zero_le r)
  calc
    ((Real.sqrt (r : ℝ) : ℂ)⁻¹) * ((Real.sqrt (r : ℝ) : ℂ)⁻¹) =
        (((Real.sqrt (r : ℝ) : ℂ) * (Real.sqrt (r : ℝ) : ℂ))⁻¹) := by
          exact (_root_.mul_inv_rev _ _).symm
    _ = (r : ℂ)⁻¹ := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr0]
      rfl

theorem right_target_marginal (d : Sector → ℕ) (hd : ∀ s, 0 < d s)
    (Y : Matrix Sector Sector ℂ) :
    partialTraceRight (encodedTarget d Y) = targetMarginal d Y := by
  ext x y
  classical
  simp [encodedTarget, targetMarginal, partialTraceRight, Matrix.mul_apply,
    Matrix.conjTranspose_apply, targetEncoding, Finset.sum_ite_eq',
    Finset.sum_ite_irrel, ite_and, hd]
  by_cases hxy : x = y
  · subst y
    rw [Finset.sum_eq_single x.fst]
    · simp only [if_pos trivial]
      have hstar :
          (starRingEnd ℂ) ((Real.sqrt (d x.fst : ℝ) : ℂ)⁻¹) =
            (Real.sqrt (d x.fst : ℝ) : ℂ)⁻¹ := by
        simp [Complex.star_def]
      rw [hstar]
      rw [show ((↑√↑(d x.fst))⁻¹ * Y x.fst x.fst *
            (↑√↑(d x.fst))⁻¹) =
            Y x.fst x.fst * ((↑√↑(d x.fst))⁻¹ * (↑√↑(d x.fst))⁻¹) by ring]
      rw [inv_sqrt_mul_inv_sqrt (d x.fst) (hd x.fst)]
    · intro b hb hbx
      have hne : x.fst ≠ b := by
        intro h
        exact hbx h.symm
      simp [hne, Nat.ne_of_gt (hd x.fst)]
    · simp
  · have hyx : ¬ y = x := Ne.symm hxy
    simp only [if_neg hyx, if_neg hxy]
    simp

theorem left_target_marginal (d : Sector → ℕ) (hd : ∀ s, 0 < d s)
    (Y : Matrix Sector Sector ℂ) :
    partialTraceLeft (encodedTarget d Y) = targetMarginal d Y := by
  ext x y
  classical
  simp [encodedTarget, targetMarginal, partialTraceLeft, Matrix.mul_apply,
    Matrix.conjTranspose_apply, targetEncoding, Finset.sum_ite_eq',
    Finset.sum_ite_irrel, ite_and, hd]
  by_cases hxy : x = y
  · subst y
    rw [Finset.sum_eq_single x.fst]
    · simp only [if_pos trivial]
      have hstar :
          (starRingEnd ℂ) ((Real.sqrt (d x.fst : ℝ) : ℂ)⁻¹) =
            (Real.sqrt (d x.fst : ℝ) : ℂ)⁻¹ := by
        simp [Complex.star_def]
      rw [hstar]
      rw [show ((↑√↑(d x.fst))⁻¹ * Y x.fst x.fst *
            (↑√↑(d x.fst))⁻¹) =
            Y x.fst x.fst * ((↑√↑(d x.fst))⁻¹ * (↑√↑(d x.fst))⁻¹) by ring]
      rw [inv_sqrt_mul_inv_sqrt (d x.fst) (hd x.fst)]
    · intro b hb hbx
      have hne : x.fst ≠ b := by
        intro h
        exact hbx h.symm
      simp [hne, Nat.ne_of_gt (hd x.fst)]
    · simp
  · have hyx : ¬ y = x := Ne.symm hxy
    simp only [if_neg hyx, if_neg hxy]
    simp

theorem result (d : Sector → ℕ) (hd : ∀ s, 0 < d s)
    (Y : Matrix Sector Sector ℂ) :
    partialTraceRight (encodedTarget d Y) = targetMarginal d Y ∧
      partialTraceLeft (encodedTarget d Y) = targetMarginal d Y :=
  ⟨right_target_marginal d hd Y, left_target_marginal d hd Y⟩

#print axioms result

end D5.S3.Quantum.PhysicalEndpointMarginal
