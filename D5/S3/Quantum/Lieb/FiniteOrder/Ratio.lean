/- GID: D5/S3/Quantum/Lieb/FiniteOrder/Ratio
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/FiniteOrder/Ratio
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Finite doubled-order monotonicity reverses the normalized quotient and preserves its reciprocal on positive definite matrices. -/
module

public import D5.S3.Quantum.Lieb.FiniteOrderCompression
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Lieb.FiniteOrder
open Matrix
open D5.S3.Quantum.Lieb.PositiveMapJensen
open D5.S3.Quantum.Lieb.FiniteOrderCompression
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private theorem sqrt_cfc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    CFC.sqrt A = cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA.nonneg, cfcₙ_eq_cfc]

private theorem normalized_eq {n : ℕ} (f : ℝ → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    (CFC.sqrt A)⁻¹ * cfc f A * (CFC.sqrt A)⁻¹ = cfc (fun t => f t / t) A := by
  have hpos : ∀ t ∈ spectrum ℝ A, 0 < t := fun t ht => hA.isStrictlyPositive.spectrum_pos ht
  have hs : (CFC.sqrt A)⁻¹ = cfc (fun t : ℝ => (Real.sqrt t)⁻¹) A := by
    rw [sqrt_cfc A hA.posSemidef, Matrix.nonsing_inv_eq_ringInverse]
    exact (cfc_inv Real.sqrt A (fun t ht => (Real.sqrt_pos.2 (hpos t ht)).ne')
      (A.finite_real_spectrum.continuousOn _) hA.isHermitian).symm
  rw [hs, ← cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _),
    ← cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro t ht
  dsimp
  have ht0 := (hpos t ht).ne'
  have hs0 := (Real.sqrt_pos.2 (hpos t ht)).ne'
  field_simp
  rw [Real.sq_sqrt (hpos t ht).le]
  ring

private theorem normalized_antitone (n : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0)) (hf0 : 0 ≤ f 0)
    (hmono : ∀ (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) :
    cfc (fun t => f t / t) B ≤ cfc (fun t => f t / t) A := by
  let S := CFC.sqrt A
  let T := CFC.sqrt B
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hT : T.IsHermitian := (CFC.sqrt_nonneg B).posSemidef.isHermitian
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hTT : T * T = B := CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
  have hSi : IsUnit S.det := (isUnit_iff_isUnit_det S).mp (hA.isStrictlyPositive.isUnit_cfcSqrt A)
  have hTi : IsUnit T.det := (isUnit_iff_isUnit_det T).mp (hB.isStrictlyPositive.isUnit_cfcSqrt B)
  have hSiH : S⁻¹ᴴ = S⁻¹ := hS.inv.eq
  have hTiH : T⁻¹ᴴ = T⁻¹ := hT.inv.eq
  have hnormB : T⁻¹ * B * T⁻¹ = 1 := by
    rw [← hTT]
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTi, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hTi]
  let C := T⁻¹ * S
  have hCC : C * Cᴴ ≤ 1 := by
    have hc := congruence_mono hAB T⁻¹
    rw [hTiH, hnormB] at hc
    simpa only [C, Matrix.conjTranspose_mul, hS.eq, hTiH,
      Matrix.mul_assoc, ← hSS] using hc
  have hnorm : ‖C‖ * ‖C‖ ≤ 1 := by
    have hh := (CStarAlgebra.norm_le_one_iff_of_nonneg (C * Cᴴ)
      (Matrix.posSemidef_self_mul_conjTranspose C).nonneg).2 hCC
    simpa only [← Matrix.star_eq_conjTranspose, CStarRing.norm_self_mul_star] using hh
  have hC : Cᴴ * C ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg (Cᴴ * C)
      (Matrix.posSemidef_conjTranspose_mul_self C).nonneg).1
    simpa only [← Matrix.star_eq_conjTranspose, CStarRing.norm_star_mul_self] using hnorm
  have hCAC : Cᴴ * B * C = A := by
    simp only [C, Matrix.conjTranspose_mul, hS.eq, hTiH]
    calc
      _ = S * (T⁻¹ * B * T⁻¹) * S := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hnormB, Matrix.mul_one, hSS]
  have hj := matrix_monotone_contraction n f hf hf0 hmono B C hB.posSemidef hC
  rw [hCAC] at hj
  have h := congruence_mono hj S⁻¹
  rw [hSiH] at h
  have hleft : S⁻¹ * (Cᴴ * cfc f B * C) * S⁻¹ = T⁻¹ * cfc f B * T⁻¹ := by
    simp only [C, Matrix.conjTranspose_mul, hS.eq, hTiH,
      Matrix.mul_assoc, ← Matrix.mul_assoc S⁻¹ S, Matrix.nonsing_inv_mul _ hSi,
      Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hSi]
  rw [hleft, normalized_eq f A hA, normalized_eq f B hB] at h
  exact h

/-- Matrix monotonicity of order exactly `2n` makes `t / f(t)` matrix monotone
of order `n` on positive definite inputs. No value of the quotient at zero is
used in this assertion. -/
theorem ratio_monotone_posDef (n : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0))
    (hfpos : ∀ t : ℝ, 0 < t → 0 < f t)
    (hmono : ∀ (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) :
    cfc (fun t => t / f t) A ≤ cfc (fun t => t / f t) B := by
  have hf0 : 0 ≤ f 0 := by
    have ht := ((hf.continuousWithinAt (show (0 : ℝ) ∈ Set.Ici 0 by simp)).mono
      Set.Ioi_subset_Ici_self).tendsto
    exact ge_of_tendsto ht (Filter.mem_of_superset self_mem_nhdsWithin
      (fun t ht => (hfpos t ht).le))
  have hN := normalized_antitone n f hf hf0 hmono A B hA hB hAB
  have hp (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosDef) :
      IsStrictlyPositive (cfc (fun t => f t / t) X) := by
    apply (cfc_isStrictlyPositive_iff _ X (X.finite_real_spectrum.continuousOn _)
      hX.isHermitian).2
    intro t ht
    exact div_pos (hfpos t (hX.isStrictlyPositive.spectrum_pos ht))
      (hX.isStrictlyPositive.spectrum_pos ht)
  have hi := CStarAlgebra.antitoneOn_ringInverse (hp B hB) (hp A hA) hN
  have he (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosDef) :
      Ring.inverse (cfc (fun t => f t / t) X) = cfc (fun t => t / f t) X := by
    have heq := cfc_inv (fun t => f t / t) X (by
      intro t ht
      exact (div_pos (hfpos t (hX.isStrictlyPositive.spectrum_pos ht))
        (hX.isStrictlyPositive.spectrum_pos ht)).ne')
      (X.finite_real_spectrum.continuousOn _) hX.isHermitian
    refine heq.symm.trans ?_
    apply cfc_congr
    intro t ht
    simp [div_eq_mul_inv, mul_comm]
  simpa only [he A hA, he B hB] using hi

#print axioms ratio_monotone_posDef
end D5.S3.Quantum.Lieb.FiniteOrder
