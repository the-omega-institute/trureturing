/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity
   mirror-E: none(waiver:structural-density-transfer)
   anchors: []
   utility: none
   digest: The literal four-by-five APPT purity maximum is 7/121, attained by the diagonal density (3,1^19)/22. -/

/-
proof_shape: normalized_ray and normalized_basis_diagonal are bind-only
  helpers, both consumed by result. Their normalization uses the generic
  separable-ray theorem, the exported normalization/PT helpers, and
  rank-one and trace identities.
proof_shape: density_bound and result are content after unfolding the
  same-delivery spectral transfer. The actual finite Bell corner supplies
  the necessary K1/K2 constraints for this physical matrix; the full
  length-twenty upper bound uses the new insertion/deletion inference
  from lengths eighteen and twenty-one through nineteen. The live
  intermediate is SpectralBoundaryTransfer.spectral_bound_transfer,
  not the Bell-corner packaging or the rational attainer arithmetic.
admission_basis: escape-witness, subject to independent combined review.
utility:none rationale: The new inference is a symbolic structural
  transfer over arbitrary ordered spectra and arbitrary complex densities.
  The generic ray formulas are consumed algebraic normalization of an
  existing separable-ray theorem. This does not settle the separate
  certified-instance eligibility of the retained Fin20 sharpness theorem.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner
import D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

set_option autoImplicit false
set_option Elab.async false

open Matrix
open scoped ComplexOrder
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
open QutritPerturbationAttainment
open AbsoluteSeparability.LowRankRays

noncomputable section

/-- The normalized separable ray, for arbitrary local dimensions. -/
def normalizedRay {m n : ℕ} (v : Fin m × Fin n → ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ((1 / (((m*n : ℕ) : ℝ) + 2) : ℝ) : ℂ) •
    (1 + (2 : ℂ) • vecMulVec v (star v))

/-- Normalization preserves the separable ray after every global unitary. -/
theorem normalized_ray {m n : ℕ} (v : Fin m × Fin n → ℂ)
    (hv : star v ⬝ᵥ v = (1 : ℂ)) :
    (normalizedRay v).PosSemidef ∧ (normalizedRay v).trace = 1 ∧
      APPT (normalizedRay v) ∧
      (normalizedRay v * normalizedRay v).trace.re =
        (((m*n : ℕ) : ℝ) + 8) / (((m*n : ℕ) : ℝ) + 2)^2 := by
  let d : ℝ := (m*n : ℕ)
  have hd : 0 < d + 2 := by dsimp [d]; positivity
  have hs : 0 ≤ (1 / (d + 2) : ℝ) := by positivity
  have htr : (vecMulVec v (star v)).trace = (1 : ℂ) := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm, hv]
  have hi : (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ).trace = (d : ℂ) := by
    simp [d, Matrix.trace_one, Fintype.card_prod]
  have hm : (1 + (2 : ℂ) • vecMulVec v (star v)) *
      (1 + (2 : ℂ) • vecMulVec v (star v)) =
      1 + (8 : ℂ) • vecMulVec v (star v) := by
    simp only [mul_add, add_mul, one_mul, mul_one, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, pure_outer_square v hv]
    module
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Matrix.PosSemidef.one.add
      ((posSemidef_vecMulVec_self_star v).smul (by norm_num))).smul
        (Complex.zero_le_real.mpr hs)
  · simp only [normalizedRay, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_smul, hi, htr, smul_eq_mul]
    change ((1 / (d + 2) : ℝ) : ℂ) * ((d : ℂ) + 2 * 1) = 1
    norm_cast
    exact div_mul_cancel₀ 1 hd.ne'
  · intro U
    have hnorm := QuadbitMaximumPurity.norm_of_dot_eq_one _ (unitary_vector_norm U v hv)
    have hsep := separableCone_smul (c := (1 / (d + 2) : ℝ)) hs
      (separableCone_one_add_two_rankOne _ hnorm)
    have hconj : (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) * normalizedRay v *
        (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ =
        ((1 / (d + 2) : ℝ) : ℂ) •
          (1 + (2 : ℂ) • vecMulVec ((U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) *ᵥ v)
            (star ((U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) *ᵥ v))) := by
      have hu : (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) *
          (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ = 1 := by
        simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
      simp only [normalizedRay, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_one, hu, conjugate_outer]
      rfl
    change (partialTranspose ((U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) *
      normalizedRay v * (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ)).PosSemidef
    rw [hconj]
    exact QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef hsep
  · simp only [normalizedRay, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm,
      Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, hi, htr, smul_eq_mul]
    have hc : (↑(1 / (d + 2) : ℝ) * ↑(1 / (d + 2) : ℝ) *
        ((d : ℂ) + 8 * 1)) =
        ((((d + 8) / (d + 2)^2 : ℝ)) : ℂ) := by
      have hdc : (d : ℂ) + 2 ≠ 0 := by exact_mod_cast hd.ne'
      push_cast
      field_simp [hdc]
      <;> ring
    change (↑(1 / (d + 2) : ℝ) * ↑(1 / (d + 2) : ℝ) *
      ((d : ℂ) + 8 * 1)).re = (d + 8) / (d + 2)^2
    rw [hc, Complex.ofReal_re]

/-- A coordinate vector gives the diagonal representative of the normalized ray. -/
theorem normalized_basis_diagonal {m n : ℕ} (a : Fin m × Fin n) :
    normalizedRay (Pi.single a 1) = diagonal (fun i =>
      if i = a then (3 / (((m*n : ℕ) : ℂ) + 2) : ℂ)
      else (1 / (((m*n : ℕ) : ℂ) + 2) : ℂ)) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = a <;>
      simp [normalizedRay, Matrix.diagonal_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply, hi]
    <;> push_cast <;> ring
  · by_cases hi : i = a
    · have hj : j ≠ a := by intro h; exact hij (hi.trans h.symm)
      simp [normalizedRay, Matrix.diagonal_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
        Pi.single_apply, hij, hi, hj, eq_comm]
      all_goals simp_all
    · simp [normalizedRay, Matrix.diagonal_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply, hij, hi]

def claim : Prop :=
    (∀ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) → APPT rho →
        (rho * rho).trace.re ≤ (7 / 121 : ℝ)) ∧
    (sSup {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = p} = (7 / 121 : ℝ)) ∧
    ∃ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      rho = diagonal (fun ij : Fin 4 × Fin 5 =>
        if ij = (0, 0) then (3 / 22 : ℂ) else (1 / 22 : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (7 / 121 : ℝ)

private theorem density_bound (rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    (rho * rho).trace.re ≤ (7 / 121 : ℝ) := by
  obtain ⟨l, ho, hn, ht, h1, h2, hp⟩ :=
    FiniteBellCorner.spectral_reduction (by decide : 3 ≤ 4) (by decide : 3 ≤ 5)
      rho hrho htrace happt
  have hb : FiniteBellCorner.boundaryValues 20 (by decide) l =
      SpectralBoundaryTransfer.boundaryValues 11 l := by
    funext q
    apply congrArg l
    apply Fin.ext
    simp only [FiniteBellCorner.boundaryValues, SpectralBoundaryTransfer.boundaryValues,
      SpectralBoundaryTransfer.boundaryIndex]
  rw [hb] at h1 h2
  rw [hp]
  exact DimensionTwentySpectralPurityBound.spectral_purity_bound l ho hn ht h1 h2

theorem result : claim := by
  let v : Fin 4 × Fin 5 → ℂ := Pi.single (0, 0) 1
  have hv : star v ⬝ᵥ v = (1 : ℂ) := by
    classical
    simp [v, dotProduct, Pi.single_apply]
  obtain ⟨hd, ht, ha, hp⟩ := normalized_ray v hv
  have heq : normalizedRay v = diagonal (fun ij : Fin 4 × Fin 5 =>
      if ij = (0, 0) then (3 / 22 : ℂ) else (1 / 22 : ℂ)) := by
    convert normalized_basis_diagonal ((0, 0) : Fin 4 × Fin 5) using 1 <;> norm_num [v]
  norm_num at hp
  have hattain : ∃ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (7 / 121 : ℝ) :=
    ⟨normalizedRay v, ⟨hd, ht⟩, ha, hp⟩
  refine ⟨fun rho hd ha => density_bound rho hd.1 hd.2 ha, ?_,
    normalizedRay v, heq, ⟨hd, ht⟩, ha, hp⟩
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_
  · exact ⟨_, hattain⟩
  · rintro p ⟨rho, hd, ha, hp⟩
    rw [← hp]
    exact density_bound rho hd.1 hd.2 ha
  · intro w hw
    exact ⟨_, hattain, hw⟩

#print axioms normalized_ray
#print axioms normalized_basis_diagonal
#print axioms result

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
