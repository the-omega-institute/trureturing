/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity
   mirror-E: none(waiver:exact-open-problem-sector)
   anchors: []
   utility: none
   digest: The maximum purity of a literal 4-by-6 APPT density matrix is 8/169. -/

/-
proof_shape: result: bind-only
escape_witness: none. This final composition is retained as the exact external
  open-problem sector resolution. The generic finite Bell-corner reduction
  and the unchanged dimension-24 certificate supply the upper bound;
  the existing low-rank separable ray supplies attainment.
admission_basis: open-problem-resolution
Preregistered target: https://github.com/the-omega-institute/trureturing/issues/17734
The claim is only the m=4, n=6 sector of Conjecture 6.7 in arXiv:2608.03390v2.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN8PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

open Matrix
open scoped ComplexOrder Kronecker
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSextitMaximumPurity

noncomputable section

def claim : Prop :=
    (∀ rho : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) → APPT rho →
        (rho * rho).trace.re ≤ (8 / 169 : ℝ)) ∧
    (sSup {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = p} = (8 / 169 : ℝ)) ∧
    ∃ rho : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ,
      rho = diagonal (fun ij : Fin 4 × Fin 6 =>
        if ij = (0, 0) then (3 / 26 : ℂ) else (1 / 26 : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (8 / 169 : ℝ)

private def basis : Fin 4 × Fin 6 → ℂ := Pi.single (0, 0) 1

private def attainingDensity : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ :=
  ((1 / 26 : ℝ) : ℂ) • (1 + (2 : ℂ) • vecMulVec basis (star basis))

private theorem basis_dot : star basis ⬝ᵥ basis = (1 : ℂ) := by
  classical
  simp [basis, dotProduct, Pi.single_apply]

private theorem attaining_pos : attainingDensity.PosSemidef := by
  apply Matrix.PosSemidef.smul _ (Complex.zero_le_real.mpr (by norm_num))
  exact Matrix.PosSemidef.one.add
    ((posSemidef_vecMulVec_self_star basis).smul (by norm_num))

private theorem attaining_trace : attainingDensity.trace = 1 := by
  have hI : (1 : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ).trace = (24 : ℂ) := by
    simp [Matrix.trace_one, Fintype.card_prod]
  have hv : (vecMulVec basis (star basis)).trace = (1 : ℂ) := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm]
    exact basis_dot
  simp only [attainingDensity, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, hI, hv]
  norm_num

private theorem attaining_purity :
    (attainingDensity * attainingDensity).trace.re = (8 / 169 : ℝ) := by
  have hsq := pure_outer_square basis basis_dot
  have hI : (1 : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ).trace = (24 : ℂ) := by
    simp [Matrix.trace_one, Fintype.card_prod]
  have hv : (vecMulVec basis (star basis)).trace = (1 : ℂ) := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm]
    exact basis_dot
  have hm : (1 + (2 : ℂ) • vecMulVec basis (star basis)) *
      (1 + (2 : ℂ) • vecMulVec basis (star basis)) =
      1 + (8 : ℂ) • vecMulVec basis (star basis) := by
    simp only [mul_add, add_mul, one_mul, mul_one, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, hsq]
    module
  simp only [attainingDensity, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm,
    Matrix.trace_smul, Matrix.trace_add, hI, hv, smul_eq_mul]
  norm_num

private theorem attaining_appt : APPT attainingDensity := by
  intro U
  have hnorm := QuadbitMaximumPurity.norm_of_dot_eq_one _ (unitary_vector_norm U basis basis_dot)
  have hsepU := separableCone_one_add_two_rankOne _ hnorm
  have hsepS := separableCone_smul (c := (1 / 26 : ℝ)) (by norm_num) hsepU
  have hconj : (U : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ) * attainingDensity *
      (U : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ)ᴴ =
      ((1 / 26 : ℝ) : ℂ) •
        (1 + (2 : ℂ) • vecMulVec
          ((U : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ) *ᵥ basis)
          (star ((U : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ) *ᵥ basis))) := by
    simp only [attainingDensity, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul,
      mul_assoc, ← conjugate_outer]
    congr 1
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.mul_assoc, one_mul]
    have hUr : (U : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ) *
        (U : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ)ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff.mp U.property
    rw [hUr]
  change (partialTranspose ((U : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ) *
    attainingDensity * (U : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ)ᴴ)).PosSemidef
  rw [hconj]
  exact QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef hsepS

private theorem attaining_diagonal :
    attainingDensity = diagonal (fun ij : Fin 4 × Fin 6 =>
      if ij = (0, 0) then (3 / 26 : ℂ) else (1 / 26 : ℂ)) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (0, 0)
    · subst i
      norm_num [attainingDensity, basis, Matrix.diagonal_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply]
    · simp [attainingDensity, basis, Matrix.diagonal_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply, hi]
  · by_cases hi : i = (0, 0)
    · have hj : j ≠ (0, 0) := by intro h; exact hij (hi.trans h.symm)
      simp [attainingDensity, basis, Matrix.diagonal_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
        Pi.single_apply, hij, hi, hj, eq_comm]
    · simp [attainingDensity, basis, Matrix.diagonal_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply, hij, hi]

private theorem density_bound (rho : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    (rho * rho).trace.re ≤ (8 / 169 : ℝ) := by
  obtain ⟨l, ho, hl, ht, h1, h2, hp⟩ :=
    FiniteBellCorner.spectral_reduction (by decide : 3 ≤ 4) (by decide : 3 ≤ 6)
      rho hrho htrace happt
  rw [hp]
  have hb : FiniteBellCorner.boundaryValues 24 (by decide) l =
      QutritSpectralReduction.boundaryValues 5 l := rfl
  rw [hb] at h1 h2
  have hbound := QutritN8PurityBound.certificate_bound l ho (hl 23) ht h1 h2
  norm_num at hbound ⊢
  exact hbound

theorem result : claim := by
  have hattain : ∃ rho : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (8 / 169 : ℝ) :=
    ⟨attainingDensity, ⟨attaining_pos, attaining_trace⟩, attaining_appt, attaining_purity⟩
  refine ⟨fun rho hd ha => density_bound rho hd.1 hd.2 ha, ?_,
    attainingDensity, attaining_diagonal, ⟨attaining_pos, attaining_trace⟩,
    attaining_appt, attaining_purity⟩
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_
  · exact ⟨_, hattain⟩
  · rintro p ⟨rho, hd, ha, hp⟩
    rw [← hp]
    exact density_bound rho hd.1 hd.2 ha
  · intro w hw
    exact ⟨_, hattain, hw⟩

#print axioms result

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSextitMaximumPurity
