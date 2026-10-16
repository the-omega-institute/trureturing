/- Research-only checkpoint; no mathematical admission or frozen delivery is claimed.
   This is an explicit APPT lower-bound instance, with no maximum-purity upper bound.
   Header-only correction after successful kernel/scoped report verification; not re-reported. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

open Matrix
open scoped ComplexOrder Kronecker
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment (APPT)
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitAttainment

noncomputable section

private def basis : Fin 4 × Fin 4 → ℂ := Pi.single (0, 0) 1

private def rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ((1 / 18 : ℝ) : ℂ) •
    (1 + (2 : ℂ) • vecMulVec basis (star basis))

private theorem basis_norm : ∑ ij, ‖basis ij‖ ^ 2 = (1 : ℝ) := by
  classical
  rw [Finset.sum_eq_single (0, 0)]
  · simp [basis]
  · intro b hb
    intro hne
    simp [basis, hne]
  · simp

private theorem norm_to_complex {I : Type} [Fintype I] (v : I → ℂ)
    (hv : ∑ i, ‖v i‖ ^ 2 = (1 : ℝ)) : ∑ i, star (v i) * v i = (1 : ℂ) := by
  calc
    ∑ i, star (v i) * v i = ∑ i, (‖v i‖ ^ 2 : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Complex.star_def]
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      exact Complex.ofReal_pow _ 2
    _ = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (Complex.ofReal_pow _ 2).symm
    _ = 1 := by rw [hv]; norm_num

private theorem separableCone_partialTranspose_posSemidef {m n : ℕ}
    {W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hW : separableCone W) : (partialTranspose W).PosSemidef := by
  rcases hW with ⟨k, A, B, hAB, rfl⟩
  have hterm : ∀ i : Fin k,
      (partialTranspose (A i ⊗ₖ B i)).PosSemidef := by
    intro i
    have heq : partialTranspose (A i ⊗ₖ B i) = A i ⊗ₖ (B i).transpose := by
      ext ⟨a,b⟩ ⟨c,d⟩
      simp [partialTranspose, Matrix.kronecker_apply]
    rw [heq]
    exact (hAB i).1.kronecker (hAB i).2.transpose
  have hs := Matrix.posSemidef_sum (s := (Finset.univ : Finset (Fin k)))
    (x := fun i : Fin k => partialTranspose (A i ⊗ₖ B i)) (by
      intro i hi
      exact hterm i)
  have hlin : partialTranspose (∑ i, A i ⊗ₖ B i) =
      ∑ i, partialTranspose (A i ⊗ₖ B i) := by
    ext ⟨a,b⟩ ⟨c,d⟩
    simp [partialTranspose, Matrix.sum_apply]
  rw [hlin]
  exact hs

private theorem conjugate_outer {I : Type} [Fintype I]
    (A : Matrix I I ℂ) (v : I → ℂ) :
    A * vecMulVec v (star v) * Aᴴ =
      vecMulVec (A *ᵥ v) (star (A *ᵥ v)) := by
  rw [mul_vecMulVec, vecMulVec_mul]
  simp [Matrix.vecMul_conjTranspose]

private theorem unitary_vector_norm {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (v : I → ℂ)
    (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    ∑ i, ‖(U *ᵥ v) i‖ ^ 2 = 1 := by
  have hu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hdot : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hu,
      Matrix.vecMul_one]
  have hv' : star v ⬝ᵥ v = (1 : ℂ) := by
    exact norm_to_complex v hv
  have h := congrArg Complex.re hdot
  have hnorm : ∀ w : I → ℂ, (star w ⬝ᵥ w).re = ∑ i, ‖w i‖ ^ 2 := by
    intro w
    rw [dotProduct, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (((starRingEnd ℂ) (w i)) * w i).re = _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      Complex.ofReal_re]
  calc
    ∑ i, ‖(U *ᵥ v) i‖ ^ 2 = (star (U *ᵥ v) ⬝ᵥ (U *ᵥ v)).re :=
      (hnorm (U *ᵥ v)).symm
    _ = (star v ⬝ᵥ v).re := h
    _ = 1 := by rw [hv']; norm_num

private theorem rho_pos : rho.PosSemidef := by
  apply Matrix.PosSemidef.smul _ (Complex.zero_le_real.mpr (by norm_num))
  exact Matrix.PosSemidef.one.add
    ((posSemidef_vecMulVec_self_star basis).smul (by norm_num))

private theorem rho_trace : rho.trace = 1 := by
  have hI : (1 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ).trace = (16 : ℂ) := by
    simp [Matrix.trace_one, Fintype.card_prod]
  have hv : (vecMulVec basis (star basis)).trace = (1 : ℂ) := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm]
    exact norm_to_complex basis basis_norm
  simp only [rho, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, hI, hv]
  norm_num

private theorem rho_purity : (rho * rho).trace.re = (2 / 27 : ℝ) := by
  have hsq : vecMulVec basis (star basis) * vecMulVec basis (star basis) =
      vecMulVec basis (star basis) := by
    rw [vecMulVec_mul_vecMulVec]
    have hv : star basis ⬝ᵥ basis = (1 : ℂ) := norm_to_complex basis basis_norm
    simp [hv]
  have hI : (1 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ).trace = (16 : ℂ) := by
    simp [Matrix.trace_one, Fintype.card_prod]
  have hv : (vecMulVec basis (star basis)).trace = (1 : ℂ) := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm]
    exact norm_to_complex basis basis_norm
  have hm : (1 + (2 : ℂ) • vecMulVec basis (star basis)) *
      (1 + (2 : ℂ) • vecMulVec basis (star basis)) =
      1 + (8 : ℂ) • vecMulVec basis (star basis) := by
    simp only [mul_add, add_mul, one_mul, mul_one, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, hsq]
    module
  simp only [rho, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm,
    Matrix.trace_smul, Matrix.trace_add, hI, hv, smul_eq_mul]
  norm_num

theorem attainment :
    APPT rho ∧ rho.PosSemidef ∧ rho.trace = 1 ∧
      (rho * rho).trace.re = (2 / 27 : ℝ) := by
  have hsep := separableCone_one_add_two_rankOne basis basis_norm
  have hAPPT : APPT rho := by
    intro U
    have hU : (U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) ∈
        Matrix.unitaryGroup (Fin 4 × Fin 4) ℂ := U.property
    have hnorm := unitary_vector_norm (U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
      hU basis basis_norm
    have hsepU : separableCone
        (1 + (2 : ℂ) • vecMulVec
          ((U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) *ᵥ basis)
          (star ((U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) *ᵥ basis))) := by
      exact separableCone_one_add_two_rankOne _ hnorm
    have hsepS := separableCone_smul (c := (1 / 18 : ℝ)) (by norm_num) hsepU
    have hconj : (U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) * rho *
        (U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)ᴴ =
        ((1 / 18 : ℝ) : ℂ) •
          (1 + (2 : ℂ) • vecMulVec
            ((U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) *ᵥ basis)
            (star ((U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) *ᵥ basis))) := by
      simp only [rho, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul,
        mul_assoc, ← conjugate_outer]
      congr 1
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_one, Matrix.mul_assoc, one_mul]
      have hUr : (U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) *
          (U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)ᴴ = 1 := by
        simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
      rw [hUr]
    change (partialTranspose ((U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) * rho *
      (U : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)ᴴ)).PosSemidef
    rw [hconj]
    convert separableCone_partialTranspose_posSemidef hsepS using 1
    ext i j
    norm_num [partialTranspose, smul_eq_mul] <;> ring
  exact ⟨hAPPT, rho_pos, rho_trace, rho_purity⟩

#print axioms attainment

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitAttainment
