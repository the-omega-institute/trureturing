/- GID: D5/S3/Quantum/Recovery/BurriReversePetz
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/BurriReversePetz
   mirror-E: none(waiver:unfinished-source-identification)
   anchors: []
   utility: none
   digest: Ordinary reference-completed Petz action for the explicit reverse instance. -/

import D5.S3.Quantum.Recovery.BurriReverseOverlap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Recovery.BurriReverseDecoder
open D5.S3.Quantum.Recovery.BurriReverseOverlap
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Recovery.ReferencePetzChannel

namespace D5.S3.Quantum.Recovery.BurriReversePetz

private def v03 : B → ℂ := fun p => if p = (0, 0) ∨ p = (1, 0) then 1 else 0
private def v14 : B → ℂ := fun p => if p = (0, 1) then 1 else if p = (1, 1) then -1 else 0
private def v02 : B → ℂ := fun p => if p = (0, 0) ∨ p = (0, 2) then 1 else 0
private def v35 : B → ℂ := fun p => if p = (1, 0) then 1 else if p = (1, 2) then -1 else 0

/-- A strictly positive diagonal plus four positive rank-one squares. -/
theorem amplitude_positive : Y.PosDef := by
  have hY : Y = Matrix.diagonal (fun p : B => if p.2 = 0 then (1 : ℂ) else 2) +
      Matrix.vecMulVec v03 (star v03) + Matrix.vecMulVec v14 (star v14) +
      Matrix.vecMulVec v02 (star v02) + Matrix.vecMulVec v35 (star v35) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
      norm_num [Y, amplitude, sign, Matrix.diagonal_apply, Matrix.vecMulVec_apply,
        v03, v14, v02, v35]
  rw [hY]
  have hd : (Matrix.diagonal (fun p : B => if p.2 = 0 then (1 : ℂ) else 2)).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro p
    split_ifs <;> norm_num [Complex.pos_iff]
  exact ((((hd.add_posSemidef (Matrix.posSemidef_vecMulVec_self_star v03)).add_posSemidef
    (Matrix.posSemidef_vecMulVec_self_star v14)).add_posSemidef
    (Matrix.posSemidef_vecMulVec_self_star v02)).add_posSemidef
    (Matrix.posSemidef_vecMulVec_self_star v35)

theorem output_positive : output.PosDef := by
  have h : (Y * Y).PosDef := by
    simpa only [amplitude_adjoint] using
      Matrix.posDef_conjTranspose_mul_self.mpr amplitude_positive.mulVec_injective
  exact h.smul (by norm_num [Complex.pos_iff])

theorem reference_positive : rho.PosSemidef :=
  (Matrix.PosSemidef.one : (1 : Matrix A A ℂ).PosSemidef).smul
    (by norm_num [Complex.nonneg_iff])

theorem reference_trace : Matrix.trace rho = 1 := by
  norm_num [rho, Matrix.trace, Fin.sum_univ_two]

def referenceState : DensityState A :=
  ⟨CStarMatrix.ofMatrix rho,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv reference_positive.nonneg, reference_trace⟩

theorem reference_root : cfc Real.sqrt rho =
    (1 / (Real.sqrt 2 : ℂ)) • (1 : Matrix A A ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : ((1 / (Real.sqrt 2 : ℂ)) • (1 : Matrix A A ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by
      norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]
      positivity)
  have hh : CFC.sqrt rho = (1 / (Real.sqrt 2 : ℂ)) • (1 : Matrix A A ℂ) := by
    apply CFC.sqrt_unique _ hp.nonneg
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, rho,
      one_div_mul_one_div, hs]
  rwa [CFC.sqrt_eq_real_sqrt _ reference_positive.nonneg, cfcₙ_eq_cfc] at hh

theorem output_root : cfc Real.sqrt output = (1 / (Real.sqrt 62 : ℂ)) • Y := by
  have hs : (Real.sqrt 62 : ℂ) * (Real.sqrt 62 : ℂ) = 62 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 62)
  have hp : ((1 / (Real.sqrt 62 : ℂ)) • Y).PosSemidef :=
    amplitude_positive.posSemidef.smul (by
      norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]
      positivity)
  have hh : CFC.sqrt output = (1 / (Real.sqrt 62 : ℂ)) • Y := by
    apply CFC.sqrt_unique _ hp.nonneg
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_div_mul_one_div, hs]
    rfl
  rwa [CFC.sqrt_eq_real_sqrt _ output_positive.posSemidef.nonneg, cfcₙ_eq_cfc] at hh

theorem output_support : spectralSupport output = 1 := by
  unfold spectralSupport
  calc
    _ = cfc (fun _ : ℝ => (1 : ℝ)) output := by
      apply cfc_congr
      intro x hx
      rw [output_positive.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      simp [ne_of_gt (output_positive.eigenvalues_pos i)]
    _ = 1 := cfc_const_one ℝ output

theorem output_inverse_root_cancel : Y * spectralInverseSqrt output =
    (Real.sqrt 62 : ℂ) • (1 : Matrix B B ℂ) := by
  have hh : cfc Real.sqrt output * spectralInverseSqrt output = 1 := by
    unfold spectralInverseSqrt
    rw [← cfc_mul]
    calc
      _ = cfc (fun _ : ℝ => (1 : ℝ)) output := by
        apply cfc_congr
        intro x hx
        rw [output_positive.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        exact mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (output_positive.eigenvalues_pos i)))
      _ = 1 := cfc_const_one ℝ output
  rw [output_root, Matrix.smul_mul] at hh
  have hn : (Real.sqrt 62 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 62))
  have h := congrArg (fun Z : Matrix B B ℂ => (Real.sqrt 62 : ℂ) • Z) hh
  simpa [smul_smul, hn] using h

theorem output_inverse_root : spectralInverseSqrt output = (Real.sqrt 62 : ℂ) • Y⁻¹ := by
  have h := congrArg (fun Z : Matrix B B ℂ => Y⁻¹ * Z) output_inverse_root_cancel
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp amplitude_positive.isUnit),
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] using h

theorem noise_adjoint_slice (e : E) : (noiseKraus e)ᴴ =
    (1 / (Real.sqrt 31 : ℂ)) • (slice e * Y) := by
  ext i ⟨j, a⟩
  rcases e with ⟨k, l, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;>
    fin_cases k <;> fin_cases l <;> fin_cases b <;>
    norm_num [noiseKraus, V, slice, active, Y, amplitude, sign,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, div_eq_mul_inv]

#print axioms amplitude_positive
#print axioms output_root
#print axioms output_support
#print axioms output_inverse_root

end D5.S3.Quantum.Recovery.BurriReversePetz
