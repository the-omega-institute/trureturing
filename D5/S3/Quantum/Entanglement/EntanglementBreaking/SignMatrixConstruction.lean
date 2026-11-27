/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous sign matrix bounds give indecomposable k-entanglement-breaking maps. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.SignMatrixPartialTranspose
import D5.S3.Quantum.Entanglement.EntanglementBreaking.SignMatrixFailureBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open _root_.Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder _root_.Matrix.Norms.L2Operator
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)

private theorem pptTest_psd_of_opNorm {d : ℕ} (hd : 0 < d)
    {H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hH : H.IsHermitian) (hbound : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) H‖ ≤ 4 * (d : ℝ)) :
    (pptTest H).PosSemidef := by
  let C := (1 / (4 * (d : ℝ))) • H
  have hd' : 0 < 4 * (d : ℝ) := mul_pos (by norm_num) (by exact_mod_cast hd)
  have hC : C.IsHermitian := hH.smul (by simp [IsSelfAdjoint])
  have hnorm : ‖C‖ ≤ 1 := by
    rw [show C = (1 / (4 * (d : ℝ))) • H from rfl, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one hd'.le)]
    exact (mul_le_mul_of_nonneg_left hbound (div_nonneg zero_le_one hd'.le)).trans_eq
      (div_mul_cancel₀ 1 hd'.ne')
  have hlow : -(1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ≤ C := by
    have h := IsSelfAdjoint.neg_algebraMap_norm_le_self C hC.isSelfAdjoint
    have hmap : algebraMap ℝ (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ‖C‖ ≤ 1 := by
      simpa only [map_one] using
        (algebraMap_mono (α := ℝ) (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) hnorm)
    exact (neg_le_neg hmap).trans h
  simpa only [pptTest, sub_neg_eq_add, add_comm] using (Matrix.le_iff.mp hlow)

private theorem pptTest_partialTranspose {d : ℕ}
    (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    partialTranspose (pptTest H) = pptTest (partialTranspose H) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  change (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (i, v) (j, u) +
      (1 / (4 * (d : ℝ))) • H (i, v) (j, u) =
    (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (i, u) (j, v) +
      (1 / (4 * (d : ℝ))) • H (i, v) (j, u)
  simp only [Matrix.one_apply, Prod.mk.injEq, eq_comm (a := v) (b := u)]

/-- One sign assignment satisfies the Schmidt bound and both operator norm bounds. -/
theorem exists_signCubeSample_good {k d : ℕ} (hk : 2 ≤ k) (hdim : 524288 * k ^ 3 ≤ d) :
    ∃ ω : HermitianSignIndex (Fin d × Fin d) → Bool,
      SchmidtQuadraticBound k (signCubeSample ω) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (signCubeSample ω)‖ ≤ 4 * (d : ℝ) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (partialTranspose (signCubeSample ω))‖ ≤ 4 * (d : ℝ) := by
  classical
  have hkd : k ≤ d := by
    have hkpow : k ≤ k ^ 3 := Nat.le_pow (by decide)
    omega
  have hd4 : 4 ≤ d := by
    have hkpow : 0 < k ^ 3 := pow_pos (by omega) _
    omega
  let μ := signCubeMeasure (HermitianSignIndex (Fin d × Fin d))
  let S : Set (HermitianSignIndex (Fin d × Fin d) → Bool) :=
    {ω | ¬ SchmidtQuadraticBound k (signCubeSample ω)}
  let O : Set (HermitianSignIndex (Fin d × Fin d) → Bool) :=
    {ω | 4 * (d : ℝ) < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (signCubeSample ω)‖}
  let T : Set (HermitianSignIndex (Fin d × Fin d) → Bool) :=
    {ω | 4 * (d : ℝ) < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (partialTranspose (signCubeSample ω))‖}
  have hS : μ.real S < 1 / 4 :=
    (signCubeSample_schmidt_failure_le hkd).trans_lt (schmidt_failure_bound_lt_quarter hk hdim)
  have ht : 0 ≤ 3 * (d : ℝ) := by positivity
  have hcut : (4 / 3 : ℝ) * (3 * (d : ℝ)) = 4 * (d : ℝ) := by ring
  have hO : μ.real O < 1 / 4 := by
    have h := (signCubeSample_operator_tail (d := d) ht).trans_lt (operator_failure_bound_lt_quarter hd4)
    simpa only [hcut] using h
  have hT : μ.real T < 1 / 4 := by
    have h := (signCubeSample_partialTranspose_operator_tail_of_quadratic (d := d) ht
      (fun x hx => signCubeSample_partialTranspose_quadratic_tail x hx.le ht)).trans_lt
        (operator_failure_bound_lt_quarter hd4)
    simpa only [hcut] using h
  have hUnion : μ.real (S ∪ O ∪ T) < 1 := by
    calc
      _ ≤ μ.real (S ∪ O) + μ.real T := measureReal_union_le _ _
      _ ≤ (μ.real S + μ.real O) + μ.real T :=
        add_le_add (measureReal_union_le _ _) le_rfl
      _ < 1 := by linarith
  have hproper : S ∪ O ∪ T ≠ Set.univ := by
    intro h
    rw [h, measureReal_def, measure_univ, ENNReal.toReal_one] at hUnion
    exact (lt_irrefl 1) hUnion
  obtain ⟨ω, hω⟩ := Set.nonempty_compl.mpr hproper
  rw [Set.mem_compl_iff, Set.mem_union, Set.mem_union, not_or, not_or] at hω
  exact ⟨ω, not_not.mp hω.1.1, le_of_not_gt hω.1.2, le_of_not_gt hω.2⟩

/-- The selected assignment produces a k-entanglement-breaking indecomposable map. -/
theorem finiteSignSample_unconditional {k d : ℕ} (hk : 2 ≤ k) (hdim : 524288 * k ^ 3 ≤ d) :
    ∃ (ω : HermitianSignIndex (Fin d × Fin d) → Bool) (Φ : MatrixMap (Fin d) (Fin d) ℂ),
      inputChoi Φ = choiCandidate (signCubeSample ω) ∧ IsKEB k Φ ∧ ¬ IsDecomposable Φ := by
  obtain ⟨ω, hQ, hO, hT⟩ := exists_signCubeSample_good hk hdim
  have hd : 0 < d := lt_of_lt_of_le (by positivity) hdim
  have hH : (signCubeSample ω).IsHermitian := finiteSignSample_isHermitian _ _
  have hPT : (partialTranspose (signCubeSample ω)).IsHermitian := by
    rw [partialTranspose_signCubeSample]
    exact finiteSignSample_isHermitian _ _
  have hR := pptTest_psd_of_opNorm hd hH hO
  have hΓ : (partialTranspose (pptTest (signCubeSample ω))).PosSemidef := by
    rw [pptTest_partialTranspose]
    exact pptTest_psd_of_opNorm hd hPT hT
  exact ⟨ω, finiteSignSample_conditional hk hdim _ _ hQ hR hΓ⟩

/-- Witness family for every admissible pair of dimensions and Schmidt cutoff. -/
theorem exists_indecomposable_kEB (k d : ℕ) (hk : 2 ≤ k) (hdim : 524288 * k ^ 3 ≤ d) :
    ∃ Φ : MatrixMap (Fin d) (Fin d) ℂ, IsKEB k Φ ∧ ¬ IsDecomposable Φ := by
  obtain ⟨_, Φ, _, hEB, hInd⟩ := finiteSignSample_unconditional hk hdim
  exact ⟨Φ, hEB, hInd⟩

end D5.S3.Quantum.Entanglement.EntanglementBreaking
