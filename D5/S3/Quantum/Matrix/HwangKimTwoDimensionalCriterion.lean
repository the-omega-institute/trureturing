/- GID: D5/S3/Quantum/Matrix/HwangKimTwoDimensionalCriterion
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HwangKimTwoDimensionalCriterion
   mirror-E: none(waiver:noncomputable-matrix-analysis)
   anchors: [D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation]
   utility: none
   digest: The exact determinant and trace criterion for near order in dimension two. -/

import D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

/-!
The exact iff is equation (criterion) of Ma–Zhang revision2, issue #29594,
CC BY 4.0. Haobo Ma: ChronoAI, Singapore; Wenlin Zhang: NUS and ChronoAI,
Singapore. The original trace obstruction's Cayley–Hamilton identities are
shared with their original owner, not reproved here. The new inference is
the sufficient direction: the product and sum constraints exclude a
positive transport eigenvalue below one. This concerns actual metric
geometric means, with positive definite L,W and det L=1.
This general theorem is not a finite numerical certificate.
-/

noncomputable section
open Matrix Unitary
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
open private transport_trace_identities nearOrder_riccati
  from D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

namespace D5.S3.Quantum.Matrix.HwangKimTwoDimensionalCriterion

private theorem one_le_iff_det_trace {C : Matrix (Fin 2) (Fin 2) ℂ}
    (hC : C.PosDef) :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ≤ C ↔
      1 ≤ C.det.re ∧ C.trace.re ≤ 1 + C.det.re := by
  let v := hC.isHermitian.eigenvalues
  let e := conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) hC.isHermitian.eigenvectorUnitary
  have he : e (diagonal (fun i => (v i : ℂ))) = C :=
    hC.isHermitian.spectral_theorem.symm
  have hd : e (diagonal (fun i => (v i : ℂ)) - 1) = C - 1 := by
    rw [map_sub, he, map_one]
  have hs : (1 : Matrix (Fin 2) (Fin 2) ℂ) ≤ C ↔ ∀ i, 1 ≤ v i := by
    rw [Matrix.le_iff, ← hd]
    change (hC.isHermitian.eigenvectorUnitary.val *
      (diagonal (fun i => (v i : ℂ)) - 1) *
        (hC.isHermitian.eigenvectorUnitary.val)ᴴ).PosSemidef ↔ _
    rw [← star_eq_conjTranspose,
      (Unitary.isUnit_coe (U := hC.isHermitian.eigenvectorUnitary)).posSemidef_star_right_conjugate_iff]
    have hh : diagonal (fun i => (v i : ℂ)) - 1 =
        diagonal (fun i => ((v i - 1 : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hh, Matrix.posSemidef_diagonal_iff]
    simp only [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im,
      eq_self_iff_true, and_true, sub_nonneg]
  have hdet : C.det.re = v 0 * v 1 := by
    rw [hC.isHermitian.det_eq_prod_eigenvalues, Fin.prod_univ_two]
    simp [v]
  have htrace : C.trace.re = v 0 + v 1 := by
    rw [hC.isHermitian.trace_eq_sum_eigenvalues, Fin.sum_univ_two]
    simp [v]
  rw [hs, hdet, htrace]
  have h0 : 0 < v 0 := hC.eigenvalues_pos 0
  have h1 : 0 < v 1 := hC.eigenvalues_pos 1
  constructor
  · intro h
    constructor
    · nlinarith [h 0, h 1, mul_nonneg (sub_nonneg.mpr (h 0)) (sub_nonneg.mpr (h 1))]
    · nlinarith [mul_nonneg (sub_nonneg.mpr (h 0)) (sub_nonneg.mpr (h 1))]
  · rintro ⟨hp, ht⟩ i
    have hv0 : 1 ≤ v 0 := by
      by_contra hn
      have hn : v 0 < 1 := lt_of_not_ge hn
      have hv1 : 1 < v 1 := by nlinarith
      nlinarith [mul_neg_of_neg_of_pos (sub_neg.mpr hn) (sub_pos.mpr hv1)]
    have hv1 : 1 ≤ v 1 := by
      by_contra hn
      have hn : v 1 < 1 := lt_of_not_ge hn
      have hv0 : 1 < v 0 := by nlinarith
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hv0) (sub_neg.mpr hn)]
    fin_cases i <;> assumption

/-- Exact two-dimensional near-order criterion, including the determinant
condition and the sufficient direction absent from the original obstruction. -/
theorem near_order_iff {L W : Matrix (Fin 2) (Fin 2) ℂ}
    (hL : L.PosDef) (hW : W.PosDef) (hdetL : L.det = 1) :
    NearOrder L W ↔
      1 ≤ Real.sqrt W.det.re ∧
      (W.trace.re + Real.sqrt W.det.re * L.trace.re)^2 -
        (1 + Real.sqrt W.det.re)^2 *
          ((L*W).trace.re + 2 * Real.sqrt W.det.re) ≤ 0 := by
  let C := D5.S3.Quantum.Hiai.PsiMeanTraceConcavity.geometricMean (1/2) L⁻¹ W
  let d := Real.sqrt W.det.re
  obtain ⟨hC, hric⟩ := nearOrder_riccati hL hW
  have hd : 0 < d := Real.sqrt_pos.mpr (Complex.pos_iff.mp hW.det_pos).1
  have hdetW : W.det = (d^2 : ℝ) := by
    apply Complex.ext
    · exact (Real.sq_sqrt (Complex.pos_iff.mp hW.det_pos).1.le).symm
    · simpa [pow_two] using (Complex.nonneg_iff.mp hW.posSemidef.det_nonneg).2.symm
  obtain ⟨hdetC, htrace, htrace2⟩ :=
    transport_trace_identities hL hC hd hdetL hdetW hric
  have hdc : C.det.re = d := congrArg Complex.re hdetC
  have htc : 0 ≤ C.trace.re := (Complex.nonneg_iff.mp hC.posSemidef.trace_nonneg).1
  have htL : 0 < L.trace.re := (Complex.pos_iff.mp hL.trace_pos).1
  have htW : 0 < W.trace.re := (Complex.pos_iff.mp hW.trace_pos).1
  have htLC : 0 < (L*C).trace.re := by
    have hprod : 0 < W.trace.re + d * L.trace.re := by positivity
    change W.trace.re + d * L.trace.re = (L*C).trace.re * C.trace.re at htrace
    rw [htrace] at hprod
    nlinarith
  change (1 : Matrix (Fin 2) (Fin 2) ℂ) ≤ C ↔ _
  rw [one_le_iff_det_trace hC, hdc]
  change 1 ≤ d ∧ C.trace.re ≤ 1+d ↔
    1 ≤ d ∧ (W.trace.re+d*L.trace.re)^2 -
      (1+d)^2*((L*W).trace.re+2*d) ≤ 0
  rw [htrace, htrace2]
  have he : ((L*C).trace.re*C.trace.re)^2 -
      (1+d)^2*(L*C).trace.re^2 =
      (L*C).trace.re^2 * (C.trace.re^2 - (1+d)^2) := by ring
  rw [he]
  have hf : 0 < (L*C).trace.re^2 := sq_pos_of_pos htLC
  constructor
  · rintro ⟨hd1, ht⟩
    exact ⟨hd1, mul_nonpos_of_nonneg_of_nonpos hf.le
      (sub_nonpos.mpr ((sq_le_sq₀ htc (by positivity)).mpr ht))⟩
  · rintro ⟨hd1, ht⟩
    have hsq : C.trace.re^2 ≤ (1+d)^2 := by
      by_contra hn
      have hp := mul_pos hf (sub_pos.mpr (lt_of_not_ge hn))
      linarith
    exact ⟨hd1, (sq_le_sq₀ htc (by positivity)).mp hsq⟩

end D5.S3.Quantum.Matrix.HwangKimTwoDimensionalCriterion
