/- GID: D5/S3/Quantum/Matrix/LinGProperty/Result
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinGProperty/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound, D5/S3/Quantum/Matrix/LinGProperty/SpectralConclusion]
   utility: none
   digest: The geometric-mean singular-value comparison for trace augmentation. -/

import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
import D5.S3.Quantum.Matrix.LinGProperty.SpectralConclusion

/-! The comparison includes every positive block matrix, including zero diagonal blocks. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.LinGProperty
open D5.S3.Quantum.Schatten

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem diagonal_blocks {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) : A.PosSemidef ∧ B.PosSemidef := by
  have heA : (fromBlocks A X Xᴴ B).submatrix Sum.inl Sum.inl = A := by ext i j; rfl
  have heB : (fromBlocks A X Xᴴ B).submatrix Sum.inr Sum.inr = B := by ext i j; rfl
  exact ⟨heA ▸ hW.submatrix Sum.inl, heB ▸ hW.submatrix Sum.inr⟩

private theorem mean_phi_posSemidef {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) {c : ℝ} (hc : 1 ≤ c) :
    (geometricMean (phi c A) (phi c B)).PosSemidef := by
  obtain ⟨hA, hB⟩ := diagonal_blocks hW
  by_cases ha : A = 0
  · simp only [ha, phi, Matrix.trace_zero, mul_zero, zero_smul, add_zero,
      geometricMean_zero_left]
    exact PosSemidef.zero
  by_cases hb : B = 0
  · simp only [hb, phi, Matrix.trace_zero, mul_zero, zero_smul, add_zero,
      geometricMean_zero_right]
    exact PosSemidef.zero
  exact (geometricMean_riccati (phi_posDef hA ha hc) (phi_posDef hB hb hc)).1.posSemidef

/-- Lin's comparison for all positive semidefinite block matrices and every decreasing index. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (A X B : Matrix (Fin n) (Fin n) ℂ)
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) (j : Fin n),
    singularValuesSorted (phi 1 X) ⟨j.val, by simpa using j.isLt⟩ ≤
      (mean_phi_posSemidef hW (c := 1) (by norm_num)).isHermitian.eigenvalues₀
        ⟨j.val, by simpa using j.isLt⟩

/-- The full positive trace-augmentation parameter family. -/
theorem parameter_family {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) {c : ℝ} (hc : 1 ≤ c)
    (j : Fin (Fintype.card (Fin n))) :
    singularValuesSorted (phi c X) j ≤
      (mean_phi_posSemidef hW hc).isHermitian.eigenvalues₀ j := by
  obtain ⟨hA, hB⟩ := diagonal_blocks hW
  by_cases hz : A = 0 ∨ B = 0
  · have hx := offDiagonal_eq_zero hW hz
    have hp := mean_phi_posSemidef hW hc
    have hn : 0 ≤ hp.isHermitian.eigenvalues₀ j := by
      simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
        hp.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
    have hzero : singularValuesSorted (phi c X) j = 0 := by
      rw [hx]
      simp only [phi, Matrix.trace_zero, mul_zero, zero_smul, add_zero]
      simpa only [Complex.ofReal_zero, zero_smul, zero_mul] using
        singularValuesSorted_smul_nonneg (0 : Matrix (Fin n) (Fin n) ℂ)
          0 le_rfl j
    exact hzero ▸ hn
  have hAn : A ≠ 0 := fun ha => hz (Or.inl ha)
  have hBn : B ≠ 0 := fun hb => hz (Or.inr hb)
  let a := A.trace.re
  let b := B.trace.re
  have ha : 0 < a := positive_trace hA hAn
  have hb : 0 < b := positive_trace hB hBn
  let r := (Real.sqrt a)⁻¹
  let s := (Real.sqrt b)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hra : r*r*a = 1 := by
    dsimp [r]
    rw [← mul_inv, Real.mul_self_sqrt ha.le, inv_mul_cancel₀ ha.ne']
  have hsb : s*s*b = 1 := by
    dsimp [s]
    rw [← mul_inv, Real.mul_self_sqrt hb.le, inv_mul_cancel₀ hb.ne']
  let A' := (r*r) • A
  let B' := (s*s) • B
  let X' := (r*s) • X
  have hW' : (fromBlocks A' X' X'ᴴ B').PosSemidef := block_scale_posSemidef hW r s
  have hat : A.trace = (a : ℂ) :=
    Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm)
  have hbt : B.trace = (b : ℂ) :=
    Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hB.trace_nonneg).2.symm)
  have hA' : A'.trace = 1 := by
    dsimp [A']; rw [Matrix.trace_smul, hat]
    apply Complex.ext
    · simpa only [Complex.smul_re, Complex.ofReal_re, smul_eq_mul, Complex.one_re] using hra
    · simp only [Complex.smul_im, Complex.ofReal_im, smul_zero, Complex.one_im]
  have hB' : B'.trace = 1 := by
    dsimp [B']; rw [Matrix.trace_smul, hbt]
    apply Complex.ext
    · simpa only [Complex.smul_re, Complex.ofReal_re, smul_eq_mul, Complex.one_re] using hsb
    · simp only [Complex.smul_im, Complex.ofReal_im, smul_zero, Complex.one_im]
  obtain ⟨hAp, hBp⟩ := diagonal_blocks hW'
  have hL1 := normalized_arithmetic_bound hW' hA' hB' hAp hBp j
  have hnorm := normalized_conclusion hW' hA' hB' hc j hAp hBp hL1
    (mean_phi_posSemidef hW' hc).isHermitian
  have hmean : geometricMean (phi c A') (phi c B') =
      (r*s) • geometricMean (phi c A) (phi c B) := by
    rw [show phi c A' = (r*r) • phi c A from phi_smul c (r*r) A,
      show phi c B' = (s*s) • phi c B from phi_smul c (s*s) B]
    rw [geometricMean_smul (phi_posDef hA hAn hc) (phi_posDef hB hBn hc)
      (mul_pos hr hr) (mul_pos hs hs)]
    congr 1
    rw [show r*r*(s*s) = (r*s)^2 by ring, Real.sqrt_sq (mul_pos hr hs).le]
  have hphi : phi c X' = (r*s) • phi c X := phi_smul c (r*s) X
  have hsing : singularValuesSorted (phi c X') j =
      (r*s) * singularValuesSorted (phi c X) j := by
    rw [hphi]
    exact singularValuesSorted_smul_nonneg _ _ (mul_pos hr hs).le j
  have hGM := (mean_phi_posSemidef hW hc).isHermitian
  have hGMs : ((r*s) • geometricMean (phi c A) (phi c B)).IsHermitian :=
    hGM.smul (show IsSelfAdjoint (r*s) from IsSelfAdjoint.all _)
  have heig := eigenvalues_zero_smul _ hGM (r*s) (mul_pos hr hs).le hGMs j
  have heig' : (mean_phi_posSemidef hW' hc).isHermitian.eigenvalues₀ j =
      (r*s) * (mean_phi_posSemidef hW hc).isHermitian.eigenvalues₀ j := by
    have he := ((mean_phi_posSemidef hW' hc).isHermitian.eigenvalues_eq_eigenvalues_iff
      hGMs).mpr (congrArg Matrix.charpoly hmean)
    have hj := congrFun he ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
    have he0 : (mean_phi_posSemidef hW' hc).isHermitian.eigenvalues₀ j =
        hGMs.eigenvalues₀ j := by
      simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using hj
    exact he0.trans heig
  rw [hsing, heig'] at hnorm
  exact (mul_le_mul_iff_right₀ (mul_pos hr hs)).mp hnorm

/-- The conjectured trace-augmentation inequality holds in every dimension. -/
theorem result : conjecture := by
  intro n A X B hW j
  exact parameter_family hW (c := 1) (by norm_num) ⟨j.val, by simpa using j.isLt⟩

end D5.S3.Quantum.Matrix.LinGProperty
