/- GID: D5/S3/Quantum/Matrix/LinPsiMap/Result
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinPsiMap/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both indexed spectral properties of the twice-trace reflection map. -/

import D5.S3.Quantum.Matrix.LinPsiMap.ReductionBlock
import D5.S3.Quantum.Matrix.LinPsiMap.GramDiscrepancy
import D5.S3.Quantum.Matrix.LinGProperty.Result

/-! The two comparisons follow from the reduction block and the common trace overlap. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.LinPsiMap
open D5.S3.Quantum.Matrix.LinGProperty
open D5.S3.Quantum.Schatten

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem psi_smul {n : ℕ} (r : ℝ) (T : Matrix (Fin n) (Fin n) ℂ) :
    psi (r • T) = r • psi T := by
  simp only [psi, Matrix.trace_smul, smul_sub, smul_smul]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  push_cast
  ring

private theorem psi_phase {n : ℕ} (z : ℂ) (T : Matrix (Fin n) (Fin n) ℂ) :
    psi (z • T) = z • psi T := by
  simp only [psi, Matrix.trace_smul, smul_sub, smul_smul, smul_eq_mul]
  congr 1
  ring

private theorem psi_posSemidef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) : (psi A).PosSemidef := by
  have ht : A.trace = (A.trace.re : ℂ) :=
    Complex.ext (by simp) (by simpa using (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm)
  have hR := trace_identity_sub_posSemidef A hA
  have hI : ((A.trace.re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    PosSemidef.one.smul (Complex.zero_le_real.mpr (Complex.nonneg_iff.mp hA.trace_nonneg).1)
  convert hI.add hR using 1
  rw [psi, ht]
  module

private theorem psi_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hne : A ≠ 0) : (psi A).PosDef := by
  have ht : A.trace = (A.trace.re : ℂ) :=
    Complex.ext (by simp) (by simpa using (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm)
  have hR := trace_identity_sub_posSemidef A hA
  have hI : ((A.trace.re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    PosDef.one.smul (Complex.zero_lt_real.mpr (positive_trace hA hne))
  convert Matrix.PosDef.posSemidef_add hR hI using 1
  rw [psi, ht]
  module

private theorem mean_psi_posSemidef {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) :
    (geometricMean (psi A) (psi B)).PosSemidef := by
  obtain ⟨hA, hB⟩ := diagonal_blocks hW
  by_cases ha : A = 0
  · simp only [ha, psi, trace_zero, mul_zero, zero_smul, sub_zero, geometricMean_zero_left]
    exact PosSemidef.zero
  by_cases hb : B = 0
  · simp only [hb, psi, trace_zero, mul_zero, zero_smul, sub_zero, geometricMean_zero_right]
    exact PosSemidef.zero
  exact (geometricMean_riccati (psi_posDef hA ha) (psi_posDef hB hb)).1.posSemidef

private theorem geometricMean_le_arithmetic {n : ℕ} {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) :
    geometricMean P Q ≤ (1 / 2 : ℝ) • (P + Q) := by
  let G := geometricMean P Q
  have hG : G.PosDef := (geometricMean_riccati hP hQ).1
  have hR : G * P⁻¹ * G = Q := (geometricMean_riccati hP hQ).2
  letI := hP.isUnit.invertible
  have hpos : 0 ≤ (G - P) * P⁻¹ * (G - P) :=
    (hG.isHermitian.sub hP.isHermitian).isSelfAdjoint.conjugate_nonneg
      hP.inv.posSemidef.nonneg
  have hR' : G * (P⁻¹ * G) = Q := by simpa only [mul_assoc] using hR
  have he : (G-P)*P⁻¹*(G-P) = P+Q-(2:ℝ) • G := by
    simp only [sub_mul, mul_sub]
    simp only [mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_inv_of_invertible,
      one_mul, mul_one, hR']
    module
  rw [he] at hpos
  have hh := smul_le_smul_of_nonneg_left (sub_nonneg.mp hpos)
    (by norm_num : (0:ℝ) ≤ 1/2)
  convert hh using 1 <;> module

private theorem discrepancy_posSemidef {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) : (A+B-X-Xᴴ).PosSemidef := by
  let C : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ := fromCols 1 (-1)
  have hh := hW.mul_mul_conjTranspose_same C
  convert hh using 1
  dsimp [C]
  rw [fromCols_mul_fromBlocks, conjTranspose_fromCols_eq_fromRows_conjTranspose,
    fromCols_mul_fromRows]
  simp
  abel

private theorem normalized_phase_conclusion {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) (hA : A.trace = 1) (hB : B.trace = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (hXt : X.trace = (t : ℂ))
    (j : Fin (Fintype.card (Fin n))) :
    singularValuesSorted (psi X) j ≤
      (mean_psi_posSemidef hW).isHermitian.eigenvalues₀ j := by
  obtain ⟨hAp, hBp⟩ := diagonal_blocks hW
  have ht : ‖X.trace‖ = t := by rw [hXt, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have ht1 : t ≤ 1 := by simpa only [ht] using normalized_trace_norm_le_one hW hA hB
  have hAn : A ≠ 0 := by intro hz; simpa [hz] using hA
  have hBn : B ≠ 0 := by intro hz; simpa [hz] using hB
  have hP := psi_posDef hAp hAn
  have hQ := psi_posDef hBp hBn
  let R := (1 : Matrix (Fin n) (Fin n) ℂ) - A
  let S := (1 : Matrix (Fin n) (Fin n) ℂ) - B
  let Y := (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Xᴴ
  have hR : R.PosSemidef := by
    simpa only [hA, Complex.one_re, Complex.ofReal_one, one_smul] using
      trace_identity_sub_posSemidef A hAp
  have hS : S.PosSemidef := by
    simpa only [hB, Complex.one_re, Complex.ofReal_one, one_smul] using
      trace_identity_sub_posSemidef B hBp
  have hY : Yᴴ = (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X := by simp [Y]
  have hred : (fromBlocks R Y Yᴴ S).PosSemidef := by
    have hh := reduction_block_posSemidef hW
    simpa [R, S, Y, hA, hB, trace_conjTranspose, hXt] using hh
  have hdisc : (((2*(1-t) : ℝ) : ℂ) • 1 - (R+S-Y-Yᴴ)).PosSemidef := by
    convert discrepancy_posSemidef hW using 1
    rw [hY]
    dsimp [R, S, Y]
    push_cast
    module
  have hL1 := gram_discrepancy_bound R Y S hred (by linarith : 0 ≤ 2*(1-t))
    hdisc hR hS j
  have hsing : singularValuesSorted Y j =
      singularValuesSorted ((t : ℂ) • 1 - X) j := by
    rw [← hY]
    exact (singularValuesSorted_conjTranspose Y j).symm
  rw [hsing] at hL1
  let H := (1/2 : ℝ) • (psi A + psi B)
  have hH : H.IsHermitian := (hP.isHermitian.add hQ.isHermitian).smul (by simp)
  have hPa : psi A = (2 : ℂ) • 1 - A := by simp [psi, hA]
  have hQb : psi B = (2 : ℂ) • 1 - B := by simp [psi, hB]
  have hfloor : (1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ H := by
    have hr := (hR.add hS).smul (by norm_num : (0:ℝ) ≤ 1/2)
    apply Matrix.le_iff.mpr
    convert hr using 1
    dsimp [H, R, S]
    rw [hPa, hQb]
    module
  have hsquare : ((1/2:ℝ) • (psi A-psi B)) * ((1/2:ℝ) • (psi A-psi B)) ≤
      ((1-t^2)/4) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have hsqC := normalized_difference_square_le hW hA hB
    rw [ht] at hsqC
    have hsq : (A-B)*(A-B) ≤ (1-t^2) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      apply Matrix.le_iff.mpr
      convert hsqC using 1
    have hh := smul_le_smul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 1/4)
    convert hh using 1
    · rw [hPa,hQb]
      have he : ((2:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-A)-((2:ℂ) • 1-B) = -(A-B) := by abel
      rw [he]
      simp [smul_mul_smul, smul_smul, div_eq_mul_inv]
      <;> norm_num
      noncomm_ring
    · rw [smul_smul]
      congr 1
      ring
  have hmean := arithmetic_sub_le_geometricMean hP hQ (by norm_num : (0:ℝ) < 1)
    hfloor hsquare
  let d := (1-t^2)/4
  let L := H + ((-d : ℝ) : ℂ) • 1
  have hL : L.IsHermitian := hH.add (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have hG := (mean_psi_posSemidef hW).isHermitian
  have hmean' : (geometricMean (psi A) (psi B)-L).PosSemidef := by
    apply Matrix.le_iff.mp
    convert hmean using 1
    dsimp [L,d,H]
    simp only [div_one, neg_smul]
    abel
  have hmono := eigenvalues_zero_mono hL hG hmean' j
  have hshift := eigenvalues_zero_add_scalar H hH (-d) hL j
  have hsum : R+S = ((2:ℝ):ℂ) • H + ((-2:ℝ):ℂ) • 1 := by
    dsimp [R,S,H]
    rw [hPa,hQb]
    module
  have h2H : (((2:ℝ):ℂ) • H).IsHermitian := hH.smul (by simp)
  have hRSeq := eigenvalues_zero_eq_of_charpoly (hR.1.add hS.1)
    (h2H.add (isHermitian_one.smul (by simp [IsSelfAdjoint])))
    (congrArg Matrix.charpoly hsum) j
  have hRSshift := eigenvalues_zero_add_scalar (((2:ℝ):ℂ) • H) h2H (-2)
    (h2H.add (isHermitian_one.smul (by simp [IsSelfAdjoint]))) j
  have hscale := eigenvalues_zero_smul H hH 2 (by norm_num) h2H j
  rw [hRSshift, hscale] at hRSeq
  rw [hRSeq] at hL1
  have hpert := singularValuesSorted_add_scalar ((t:ℂ) • 1-X) (t:ℂ) j
  have hpsi : ((t:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-X)+(t:ℂ) • 1 = psi X := by
    rw [psi,hXt]
    module
  rw [hpsi, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at hpert
  dsimp [d] at hshift
  nlinarith [sq_nonneg (1-t)]

private theorem normalized_conclusion {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) (hA : A.trace = 1) (hB : B.trace = 1)
    (j : Fin (Fintype.card (Fin n))) :
    singularValuesSorted (psi X) j ≤
      (mean_psi_posSemidef hW).isHermitian.eigenvalues₀ j := by
  obtain ⟨z,hz,hzt⟩ := exists_trace_phase X
  have hWz := block_posSemidef_phase hW z hz
  have hh := normalized_phase_conclusion hWz hA hB (norm_nonneg _) hzt j
  rw [psi_phase, singularValuesSorted_phase (psi X) z hz j] at hh
  exact hh

private theorem full_g_property {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) (j : Fin (Fintype.card (Fin n))) :
    singularValuesSorted (psi X) j ≤
      (mean_psi_posSemidef hW).isHermitian.eigenvalues₀ j := by
  obtain ⟨hA,hB⟩ := diagonal_blocks hW
  by_cases hz : A = 0 ∨ B = 0
  · have hx := offDiagonal_eq_zero hW hz
    have hp := mean_psi_posSemidef hW
    have hn : 0 ≤ hp.isHermitian.eigenvalues₀ j := by
      simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
        hp.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
    have hzero : singularValuesSorted (psi X) j = 0 := by
      rw [hx]
      simp only [psi, Matrix.trace_zero, mul_zero, zero_smul, sub_zero]
      simpa only [Complex.ofReal_zero, zero_smul, zero_mul] using
        singularValuesSorted_smul_nonneg (0 : Matrix (Fin n) (Fin n) ℂ) 0 le_rfl j
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
  have hnorm := normalized_conclusion hW' hA' hB' j
  have hmean : geometricMean (psi A') (psi B') =
      (r*s) • geometricMean (psi A) (psi B) := by
    rw [show psi A' = (r*r) • psi A from psi_smul (r*r) A,
      show psi B' = (s*s) • psi B from psi_smul (s*s) B]
    rw [geometricMean_smul (psi_posDef hA hAn) (psi_posDef hB hBn)
      (mul_pos hr hr) (mul_pos hs hs)]
    congr 1
    rw [show r*r*(s*s) = (r*s)^2 by ring, Real.sqrt_sq (mul_pos hr hs).le]
  have hsing : singularValuesSorted (psi X') j =
      (r*s) * singularValuesSorted (psi X) j := by
    rw [show psi X' = (r*s) • psi X from psi_smul (r*s) X]
    exact singularValuesSorted_smul_nonneg _ _ (mul_pos hr hs).le j
  have hGM := (mean_psi_posSemidef hW).isHermitian
  have hGMs : ((r*s) • geometricMean (psi A) (psi B)).IsHermitian :=
    hGM.smul (show IsSelfAdjoint (r*s) from IsSelfAdjoint.all _)
  have heig := eigenvalues_zero_smul _ hGM (r*s) (mul_pos hr hs).le hGMs j
  have heig' : (mean_psi_posSemidef hW').isHermitian.eigenvalues₀ j =
      (r*s) * (mean_psi_posSemidef hW).isHermitian.eigenvalues₀ j := by
    have he := ((mean_psi_posSemidef hW').isHermitian.eigenvalues_eq_eigenvalues_iff
      hGMs).mpr (congrArg Matrix.charpoly hmean)
    have hj := congrFun he ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
    have he0 : (mean_psi_posSemidef hW').isHermitian.eigenvalues₀ j =
        hGMs.eigenvalues₀ j := by
      simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using hj
    exact he0.trans heig
  rw [hsing,heig'] at hnorm
  exact (mul_le_mul_iff_right₀ (mul_pos hr hs)).mp hnorm

private theorem full_a_property {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) (j : Fin (Fintype.card (Fin n))) :
    2 * singularValuesSorted (psi X) j ≤
      ((psi_posSemidef (diagonal_blocks hW).1).isHermitian.add
        (psi_posSemidef (diagonal_blocks hW).2).isHermitian).eigenvalues₀ j := by
  obtain ⟨hA,hB⟩ := diagonal_blocks hW
  have hsum := (psi_posSemidef hA).add (psi_posSemidef hB)
  by_cases hz : A = 0 ∨ B = 0
  · have hx := offDiagonal_eq_zero hW hz
    have hn : 0 ≤ hsum.isHermitian.eigenvalues₀ j := by
      simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
        hsum.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
    have hzero : singularValuesSorted (psi X) j = 0 := by
      rw [hx]
      simp only [psi, Matrix.trace_zero, mul_zero, zero_smul, sub_zero]
      simpa only [Complex.ofReal_zero, zero_smul, zero_mul] using
        singularValuesSorted_smul_nonneg (0 : Matrix (Fin n) (Fin n) ℂ) 0 le_rfl j
    simpa only [hzero,mul_zero] using hn
  have hAn : A ≠ 0 := fun ha => hz (Or.inl ha)
  have hBn : B ≠ 0 := fun hb => hz (Or.inr hb)
  have hmean := geometricMean_le_arithmetic (psi_posDef hA hAn) (psi_posDef hB hBn)
  have hhalf := hsum.isHermitian.smul (show IsSelfAdjoint (1/2:ℝ) from IsSelfAdjoint.all _)
  have hm := eigenvalues_zero_mono (mean_psi_posSemidef hW).isHermitian hhalf
    (Matrix.le_iff.mp hmean) j
  have hs := eigenvalues_zero_smul (psi A+psi B) hsum.isHermitian (1/2)
    (by norm_num) hhalf j
  have hg := full_g_property hW j
  linarith

/-- The a-property and g-property for the twice-trace reflection map. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (A X B : Matrix (Fin n) (Fin n) ℂ)
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) (j : Fin n),
    (2 * singularValuesSorted (psi X) ⟨j.val, by simpa using j.isLt⟩ ≤
      ((psi_posSemidef (diagonal_blocks hW).1).isHermitian.add
        (psi_posSemidef (diagonal_blocks hW).2).isHermitian).eigenvalues₀
          ⟨j.val, by simpa using j.isLt⟩) ∧
    (singularValuesSorted (psi X) ⟨j.val, by simpa using j.isLt⟩ ≤
      (mean_psi_posSemidef hW).isHermitian.eigenvalues₀ ⟨j.val, by simpa using j.isLt⟩)

/-- Both conjectured indexed comparisons hold in every dimension. -/
theorem result : conjecture := by
  intro n A X B hW j
  exact ⟨full_a_property hW ⟨j.val, by simpa using j.isLt⟩,
    full_g_property hW ⟨j.val, by simpa using j.isLt⟩⟩

end D5.S3.Quantum.Matrix.LinPsiMap
