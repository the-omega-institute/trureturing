/- GID: D5/S3/Quantum/Divergence/SingleCoordinateSchur
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/SingleCoordinateSchur
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Schur and shifted log determinant bounds for one-coordinate pinching. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A Löwner sandwich controls the Schur complement of the shifted retained block. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Divergence.SingleCoordinateSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev scalarBlock (t : ℝ) : Matrix Unit Unit ℂ := t • 1

private theorem scalarBlock_posDef {t : ℝ} (ht : 0 < t) :
    (scalarBlock t).PosDef :=
  Matrix.PosDef.one.smul ht

private theorem scalarBlock_inv {t : ℝ} (ht : 0 < t) :
    (scalarBlock t)⁻¹ = scalarBlock t⁻¹ := by
  apply Matrix.inv_eq_right_inv
  change (t • (1 : Matrix Unit Unit ℂ)) * (t⁻¹ • (1 : Matrix Unit Unit ℂ)) = 1
  rw [Matrix.smul_mul, Matrix.mul_smul, mul_one, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

private theorem schur_midpoint (C : Matrix ι ι ℂ) (h : Matrix ι Unit ℂ)
    (a lam u v : ℝ) (F : Matrix ι ι ℂ)
    (hlo : u • fromBlocks C 0 0 (scalarBlock lam) ≤ fromBlocks F h hᴴ (scalarBlock a))
    (hhi : fromBlocks F h hᴴ (scalarBlock a) ≤ v • fromBlocks C 0 0 (scalarBlock lam)) :
    (fromBlocks (((v - u) / 2) • C) h hᴴ (scalarBlock (((v - u) / 2) * lam))).PosSemidef := by
  let J : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ := fromBlocks 1 0 0 (-1)
  have hmid := ((Matrix.le_iff.mp hlo).add
    ((Matrix.le_iff.mp hhi).conjTranspose_mul_mul_same J)).smul (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  convert hmid using 1
  simp only [J, sub_eq_add_neg, fromBlocks_smul, fromBlocks_neg, fromBlocks_add,
    fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_one, conjTranspose_neg,
    conjTranspose_zero, smul_zero, neg_zero, add_zero, zero_add, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  congr 1 <;> module

/-- A two-sided Löwner bound gives a dimension-independent Schur term bound and an
exact shifted determinant ratio for pinching one coordinate. The logarithmic deficit
is dominated by an integrable product of two scalar resolvents. -/
theorem schur_det_log_bound (C F : Matrix ι ι ℂ) (h : Matrix ι Unit ℂ)
    (a lam c u v s : ℝ) (hC : C.PosDef) (hlam : 0 < lam) (hc : 0 < c) (hu : 0 < u)
    (hd : 0 < (v - u) / 2) (hdu : (v - u) / 2 < u) (hs : 0 ≤ s)
    (hcap : C ≤ c • (1 : Matrix ι ι ℂ))
    (hlo : u • fromBlocks C 0 0 (lam • 1 : Matrix Unit Unit ℂ) ≤
      fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ))
    (hhi : fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ) ≤
      v • fromBlocks C 0 0 (lam • 1 : Matrix Unit Unit ℂ)) :
    let d := (v - u) / 2
    let A := fromBlocks F h hᴴ (a • 1 : Matrix Unit Unit ℂ)
    let A₀ := fromBlocks F 0 0 (a • 1 : Matrix Unit Unit ℂ)
    let q := (hᴴ * (F + s • 1)⁻¹ * h) () () |>.re
    0 ≤ q ∧ q ≤ d ^ 2 * lam * c / (u * c + s) ∧
    (A + s • 1).det.re / (A₀ + s • 1).det.re = 1 - q / (a + s) ∧
    0 ≤ q / (a + s) ∧ q / (a + s) ≤ d ^ 2 * lam * c / ((u * c + s) * (u * lam + s)) ∧
    d ^ 2 * lam * c / ((u * c + s) * (u * lam + s)) ≤ d ^ 2 / u ^ 2 ∧
    0 ≤ Real.log (A₀ + s • 1).det.re - Real.log (A + s • 1).det.re ∧
    Real.log (A₀ + s • 1).det.re - Real.log (A + s • 1).det.re ≤
      (d ^ 2 * lam * c / ((u * c + s) * (u * lam + s))) / (1 - d ^ 2 / u ^ 2) := by
  intro d A A₀ q
  let M := F + s • (1 : Matrix ι ι ℂ)
  let k := u + s / c
  let t := d ^ 2 * lam / k
  have hk : 0 < k := by dsimp [k]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hmass : 0 < d * lam := mul_pos hd hlam
  have hlow := Matrix.le_iff.mp hlo
  have hF : u • C ≤ F := by
    apply Matrix.le_iff.mpr
    exact hlow.submatrix (Sum.inl : ι → ι ⊕ Unit)
  have ha : u * lam ≤ a := by
    have hdiag := (Complex.nonneg_iff.mp (hlow.diag_nonneg (i := Sum.inr ()))).1
    simpa [fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.smul_apply, Complex.smul_re] using hdiag
  have hMlower : k • C ≤ M := by
    have hshift : (s / c) • C ≤ s • (1 : Matrix ι ι ℂ) := by
      calc
        (s / c) • C ≤ (s / c) • (c • (1 : Matrix ι ι ℂ)) :=
          smul_le_smul_of_nonneg_left hcap (div_nonneg hs hc.le)
        _ = _ := by rw [smul_smul, div_mul_cancel₀ _ hc.ne']
    rw [show k • C = u • C + (s / c) • C by exact add_smul _ _ _]
    exact add_le_add hF hshift
  have hM : M.PosDef := by
    have h := (hC.smul hk).add_posSemidef (Matrix.le_iff.mp hMlower)
    rwa [add_comm, sub_add_cancel] at h
  let : Invertible M := hM.isUnit.invertible
  have hcoupling : h * hᴴ ≤ (d ^ 2 * lam) • C := by
    let : Invertible (scalarBlock (d * lam)) := (scalarBlock_posDef hmass).isUnit.invertible
    have hschur := (Matrix.PosDef.fromBlocks₂₂ (d • C) h (scalarBlock_posDef hmass)).mp
      (schur_midpoint C h a lam u v F hlo hhi)
    rw [scalarBlock_inv hmass] at hschur
    have horder : (d * lam)⁻¹ • (h * hᴴ) ≤ d • C := by
      simpa only [scalarBlock, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] using
        (Matrix.le_iff.mpr hschur)
    have := smul_le_smul_of_nonneg_left horder hmass.le
    simpa only [smul_smul, mul_inv_cancel₀ hmass.ne', one_smul,
      show d * lam * d = d ^ 2 * lam by ring] using this
  have hqt : q ≤ t := by
    let : Invertible (scalarBlock t) := (scalarBlock_posDef ht).isUnit.invertible
    have hscaled : t⁻¹ • (h * hᴴ) ≤ M := by
      calc
        t⁻¹ • (h * hᴴ) ≤ t⁻¹ • ((d ^ 2 * lam) • C) :=
          smul_le_smul_of_nonneg_left hcoupling (inv_nonneg.mpr ht.le)
        _ = k • C := by
          rw [smul_smul]
          congr 1
          dsimp [t]
          field_simp [hk.ne', show d ≠ 0 from hd.ne', hlam.ne']
        _ ≤ M := hMlower
    have htest := (Matrix.PosDef.fromBlocks₂₂ M h (scalarBlock_posDef ht)).mpr
      (Matrix.le_iff.mp (show h * (scalarBlock t)⁻¹ * hᴴ ≤ M by
        rw [scalarBlock_inv ht]
        simpa only [scalarBlock, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] using hscaled))
    have hschur := (Matrix.PosDef.fromBlocks₁₁ h (scalarBlock t) hM).mp htest
    have hdiag := (Complex.nonneg_iff.mp (hschur.diag_nonneg (i := ()))).1
    change q ≤ t
    apply sub_nonneg.mp
    simpa [scalarBlock, Matrix.sub_apply, Matrix.smul_apply, q, M] using hdiag
  have hq0 : 0 ≤ q :=
    (Complex.nonneg_iff.mp ((hM.inv.posSemidef.conjTranspose_mul_mul_same h).diag_nonneg
      (i := ()))).1
  have huc : 0 < u * c + s := by positivity
  have hulam : 0 < u * lam + s := by positivity
  have has : 0 < a + s := hulam.trans_le (add_le_add_left ha s)
  have htval : t = d ^ 2 * lam * c / (u * c + s) := by
    dsimp [t, k]
    field_simp [hk.ne', hc.ne', huc.ne']
  rw [htval] at hqt
  let r := q / (a + s)
  let b := d ^ 2 * lam * c / ((u * c + s) * (u * lam + s))
  let B := d ^ 2 / u ^ 2
  have hr : 0 ≤ r := div_nonneg hq0 has.le
  have hrb : r ≤ b := by
    dsimp [r, b]
    rw [← div_div]
    exact (div_le_div_of_nonneg_left hq0 hulam (add_le_add_left ha s)).trans
      (div_le_div_of_nonneg_right hqt hulam.le)
  have hbB : b ≤ B := by
    dsimp [b, B]
    apply (div_le_div_iff₀ (mul_pos huc hulam) (by positivity : 0 < u ^ 2)).mpr
    calc
      _ = d ^ 2 * ((u * c) * (u * lam)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul (le_add_of_nonneg_right hs) (le_add_of_nonneg_right hs)
          (by positivity) huc.le) (sq_nonneg d)
  have hB : B < 1 := (div_lt_one (by positivity)).mpr (pow_lt_pow_left₀ hdu hd.le (by decide))
  have hr1 : 0 < 1 - r := sub_pos.mpr ((hrb.trans hbB).trans_lt hB)
  have hId : (1 : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) =
      fromBlocks (1 : Matrix ι ι ℂ) 0 0 (1 : Matrix Unit Unit ℂ) := fromBlocks_one.symm
  have hshiftA : A + s • 1 = fromBlocks M h hᴴ (scalarBlock (a + s)) := by
    rw [hId]
    simp only [A, M, scalarBlock, add_smul, fromBlocks_smul, fromBlocks_add, smul_zero, add_zero]
  have hshiftA₀ : A₀ + s • 1 = fromBlocks M 0 0 (scalarBlock (a + s)) := by
    rw [hId]
    simp only [A₀, M, scalarBlock, add_smul, fromBlocks_smul, fromBlocks_add, smul_zero, add_zero]
  have hdetM := Complex.pos_iff.mp hM.det_pos
  have hdet : (A + s • 1).det.re = M.det.re * (a + s - q) := by
    rw [hshiftA, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (scalarBlock (a + s) - hᴴ * M⁻¹ * h),
      Complex.mul_re, ← hdetM.2, zero_mul, sub_zero]
    simp [scalarBlock, Matrix.sub_apply, Matrix.smul_apply, q, M]
  have hdet₀ : (A₀ + s • 1).det.re = M.det.re * (a + s) := by
    rw [hshiftA₀, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (scalarBlock (a + s)),
      Complex.mul_re,
      ← hdetM.2, zero_mul, sub_zero]
    simp [scalarBlock, Matrix.smul_apply]
  have hratio : (A + s • 1).det.re / (A₀ + s • 1).det.re = 1 - r := by
    rw [hdet, hdet₀]
    dsimp [r]
    field_simp [hdetM.1.ne', has.ne']
  have hpos₀ : 0 < (A₀ + s • 1).det.re := hdet₀ ▸ mul_pos hdetM.1 has
  have hpos : 0 < (A + s • 1).det.re :=
    (div_pos_iff_of_pos_right hpos₀).mp (hratio ▸ hr1)
  have hlog : Real.log (A₀ + s • 1).det.re - Real.log (A + s • 1).det.re =
      -Real.log (1 - r) := by rw [← hratio, Real.log_div hpos.ne' hpos₀.ne', neg_sub]
  refine ⟨hq0, hqt, hratio, hr, hrb, hbB, ?_, ?_⟩
  · rw [hlog]
    exact neg_nonneg.mpr (Real.log_nonpos hr1.le (by linarith))
  · rw [hlog]
    calc
      -Real.log (1 - r) ≤ r / (1 - r) := by
        have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hr1)
        rw [Real.log_inv, inv_eq_one_div, show 1 / (1 - r) - 1 = r / (1 - r) by
          field_simp
          ring] at h
        exact h
      _ ≤ r / (1 - B) :=
        div_le_div_of_nonneg_left hr (sub_pos.mpr hB) (sub_le_sub_left (hrb.trans hbB) 1)
      _ ≤ b / (1 - B) := div_le_div_of_nonneg_right hrb (sub_nonneg.mpr hB.le)

#print axioms schur_det_log_bound

end D5.S3.Quantum.Divergence.SingleCoordinateSchur
