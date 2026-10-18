/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Joint moment of ordered real defects under the literal positive semidefinite constraint. -/
/- UNCOMPILED integration changes; original upstream proofs are preserved. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone
import Mathlib.Analysis.Matrix.PosDef

/-! Joint moments of ordered real defects under the literal PSD constraint. -/

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
noncomputable section

private theorem z_matrix_psd_mono {n : Type*} [Finite n]
    {M N : Matrix n n ℝ} (hM : M.PosSemidef) (hN : N.IsHermitian)
    (hZ : ∀ i j, i ≠ j → N i j ≤ 0) (hMN : ∀ i j, M i j ≤ N i j) :
    N.PosSemidef := by
  classical
  letI := Fintype.ofFinite n
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hN
  intro x
  have h0 := hM.dotProduct_mulVec_nonneg (fun i => |x i|)
  simp only [dotProduct, mulVec, star_trivial, Pi.star_apply,
    Finset.mul_sum] at h0 ⊢
  calc
    0 ≤ ∑ i, ∑ j, |x i| * (M i j * |x j|) := h0
    _ ≤ ∑ i, ∑ j, |x i| * (N i j * |x j|) := by
      apply sum_le_sum; intro i _
      apply sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hMN i j) (abs_nonneg _)) (abs_nonneg _)
    _ ≤ ∑ i, ∑ j, x i * (N i j * x j) := by
      apply sum_le_sum; intro i _
      apply sum_le_sum; intro j _
      by_cases hij : i = j
      · subst j
        apply le_of_eq
        calc
          |x i| * (N i i * |x i|) = N i i * |x i| ^ 2 := by ring
          _ = N i i * (x i) ^ 2 := by rw [sq_abs]
          _ = x i * (N i i * x i) := by ring
      · have hc := mul_le_mul_of_nonpos_left (le_abs_self (x i * x j)) (hZ i j hij)
        rw [abs_mul] at hc
        nlinarith only [hc]

private def actualK (h : Fin 5 → ℝ) (d : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2 * (1 - d 8), -(h 0 + d 7), -(h 1 + d 5);
     -(h 0 + d 7), 2 * (1 - d 6), -(h 2 + d 4);
     -(h 1 + d 5), -(h 2 + d 4), 2 * (1 - d 3)]

private theorem actualK_form (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (x : Fin 3 → ℝ) :
    star x ⬝ᵥ (actualK h d *ᵥ x) =
      2 * (1 - d 8) * (x 0) ^ 2 + 2 * (1 - d 6) * (x 1) ^ 2 + 2 * (1 - d 3) * (x 2) ^ 2 -
      2 * (h 0 + d 7) * x 0 * x 1 - 2 * (h 1 + d 5) * x 0 * x 2 - 2 * (h 2 + d 4) * x 1 * x 2 := by
  simp [actualK, dotProduct, mulVec, Fin.sum_univ_succ]
  ring

-- Half of the full plus/minus congruence; no invertibility premise is needed.
private def actualP (h : Fin 5 → ℝ) (d : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2 - h 0 - (d 6 + d 7 + d 8), -(d 8 - d 6), -(h 1 + h 2 + d 4 + d 5) / 2;
     -(d 8 - d 6), 2 + h 0 + d 7 - d 6 - d 8, -(h 1 - h 2 + d 5 - d 4) / 2;
     -(h 1 + h 2 + d 4 + d 5) / 2, -(h 1 - h 2 + d 5 - d 4) / 2, 1 - d 3]

private theorem actualK_hermitian (h : Fin 5 → ℝ) (d : Fin 9 → ℝ) :
    (actualK h d).IsHermitian := by
  change (actualK h d)ᴴ = actualK h d
  ext i j
  fin_cases i <;> fin_cases j <;> simp [actualK, Matrix.conjTranspose]

private theorem actualP_hermitian (h : Fin 5 → ℝ) (d : Fin 9 → ℝ) :
    (actualP h d).IsHermitian := by
  change (actualP h d)ᴴ = actualP h d
  ext i j
  fin_cases i <;> fin_cases j <;> simp [actualP, Matrix.conjTranspose]

private theorem actualP_psd (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (hK : (actualK h d).PosSemidef) : (actualP h d).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (actualP_hermitian h d)
  intro x
  have hid : star x ⬝ᵥ (actualP h d *ᵥ x) =
      (star (![x 0 + x 1, x 0 - x 1, x 2] : Fin 3 → ℝ) ⬝ᵥ
        (actualK h d *ᵥ ![x 0 + x 1, x 0 - x 1, x 2])) / 2 := by
    simp [actualP, actualK, dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  rw [hid]
  exact div_nonneg (hK.dotProduct_mulVec_nonneg _) (by norm_num)

private theorem actualK_psd_of_actualP (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (hP : (actualP h d).PosSemidef) : (actualK h d).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (actualK_hermitian h d)
  intro x
  have hid : star x ⬝ᵥ (actualK h d *ᵥ x) =
      2 * (star (![(x 0 + x 1) / 2, (x 0 - x 1) / 2, x 2] : Fin 3 → ℝ) ⬝ᵥ
        (actualP h d *ᵥ ![(x 0 + x 1) / 2, (x 0 - x 1) / 2, x 2])) := by
    simp [actualP, actualK, dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  rw [hid]
  exact mul_nonneg (by norm_num) (hP.dotProduct_mulVec_nonneg _)

private theorem delete_head_psd (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (hn : ∀ i, 0 ≤ h i) (dn : ∀ i, 0 ≤ d i)
    (hK : (actualK h d).PosSemidef) : (actualK 0 d).PosSemidef := by
  apply z_matrix_psd_mono hK (actualK_hermitian 0 d)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num at hij <;> norm_num [actualK] <;> linarith [dn 4, dn 5, dn 7]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [actualK] <;> linarith [hn 0, hn 1, hn 2]

-- The original ordered-block supplier, with its original proof, pays D2 ≤ r².
private theorem ordered_tail_bounds (d : Fin 9 → ℝ)
    (dn : ∀ i, 0 ≤ d i) (dord : Monotone d) :
    (∑ i, (d i) ^ 2) ≤ (d 6 + d 7 + d 8) ^ 2 ∧
      d 6 + d 7 + d 8 ≤ ∑ i, d i ∧ (∑ i, d i) ≤ 3 * (d 6 + d 7 + d 8) := by
  have he := ordered_block_energy
    (fun i : Fin 3 => (![d 6, d 7, d 8] : Fin 3 → ℝ) i)
    (fun i : Fin 6 => (![d 0, d 1, d 2, d 3, d 4, d 5] : Fin 6 → ℝ) i) (d 6)
    (dn 6)
    (by intro i; fin_cases i <;> exact dord (by decide))
    (by intro i; fin_cases i <;> exact dn _)
    (by intro i; fin_cases i <;> exact dord (by decide))
    (by norm_num) (by norm_num)
  simp only [Fin.sum_univ_succ, Matrix.cons_val,
    Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at he ⊢
  refine ⟨by nlinarith only [he], ?_, ?_⟩
  · linarith [dn 0, dn 1, dn 2, dn 3, dn 4, dn 5]
  · linarith [dord (show (0 : Fin 9) ≤ 6 by decide),
      dord (show (1 : Fin 9) ≤ 7 by decide), dord (show (2 : Fin 9) ≤ 8 by decide),
      dord (show (3 : Fin 9) ≤ 6 by decide), dord (show (4 : Fin 9) ≤ 7 by decide),
      dord (show (5 : Fin 9) ≤ 8 by decide)]

private theorem tail_variance_bound (d : Fin 9 → ℝ)
    (dn : ∀ i, 0 ≤ d i) (dord : Monotone d) :
    (∑ i, (d i) ^ 2) ≤ (d 6 + d 7 + d 8) ^ 2 / 3 +
      (2 / 3) * (d 8 - d 6) ^ 2 + (d 4 + d 5) ^ 2 + 2 * (d 3) ^ 2 := by
  have hs (i : Fin 9) (hi : i ≤ 3) : (d i) ^ 2 ≤ (d 3) ^ 2 := by
    have h := dord hi
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (dn 3) (dn i))]
  have huv : (d 3) ^ 2 ≤ d 4 * d 5 := by
    have h34 := dord (show (3 : Fin 9) ≤ 4 by decide)
    have h35 := dord (show (3 : Fin 9) ≤ 5 by decide)
    nlinarith [mul_nonneg (sub_nonneg.mpr h34) (dn 5),
      mul_nonneg (dn 3) (sub_nonneg.mpr h35)]
  have hpq := dord (show (6 : Fin 9) ≤ 7 by decide)
  have hqt := dord (show (7 : Fin 9) ≤ 8 by decide)
  have hlast := mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hqt)
  simp only [Fin.sum_univ_succ, Fin.reduceSucc,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  nlinarith only [hs 0 (by decide), hs 1 (by decide), hs 2 (by decide), huv, hlast]

-- Scalar combination of the two envelopes, with rational polynomial factors.
private theorem sharp_tail_envelopes (r u T : ℝ)
    (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hu0 : 0 ≤ u) (hu2 : u ≤ 1 / 2)
    (hsq : T ≤ r ^ 2)
    (hf : T ≤ r ^ 2 / 3 + 4 * (2 - r) * (1 - u) + 2 * u ^ 2)
    (hg : 3 / 2 ≤ r → T ≤ 7 * r ^ 2 / 9 + 2 * u ^ 2) : T ≤ 9 / 4 := by
  by_cases hr : r ≤ 3 / 2
  · nlinarith [mul_nonneg (by linarith : 0 ≤ 3 / 2 - r) (by linarith : 0 ≤ 3 / 2 + r)]
  · have hr' : 3 / 2 ≤ r := le_of_lt (lt_of_not_ge hr)
    by_cases hR : r ≤ 27 / 16
    · let u0 : ℝ := 7 / 2 - 2 * r
      have hu00 : 0 ≤ u0 := by dsimp [u0]; linarith
      by_cases hu : u ≤ u0
      · have husq : u ^ 2 ≤ u0 ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hu) (add_nonneg hu00 hu0)]
        have hp := mul_nonneg (by linarith : 0 ≤ 2 * r - 3)
          (by linarith : 0 ≤ 267 - 158 * r)
        have hh := hg hr'
        dsimp [u0] at husq
        nlinarith only [hh, husq, hp]
      · have hu' : u0 ≤ u := le_of_lt (lt_of_not_ge hu)
        have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu')
          (by linarith : u - 1 / 2 ≤ 0)
        have hq := mul_nonneg (by linarith : 0 ≤ 2 * r - 3)
          (by linarith : 0 ≤ 9 - 2 * r)
        dsimp [u0] at hp
        nlinarith only [hf, hp, hq]
    · have hR' : 27 / 16 ≤ r := le_of_lt (lt_of_not_ge hR)
      have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hR')
        (by linarith : (r + 27 / 16) / 3 - 4 + 4 * u ≤ 0)
      have hq := mul_nonpos_of_nonneg_of_nonpos hu0 (by linarith : u - 5 / 8 ≤ 0)
      nlinarith only [hf, hp, hq]

private theorem sharp_tail_square (d : Fin 9 → ℝ)
    (dn : ∀ i, 0 ≤ d i) (dord : Monotone d) (du : ∀ i, d i ≤ 1)
    (hK : (actualK 0 d).PosSemidef) : (∑ i, (d i) ^ 2) ≤ 9 / 4 := by
  let r := d 6 + d 7 + d 8
  let u := d 3
  let δ := d 8 - d 6
  let B := d 4 + d 5
  let C := 1 - u
  let Am := 2 + d 7 - d 6 - d 8
  let L := d 5 - d 4
  have h110 := hK.dotProduct_mulVec_nonneg (![1, 1, 0] : Fin 3 → ℝ)
  have h111 := hK.dotProduct_mulVec_nonneg (![1, 1, 1] : Fin 3 → ℝ)
  rw [actualK_form] at h110 h111
  norm_num at h110 h111
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [dn 6, dn 7, dn 8]
  have hr2 : r ≤ 2 := by dsimp [r]; linarith only [h110]
  have hu0 : 0 ≤ u := dn 3
  have h3u : 3 * u ≤ r := by
    dsimp [r, u]
    linarith [dord (show (3 : Fin 9) ≤ 6 by decide),
      dord (show (3 : Fin 9) ≤ 7 by decide), dord (show (3 : Fin 9) ≤ 8 by decide)]
  have h3ur : 3 * u + r ≤ 3 := by
    dsimp [r, u]
    linarith [h111, dord (show (3 : Fin 9) ≤ 4 by decide),
      dord (show (3 : Fin 9) ≤ 5 by decide)]
  have hu2 : u ≤ 1 / 2 := by linarith
  have hC : 0 < C := by dsimp [C]; linarith
  have hδ : 0 ≤ δ := sub_nonneg.mpr (dord (by decide))
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith [du 8, dn 6]
  have hB : 0 ≤ B := add_nonneg (dn 4) (dn 5)
  have hL : 0 ≤ L := sub_nonneg.mpr (dord (by decide))
  have hAm3 : Am ≤ 3 := by dsimp [Am]; linarith only [du 7, dn 6, dn 8]
  have hC6 : 3 ≤ 6 * C := by dsimp [C]; linarith only [hu2]
  have hAm : Am ≤ 6 * C := hAm3.trans hC6
  have hP := actualP_psd 0 d hK
  have htest := hP.dotProduct_mulVec_nonneg (![6 * C, δ, 3 * B] : Fin 3 → ℝ)
  have hform : star (![6 * C, δ, 3 * B] : Fin 3 → ℝ) ⬝ᵥ
      (actualP 0 d *ᵥ ![6 * C, δ, 3 * B]) =
      36 * C ^ 2 * (2 - r) + (Am - 12 * C) * δ ^ 2 - 9 * C * B ^ 2 - 3 * L * δ * B := by
    dsimp [C, u, δ, B, r, Am, L]
    simp [actualP, dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  rw [hform] at htest
  have hcharge := mul_nonneg (sub_nonneg.mpr hAm) (sq_nonneg δ)
  have hcross := mul_nonneg (mul_nonneg hL hδ) hB
  have hbudget : (2 / 3) * δ ^ 2 + B ^ 2 ≤ 4 * C * (2 - r) := by
    have hp : 0 ≤ C * (12 * C * (2 - r) - 2 * δ ^ 2 - 3 * B ^ 2) := by
      nlinarith only [htest, hcharge, hcross]
    have hi : 0 ≤ 12 * C * (2 - r) - 2 * δ ^ 2 - 3 * B ^ 2 := by
      by_contra h
      have hneg := mul_neg_of_pos_of_neg hC (lt_of_not_ge h)
      linarith only [hp, hneg]
    linarith only [hi]
  have hvar : (∑ i, (d i) ^ 2) ≤ r ^ 2 / 3 + (2 / 3) * δ ^ 2 + B ^ 2 + 2 * u ^ 2 :=
    tail_variance_bound d dn dord
  have hf : (∑ i, (d i) ^ 2) ≤ r ^ 2 / 3 + 4 * (2 - r) * (1 - u) + 2 * u ^ 2 := by
    dsimp [C] at hbudget
    nlinarith only [hvar, hbudget]
  apply sharp_tail_envelopes r u _ hr0 hr2 hu0 hu2
    (ordered_tail_bounds d dn dord).1 hf
  intro hr
  have hBupper : B ≤ 2 * (r - δ) / 3 := by
    dsimp [B, r, δ]
    linarith [dord (show (4 : Fin 9) ≤ 6 by decide),
      dord (show (5 : Fin 9) ≤ 6 by decide), dord (show (6 : Fin 9) ≤ 7 by decide)]
  have hBsquare : B ^ 2 ≤ 4 * (r - δ) ^ 2 / 9 := by
    have hpos : 0 ≤ 2 * (r - δ) / 3 + B := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hBupper) hpos]
  have hp := mul_nonpos_of_nonneg_of_nonpos hδ (by linarith : 5 * δ - 4 * r ≤ 0)
  nlinarith only [hvar, hBsquare, hp]

private def flatFormula (z e : ℝ) : ℝ :=
  z ^ 2 + 2 * e ^ 2 - (z + 2 * e) / 4 + max (e - 1 / 4) 0 * min (2 * e) (4 - z - 2 * e)

private theorem flat_lower_endpoint (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    flatFormula e e ≤ 7 / 2 := by
  by_cases he : e ≤ 1 / 4
  · simp only [flatFormula, max_eq_right (by linarith : e - 1 / 4 ≤ 0), zero_mul, add_zero]
    nlinarith [mul_nonneg he0 (by linarith : 0 ≤ 1 / 4 - e)]
  · have he' : 1 / 4 ≤ e := le_of_lt (lt_of_not_ge he)
    unfold flatFormula
    rw [max_eq_left (by linarith : 0 ≤ e - 1 / 4)]
    by_cases h4 : e ≤ 4 / 5
    · rw [min_eq_left (by linarith : 2 * e ≤ 4 - e - 2 * e)]
      have hp := mul_nonneg (by linarith : 0 ≤ 4 / 5 - e)
        (by linarith : 0 ≤ 5 * e + 11 / 4)
      nlinarith only [hp]
    · rw [min_eq_right (by linarith : 4 - e - 2 * e ≤ 2 * e)]
      nlinarith only [he1]

private theorem flat_upper_endpoint (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    flatFormula (2 - e ^ 2) e ≤ 7 / 2 := by
  have hesq : e ^ 2 ≤ e := by nlinarith [mul_nonneg he0 (sub_nonneg.mpr he1)]
  by_cases he : e ≤ 1 / 4
  · simp only [flatFormula, max_eq_right (by linarith : e - 1 / 4 ≤ 0), zero_mul, add_zero]
    have hp := mul_nonneg (sq_nonneg e) (by nlinarith : 0 ≤ 7 / 4 - e ^ 2)
    nlinarith only [hp, he0]
  · unfold flatFormula
    rw [max_eq_left (by linarith : 0 ≤ e - 1 / 4)]
    by_cases hc : 2 * e ≤ 4 - (2 - e ^ 2) - 2 * e
    · rw [min_eq_left hc]
      have he2 : e ≤ 2 / 3 := by nlinarith only [hesq, hc]
      have hcube : e ^ 3 ≤ 8 / 27 := by
        have hp := mul_nonneg (by linarith : 0 ≤ 2 / 3 - e)
          (by nlinarith [sq_nonneg e] : 0 ≤ e ^ 2 + (2 / 3) * e + 4 / 9)
        nlinarith only [hp]
      have hp := mul_nonneg he0 (by linarith : 0 ≤ 1 - e ^ 3 - e / 4)
      nlinarith only [hp]
    · rw [min_eq_right (by linarith : 4 - (2 - e ^ 2) - 2 * e ≤ 2 * e)]
      have hp := mul_nonneg (mul_nonneg (sq_nonneg e) (sub_nonneg.mpr he1))
        (by linarith : 0 ≤ e + 2)
      nlinarith only [hp, sq_nonneg (2 * e - 1)]

private theorem flat_kink (e : ℝ)
    (hl : e ≤ 4 - 4 * e) (hu : 4 - 4 * e ≤ 2 - e ^ 2) :
    flatFormula (4 - 4 * e) e ≤ 7 / 2 := by
  have he9 : 9 / 16 ≤ e := by
    by_contra h
    have hp := mul_nonneg_of_nonpos_of_nonpos
      (by linarith : e - 9 / 16 ≤ 0) (by linarith : e - 55 / 16 ≤ 0)
    nlinarith only [hp, hu]
  have hp := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ e - 9 / 16)
    (by linarith : 20 * e - 83 / 4 ≤ 0)
  unfold flatFormula
  rw [max_eq_left (by linarith : 0 ≤ e - 1 / 4),
    min_eq_left (by linarith : 2 * e ≤ 4 - (4 - 4 * e) - 2 * e)]
  nlinarith only [hp]

-- Each side of the kink uses the original quadratic interval supplier.
private theorem flat_interval_bound (z e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hz0 : e ≤ z) (hzA : z ≤ 2 - e ^ 2) : flatFormula z e ≤ 7 / 2 := by
  let A := 2 - e ^ 2
  let k := max (e - 1 / 4) 0
  let t := 4 - 4 * e
  let qL : ℝ → ℝ := fun y => y ^ 2 + (-1 / 4) * y + (2 * e ^ 2 - e / 2 + k * (2 * e))
  let qR : ℝ → ℝ := fun y => y ^ 2 + (-1 / 4 - k) * y + (2 * e ^ 2 - e / 2 + k * (4 - 2 * e))
  have hL (y : ℝ) (hy : y ≤ t) : flatFormula y e = qL y := by
    dsimp [flatFormula, qL, k]
    rw [min_eq_left (by dsimp [t] at hy; linarith : 2 * e ≤ 4 - y - 2 * e)]
    ring
  have hR (y : ℝ) (hy : t ≤ y) : flatFormula y e = qR y := by
    dsimp [flatFormula, qR, k]
    rw [min_eq_right (by dsimp [t] at hy; linarith : 4 - y - 2 * e ≤ 2 * e)]
    ring
  have hleft := flat_lower_endpoint e he0 he1
  have hright := flat_upper_endpoint e he0 he1
  by_cases hzt : z ≤ t
  · rw [hL z hzt]
    by_cases hAt : A ≤ t
    · apply quadratic_interval_le_fun qL 1 (-1 / 4) (2 * e ^ 2 - e / 2 + k * (2 * e))
        e A z (7 / 2) (by intro y; dsimp [qL]; ring) (by norm_num) hz0 hzA
      · rw [← hL e (by linarith)]; exact hleft
      · rw [← hL A hAt]; exact hright
    · have htA : t ≤ A := le_of_lt (lt_of_not_ge hAt)
      apply quadratic_interval_le_fun qL 1 (-1 / 4) (2 * e ^ 2 - e / 2 + k * (2 * e))
        e t z (7 / 2) (by intro y; dsimp [qL]; ring) (by norm_num) hz0 hzt
      · rw [← hL e (by linarith)]; exact hleft
      · rw [← hL t le_rfl]
        exact flat_kink e (by linarith) htA
  · have htz : t ≤ z := le_of_lt (lt_of_not_ge hzt)
    rw [hR z htz]
    by_cases hte : t ≤ e
    · apply quadratic_interval_le_fun qR 1 (-1 / 4 - k) (2 * e ^ 2 - e / 2 + k * (4 - 2 * e))
        e A z (7 / 2) (by intro y; dsimp [qR]; ring) (by norm_num) hz0 hzA
      · rw [← hR e hte]; exact hleft
      · rw [← hR A (by linarith)]; exact hright
    · have het : e ≤ t := le_of_lt (lt_of_not_ge hte)
      apply quadratic_interval_le_fun qR 1 (-1 / 4 - k) (2 * e ^ 2 - e / 2 + k * (4 - 2 * e))
        t A z (7 / 2) (by intro y; dsimp [qR]; ring) (by norm_num) htz hzA
      · rw [← hR t le_rfl]
        exact flat_kink e het (by linarith)
      · rw [← hR A (by linarith)]; exact hright

-- Shared original scalar PSD consequences, extracted from flat_five_moment.
-- Both the original zero-jump proof and the middle-energy proof consume them.
private theorem flat_third_head_le_one (a b e : ℝ)
    (hab : b ≤ a) (hbe : e ≤ b) (he0 : 0 ≤ e)
    (hdet : a ^ 2 + b ^ 2 + e ^ 2 + a * b * e ≤ 4) : e ≤ 1 := by
  have hb0 : 0 ≤ b := he0.trans hbe
  have ha0 : 0 ≤ a := hb0.trans hab
  have hae : e ≤ a := hbe.trans hab
  have habprod : e ^ 2 ≤ a * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hae) hb0,
      mul_nonneg he0 (sub_nonneg.mpr hbe)]
  have hecube : e ^ 3 + 3 * e ^ 2 ≤ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right habprod he0,
      mul_nonneg (sub_nonneg.mpr hae) (add_nonneg ha0 he0),
      mul_nonneg (sub_nonneg.mpr hbe) (add_nonneg hb0 he0)]
  by_contra h
  have hesq : 1 < e ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < e - 1) (by linarith : 0 < e + 1)]
  have hp := mul_nonneg (sq_nonneg e) (by linarith : 0 ≤ e - 1)
  nlinarith only [hecube, hesq, hp]

private theorem flat_endpoint_ge_third (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    e ≤ 2 - e ^ 2 := by
  have hp := mul_nonneg (sub_nonneg.mpr he1) (by linarith : 0 ≤ e + 2)
  nlinarith only [hp]

private theorem flat_pair_square_le_low (a b e : ℝ)
    (hae : e ≤ a) (hbe : e ≤ b) :
    a ^ 2 + b ^ 2 ≤ (a + b - e) ^ 2 + e ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hae) (sub_nonneg.mpr hbe)]

private theorem flat_pair_square_le_high (a b e : ℝ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hdet : a ^ 2 + b ^ 2 + e ^ 2 + a * b * e ≤ 4)
    (hs : (2 - e ^ 2) + e ≤ a + b) :
    a ^ 2 + b ^ 2 ≤ (2 - e ^ 2) ^ 2 + e ^ 2 := by
  let A := 2 - e ^ 2
  change A + e ≤ a + b at hs
  change a ^ 2 + b ^ 2 ≤ A ^ 2 + e ^ 2
  have hAe : e ≤ A := flat_endpoint_ge_third e he0 he1
  have hpoly : (2 - e) * (a ^ 2 + b ^ 2 - (A ^ 2 + e ^ 2)) ≤
      -e * ((a + b) - (A + e)) * ((a + b) + (A + e)) := by
    dsimp [A]
    nlinarith only [hdet]
  have hp := mul_nonneg (mul_nonneg he0 (sub_nonneg.mpr hs))
    (by linarith [hAe] : 0 ≤ (a + b) + (A + e))
  by_contra h
  have hpos := mul_pos (by linarith : 0 < 2 - e)
    (by linarith : 0 < a ^ 2 + b ^ 2 - (A ^ 2 + e ^ 2))
  linarith only [hpoly, hp, hpos]

private theorem flat_five_moment (a b e x y : ℝ)
    (hab : b ≤ a) (hbe : e ≤ b) (hex : x ≤ e) (hxy : y ≤ x) (hy0 : 0 ≤ y)
    (hmass : a + b + e + x + y ≤ 4) (hdet : a ^ 2 + b ^ 2 + e ^ 2 + a * b * e ≤ 4) :
    a ^ 2 + b ^ 2 + e ^ 2 + x ^ 2 + y ^ 2 - (a + b + e + x + y) / 4 ≤ 7 / 2 := by
  have hx0 : 0 ≤ x := by linarith
  have he0 : 0 ≤ e := by linarith
  have hae : e ≤ a := le_trans hbe hab
  have he1 := flat_third_head_le_one a b e hab hbe he0 hdet
  let k := max (e - 1 / 4) 0
  have hk : 0 ≤ k := le_max_right _ _
  have hc : (x ^ 2 - x / 4) + (y ^ 2 - y / 4) ≤ k * min (2 * e) (4 - (a + b) - e) := by
    by_cases he : e ≤ 1 / 4
    · have hk0 : k = 0 := max_eq_right (by linarith)
      rw [hk0, zero_mul]
      nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 / 4 - x),
        mul_nonneg hy0 (by linarith : 0 ≤ 1 / 4 - y)]
    · have hkval : k = e - 1 / 4 := max_eq_left (by linarith)
      have hmin : x + y ≤ min (2 * e) (4 - (a + b) - e) := le_min (by linarith) (by linarith)
      have hm := mul_le_mul_of_nonneg_left hmin hk
      rw [hkval] at hm ⊢
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hex),
        mul_nonneg hy0 (by linarith : 0 ≤ e - y)]
  let A := 2 - e ^ 2
  have hAe : e ≤ A := flat_endpoint_ge_third e he0 he1
  by_cases hs : a + b ≤ A + e
  · have hz0 : e ≤ a + b - e := by linarith
    have hzA : a + b - e ≤ 2 - e ^ 2 := by dsimp [A] at hs; linarith
    have hF := flat_interval_bound (a + b - e) e he0 he1 hz0 hzA
    have hq := flat_pair_square_le_low a b e hae hbe
    have hmin : 4 - (a + b) - e = 4 - (a + b - e) - 2 * e := by ring
    rw [hmin] at hc
    dsimp [flatFormula] at hF
    dsimp [k] at hc
    nlinarith only [hF, hc, hq]
  · have hs' : A + e ≤ a + b := le_of_lt (lt_of_not_ge hs)
    have hq := flat_pair_square_le_high a b e he0 he1 hdet hs'
    have hm : min (2 * e) (4 - (a + b) - e) ≤ min (2 * e) (4 - A - 2 * e) :=
      min_le_min le_rfl (by linarith)
    have hcmp := mul_le_mul_of_nonneg_left hm hk
    have hF := flat_interval_bound A e he0 he1 hAe le_rfl
    dsimp [flatFormula, A, k] at hF hc hcmp hq hs'
    nlinarith only [hF, hc, hcmp, hq, hs']

private theorem flat_head_determinant (h : Fin 5 → ℝ)
    (hK : (actualK h 0).PosSemidef) :
    (h 0) ^ 2 + (h 1) ^ 2 + (h 2) ^ 2 + h 0 * h 1 * h 2 ≤ 4 := by
  have hd := hK.det_nonneg
  norm_num [actualK, Matrix.det_fin_three] at hd
  nlinarith only [hd]

private theorem flat_head_moment (h : Fin 5 → ℝ)
    (hn : ∀ i, 0 ≤ h i) (ho : Antitone h) (hH : (∑ i, h i) ≤ 4)
    (hK : (actualK h 0).PosSemidef) :
    (∑ i, (h i) ^ 2) - (∑ i, h i) / 4 ≤ 7 / 2 := by
  have hd' := flat_head_determinant h hK
  have hh := flat_five_moment (h 0) (h 1) (h 2) (h 3) (h 4)
    (ho (by decide)) (ho (by decide)) (ho (by decide)) (ho (by decide)) (hn 4)
    (by simpa [Fin.sum_univ_succ, add_assoc] using hH) hd'
  simpa [Fin.sum_univ_succ, add_assoc] using hh

private def flatHead (h : Fin 5 → ℝ) (d : Fin 9 → ℝ) : Fin 5 → ℝ :=
  ![h 0 + (d 6 + d 7 + d 8), h 1, h 2, h 3, h 4]

-- Entrywise monotonicity is used in the full congruent Z-matrix, not in K.
private theorem tail_to_head_psd (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (hn : ∀ i, 0 ≤ h i) (ho : Antitone h)
    (dn : ∀ i, 0 ≤ d i) (dord : Monotone d)
    (hK : (actualK h d).PosSemidef) : (actualK (flatHead h d) 0).PosSemidef := by
  apply actualK_psd_of_actualP
  apply z_matrix_psd_mono (actualP_psd h d hK) (actualP_hermitian (flatHead h d) 0)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num at hij <;> norm_num [actualP, flatHead] <;>
      linarith [hn 1, hn 2, ho (show (1 : Fin 5) ≤ 2 by decide)]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [actualP, flatHead] <;>
      linarith [dn 3, dn 4, dn 5, dn 6, dn 8,
        dord (show (4 : Fin 9) ≤ 5 by decide), dord (show (6 : Fin 9) ≤ 8 by decide)]

-- Shared original flatHead bookkeeping, extracted from large_head_moment.
-- Both that proof and the w-dependent transfer below consume it.
private theorem flatHead_facts (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (hn : ∀ i, 0 ≤ h i) (ho : Antitone h)
    (dn : ∀ i, 0 ≤ d i) (dord : Monotone d) :
    (∑ i, flatHead h d i) = (∑ i, h i) + (d 6 + d 7 + d 8) ∧
    (∑ i, (flatHead h d i) ^ 2) =
      (∑ i, (h i) ^ 2) + 2 * h 0 * (d 6 + d 7 + d 8) + (d 6 + d 7 + d 8) ^ 2 ∧
    (∀ i, 0 ≤ flatHead h d i) ∧ Antitone (flatHead h d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [flatHead, Fin.sum_univ_succ] <;> ring
  · simp [flatHead, Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> simp [flatHead] <;>
      linarith [hn 0, hn 1, hn 2, hn 3, hn 4, dn 6, dn 7, dn 8]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num [flatHead] <;>
      linarith [ho (show (0 : Fin 5) ≤ 1 by decide), ho (show (1 : Fin 5) ≤ 2 by decide),
        ho (show (2 : Fin 5) ≤ 3 by decide), ho (show (3 : Fin 5) ≤ 4 by decide),
        dn 6, dn 7, dn 8]

private theorem large_head_moment (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (hn : ∀ i, 0 ≤ h i) (ho : Antitone h)
    (dn : ∀ i, 0 ≤ d i) (dord : Monotone d)
    (hL4 : (∑ i, h i) + (∑ i, d i) ≤ 4)
    (hK : (actualK h d).PosSemidef) (hlarge : 1 / 2 ≤ h 0) :
    (∑ i, (h i) ^ 2) + (∑ i, (d i) ^ 2) - ((∑ i, h i) - (∑ i, d i)) / 4 ≤ 7 / 2 := by
  let r := d 6 + d 7 + d 8
  have hr : 0 ≤ r := by dsimp [r]; linarith [dn 6, dn 7, dn 8]
  obtain ⟨hD2, hrD, hD⟩ := ordered_tail_bounds d dn dord
  obtain ⟨hsum, hsum2, hflat_nonneg, hflat_order⟩ := flatHead_facts h d hn ho dn dord
  change (∑ i, flatHead h d i) = (∑ i, h i) + r at hsum
  change (∑ i, (flatHead h d i) ^ 2) = (∑ i, (h i) ^ 2) + 2 * h 0 * r + r ^ 2 at hsum2
  have hflat_mass : (∑ i, flatHead h d i) ≤ 4 := by
    rw [hsum]
    change r ≤ ∑ i, d i at hrD
    linarith only [hrD, hL4]
  have hflat := flat_head_moment (flatHead h d) hflat_nonneg hflat_order hflat_mass
    (tail_to_head_psd h d hn ho dn dord hK)
  have htransfer :
      (∑ i, (h i) ^ 2) + (∑ i, (d i) ^ 2) - ((∑ i, h i) - (∑ i, d i)) / 4 ≤
      (∑ i, (flatHead h d i) ^ 2) - (∑ i, flatHead h d i) / 4 := by
    rw [hsum2, hsum]
    have hp := mul_nonneg hr (by linarith : 0 ≤ h 0 - 1 / 2)
    change (∑ i, (d i) ^ 2) ≤ r ^ 2 at hD2
    change (∑ i, d i) ≤ 3 * r at hD
    nlinarith only [hD2, hD, hp]
  exact htransfer.trans hflat

/-- The dimension-independent zero-middle-jump moment bound for all five
ordered nonnegative head defects and all nine ordered tail defects in [0,1].
The positive-semidefinite premise is the literal actual defect matrix. -/
theorem actual_psd_zero_jump_moment (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (dord : Monotone d) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (hL4 : (∑ i, h i) + (∑ i, d i) ≤ 4)
    (hK : (!![2 * (1 - d 8), -(h 0 + d 7), -(h 1 + d 5);
                -(h 0 + d 7), 2 * (1 - d 6), -(h 2 + d 4);
                -(h 1 + d 5), -(h 2 + d 4), 2 * (1 - d 3)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef) :
    (∑ i, (h i) ^ 2) + (∑ i, (d i) ^ 2) - ((∑ i, h i) - (∑ i, d i)) / 4 ≤ (7 / 2 : ℝ) := by
  change (actualK h d).PosSemidef at hK
  have dn : ∀ i, 0 ≤ d i := fun i => (hd i).1
  by_cases hsmall : h 0 ≤ 1 / 2
  · have htail := sharp_tail_square d dn dord (fun i => (hd i).2)
      (delete_head_psd h d hn dn hK)
    have hh : (∑ i, (h i) ^ 2) ≤ (∑ i, h i) / 2 := by
      calc
        _ ≤ ∑ i, h i / 2 := by
          apply sum_le_sum
          intro i _
          have hi : h i ≤ 1 / 2 := (ho (show (0 : Fin 5) ≤ i from Fin.zero_le i)).trans hsmall
          nlinarith [mul_nonneg (hn i) (by linarith : 0 ≤ 1 / 2 - h i)]
        _ = _ := by rw [Finset.sum_div]
    have hsmall_bound :
        (∑ i, (h i) ^ 2) + (∑ i, (d i) ^ 2) - ((∑ i, h i) - (∑ i, d i)) / 4 ≤ (13 / 4 : ℝ) := by
      linarith only [hh, htail, hL4]
    linarith only [hsmall_bound]
  · exact large_head_moment h d hn ho dn dord hL4 hK (by linarith)

-- The middle proof uses scalar comparison points, not replacement PSD spectra.
-- In particular, the second minimum entry may be negative at such a point.
private def middleFormula (w z e : ℝ) : ℝ :=
  z ^ 2 + 2 * e ^ 2 - w * (z + 2 * e) +
    e * min (2 * (e - w)) (4 - 3 * w - z - 2 * e)

private def middleFull (w e : ℝ) : ℝ :=
  4 - 2 * w - 4 * w * e + w * e ^ 2 + e ^ 4

private def middleTrunc (w e : ℝ) : ℝ :=
  4 - 2 * w + 2 * e - 5 * w * e + (w - 4) * e ^ 2 + e ^ 3 + e ^ 4

private theorem middleFormula_eq_min (w z e : ℝ) (he0 : 0 ≤ e) :
    middleFormula w z e =
      min (z ^ 2 + 4 * e ^ 2 - w * z - 4 * w * e)
        (z ^ 2 - (w + e) * z + (4 - 5 * w) * e) := by
  unfold middleFormula
  rw [mul_min_of_nonneg _ _ he0, ← min_add_add_left]
  congr 1 <;> ring

private theorem middleFormula_mono (w z A e : ℝ)
    (hw0 : 0 ≤ w) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hz : 1 + w ≤ z) (hzA : z ≤ A) :
    middleFormula w z e ≤ middleFormula w A e := by
  rw [middleFormula_eq_min w z e he0, middleFormula_eq_min w A e he0]
  apply min_le_min
  · have hp := mul_nonneg (sub_nonneg.mpr hzA)
      (by linarith : 0 ≤ A + z - w)
    nlinarith only [hp]
  · have hp := mul_nonneg (sub_nonneg.mpr hzA)
      (by linarith : 0 ≤ A + z - w - e)
    nlinarith only [hp]

-- Exact nonnegative decomposition of the reversed full-polynomial secant.
private theorem middleFull_le_at_w (w t : ℝ)
    (hw : 1 / 4 ≤ w) (hwt : w ≤ t) (ht : t ≤ 1 / 2) :
    middleFull w t ≤ middleFull w w := by
  have hw0 : 0 ≤ w := by linarith
  have ht0 : 0 ≤ t := hw0.trans hwt
  have hw1 : w ≤ 1 / 2 := hwt.trans ht
  have hbracket : 0 ≤ 4 * w - (t + w) * (t ^ 2 + w ^ 2 + w) := by
    calc
      _ = (1 - t - w) * (t ^ 2 + w ^ 2 + w) + (3 * w - 1 / 2) +
          (1 / 2 - t) * (1 / 2 + t) + (1 / 2 - w) * (1 / 2 + w) := by ring
      _ ≥ 0 := add_nonneg
        (add_nonneg
          (add_nonneg
            (mul_nonneg (by linarith) (by nlinarith only [sq_nonneg t, sq_nonneg w, hw0]))
            (by linarith))
          (mul_nonneg (by linarith) (by linarith)))
        (mul_nonneg (by linarith) (by linarith))
  have hp := mul_nonneg (sub_nonneg.mpr hwt) hbracket
  dsimp [middleFull]
  nlinarith only [hp]

private theorem middleTrunc_le_at_half (w e : ℝ)
    (hw : 1 / 4 ≤ w) (he : 1 / 2 ≤ e) (he1 : e ≤ 1) :
    middleTrunc w e ≤ middleTrunc w (1 / 2) := by
  have he0 : 0 ≤ e := by linarith
  have hp : 0 ≤ (e - 1 / 2) *
      (3 / 4 + e / 2 + e * (1 - e) * (e + 5 / 2) +
        (w - 1 / 4) * (9 / 2 - e)) := by
    apply mul_nonneg (by linarith)
    apply add_nonneg
    · exact add_nonneg (by linarith)
        (mul_nonneg (mul_nonneg he0 (by linarith)) (by linarith))
    · exact mul_nonneg (by linarith) (by linarith)
  dsimp [middleTrunc]
  nlinarith only [hp]

private theorem middle_upper_endpoint (w e : ℝ)
    (hw : 1 / 4 ≤ w) (hw1 : w ≤ 1 / 2) (hwe : w ≤ e) (he1 : e ≤ 1) :
    middleFormula w (2 - e ^ 2) e ≤ 4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4 := by
  have he0 : 0 ≤ e := by linarith
  have hpoly : middleFormula w (2 - e ^ 2) e =
      min (middleFull w e) (middleTrunc w e) := by
    rw [middleFormula_eq_min w (2 - e ^ 2) e he0]
    congr 1 <;> dsimp [middleFull, middleTrunc] <;> ring
  have htarget : middleFull w w = 4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4 := by
    dsimp [middleFull]
    ring
  rw [hpoly, ← htarget]
  by_cases he : e ≤ 1 / 2
  · exact (min_le_left _ _).trans (middleFull_le_at_w w e hw hwe he)
  · have he' : 1 / 2 ≤ e := le_of_lt (lt_of_not_ge he)
    have hbridge : middleTrunc w (1 / 2) ≤ middleFull w (1 / 2) := by
      dsimp [middleTrunc, middleFull]
      nlinarith only [hw]
    exact (min_le_right _ _).trans
      ((middleTrunc_le_at_half w e hw he' he1).trans
        (hbridge.trans (middleFull_le_at_w w (1 / 2) hw hw1 le_rfl)))

-- The original tail chord is used only at (a,b,e,x,y).
-- The shared fixed-e suppliers then permit the scalar comparison to A=2-e².
private theorem flat_five_middle_energy (w a b e x y : ℝ)
    (hw : 1 / 4 ≤ w) (hw1 : w ≤ 1 / 2) (ha : 1 + w ≤ a)
    (hab : b ≤ a) (hbe : e ≤ b) (hex : x ≤ e) (hxy : y ≤ x) (hyw : w ≤ y)
    (hmass : a + b + e + x + y ≤ 4 - w)
    (hdet : a ^ 2 + b ^ 2 + e ^ 2 + a * b * e ≤ 4) :
    a * (a - w) + b * (b - w) + e * (e - w) + x * (x - w) + y * (y - w) ≤
      4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4 := by
  have hw0 : 0 ≤ w := by linarith
  have hwe : w ≤ e := hyw.trans (hxy.trans hex)
  have he0 : 0 ≤ e := hw0.trans hwe
  have hae : e ≤ a := hbe.trans hab
  have he1 := flat_third_head_le_one a b e hab hbe he0 hdet
  let A := 2 - e ^ 2
  have hmin : x + y - 2 * w ≤ min (2 * (e - w)) (4 - 3 * w - (a + b) - e) :=
    le_min (by linarith) (by linarith only [hmass])
  have hc : x * (x - w) + y * (y - w) ≤
      e * min (2 * (e - w)) (4 - 3 * w - (a + b) - e) := by
    have hm := mul_le_mul_of_nonneg_left hmin he0
    have hx := mul_nonneg (by linarith : 0 ≤ x - w) (sub_nonneg.mpr hex)
    have hy := mul_nonneg (by linarith : 0 ≤ y - w) (by linarith : 0 ≤ e - y)
    nlinarith only [hm, hx, hy]
  have hG : a * (a - w) + b * (b - w) + e * (e - w) +
      x * (x - w) + y * (y - w) ≤ middleFormula w A e := by
    by_cases hs : a + b ≤ A + e
    · have hz : 1 + w ≤ a + b - e := by linarith
      have hzA : a + b - e ≤ A := by linarith
      have hq := flat_pair_square_le_low a b e hae hbe
      have hmono := middleFormula_mono w (a + b - e) A e hw0 he0 he1 hz hzA
      have hmin_eq : 4 - 3 * w - (a + b) - e =
          4 - 3 * w - (a + b - e) - 2 * e := by ring
      rw [hmin_eq] at hc
      dsimp [middleFormula] at hmono ⊢
      nlinarith only [hq, hc, hmono]
    · have hs' : A + e ≤ a + b := le_of_lt (lt_of_not_ge hs)
      have hq := flat_pair_square_le_high a b e he0 he1 hdet hs'
      have hm : min (2 * (e - w)) (4 - 3 * w - (a + b) - e) ≤
          min (2 * (e - w)) (4 - 3 * w - A - 2 * e) :=
        min_le_min le_rfl (by linarith)
      have hcmp := mul_le_mul_of_nonneg_left hm he0
      have hwcmp := mul_nonneg hw0 (sub_nonneg.mpr hs')
      change a ^ 2 + b ^ 2 ≤ A ^ 2 + e ^ 2 at hq
      dsimp [middleFormula]
      nlinarith only [hq, hc, hcmp, hwcmp]
  exact hG.trans (middle_upper_endpoint w e hw hw1 hwe he1)

/-- Dimension-independent middle energy for all ordered nonnegative real heads.
The sole matrix hypothesis is the literal flat-tail PSD matrix, including singular
matrices. Determinant, reduced-head caps and the tail chord are derived in the proof. -/
theorem actual_psd_flat_tail_middle_energy (w : ℝ) (h : Fin 5 → ℝ)
    (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (hH : (∑ i, h i) ≤ 4 - 6 * w) (hlarge : 1 ≤ h 0)
    (hw : 1 / 4 ≤ w) (hrho : w ≤ (5 - Real.sqrt 17) / 2)
    (hK : (!![2, -(w + h 0), -(w + h 1);
                -(w + h 0), 2, -(w + h 2);
                -(w + h 1), -(w + h 2), 2] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef) :
    w * (∑ i, h i) + (∑ i, (h i) ^ 2) ≤
      4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4 := by
  have hsqrt : 4 ≤ Real.sqrt 17 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
    have hn := Real.sqrt_nonneg (17 : ℝ)
    by_contra h
    have hp := mul_pos (by linarith : 0 < 4 - Real.sqrt 17)
      (by linarith : 0 < 4 + Real.sqrt 17)
    nlinarith only [hs, hp]
  have hw1 : w ≤ 1 / 2 := by linarith only [hrho, hsqrt]
  let g : Fin 5 → ℝ := fun i => w + h i
  have hgK : (actualK g 0).PosSemidef := by
    simpa [actualK, g] using hK
  have hd := flat_head_determinant g hgK
  have hbudget : g 0 + g 1 + g 2 + g 3 + g 4 ≤ 4 - w := by
    have hH' := hH
    simp only [Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hH'
    dsimp [g]
    linarith only [hH']
  have hb := flat_five_middle_energy w (g 0) (g 1) (g 2) (g 3) (g 4)
    hw hw1 (by dsimp [g]; linarith only [hlarge])
    (by dsimp [g]; linarith only [ho (show (0 : Fin 5) ≤ 1 by decide)])
    (by dsimp [g]; linarith only [ho (show (1 : Fin 5) ≤ 2 by decide)])
    (by dsimp [g]; linarith only [ho (show (2 : Fin 5) ≤ 3 by decide)])
    (by dsimp [g]; linarith only [ho (show (3 : Fin 5) ≤ 4 by decide)])
    (by dsimp [g]; linarith only [hn 4]) hbudget hd
  dsimp [g] at hb
  simp only [Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  nlinarith only [hb]

-- K_w(h,d) is exactly actualK (fun i => w + h i) d.
-- Its two original row budgets are derived, never added as PSD premises.
private theorem shifted_actual_defects (w : ℝ) (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (dord : Monotone d) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (hL4 : H h + D d ≤ 4 - 6 * w)
    (hK : (actualK (fun i => w + h i) d).PosSemidef) :
    DefectData 1 w h d := by
  have h111 := hK.dotProduct_mulVec_nonneg (![1, 1, 1] : Fin 3 → ℝ)
  have h110 := hK.dotProduct_mulVec_nonneg (![1, 1, 0] : Fin 3 → ℝ)
  rw [actualK_form] at h111 h110
  norm_num at h111 h110
  refine ⟨hn, ho, fun i => (hd i).1, dord, fun i => (hd i).2, ?_, ?_, ?_⟩
  · dsimp [H3, D6]
    linarith only [h111]
  · simpa only [mul_one] using hL4
  · dsimp [D3]
    linarith only [h110]

-- The w term charges D-r, not D.  The two original ordered-tail
-- conclusions pay it when w ≤ h0.  No compensation hypothesis is used.
private theorem shifted_flatHead_energy (w : ℝ) (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (hw : 0 ≤ w) (hn : ∀ i, 0 ≤ h i) (ho : Antitone h)
    (dn : ∀ i, 0 ≤ d i) (dord : Monotone d) (hlarge : w ≤ h 0)
    (hK : (actualK (fun i => w + h i) d).PosSemidef) :
    (actualK (fun i => w + flatHead h d i) 0).PosSemidef ∧
    E w h d ≤ w * (∑ i, flatHead h d i) + (∑ i, (flatHead h d i) ^ 2) := by
  have hg_nonneg : ∀ i, 0 ≤ w + h i := fun i => add_nonneg hw (hn i)
  have hg_order : Antitone (fun i => w + h i) :=
    fun i j hij => by simpa only [add_comm] using add_le_add_left (ho hij) w
  have hflatK := tail_to_head_psd (fun i => w + h i) d
    hg_nonneg hg_order dn dord hK
  have hid : flatHead (fun i => w + h i) d = fun i => w + flatHead h d i := by
    ext i
    fin_cases i <;> simp [flatHead] <;> ring
  rw [hid] at hflatK
  refine ⟨hflatK, ?_⟩
  obtain ⟨hsum, hsum2, _, _⟩ := flatHead_facts h d hn ho dn dord
  obtain ⟨hD2, _, hD⟩ := ordered_tail_bounds d dn dord
  let r := d 6 + d 7 + d 8
  have hr : 0 ≤ r := by dsimp [r]; linarith [dn 6, dn 7, dn 8]
  have hmass_charge := mul_le_mul_of_nonneg_left hD hw
  have hhead_charge := mul_nonneg hr (sub_nonneg.mpr hlarge)
  change (∑ i, (d i) ^ 2) ≤ r ^ 2 at hD2
  change (∑ i, d i) ≤ 3 * r at hD
  change w * (∑ i, d i) ≤ w * (3 * r) at hmass_charge
  change (∑ i, flatHead h d i) = (∑ i, h i) + r at hsum
  change (∑ i, (flatHead h d i) ^ 2) =
    (∑ i, (h i) ^ 2) + 2 * h 0 * r + r ^ 2 at hsum2
  rw [hsum, hsum2]
  dsimp [E, H, D, H2, D2]
  nlinarith only [hD2, hmass_charge, hhead_charge]

/-- Nonflat-tail energy on the original middle interval.  All fourteen
defects remain arbitrary reals with the original ordering, caps, L4 budget,
and literal shifted PSD matrix.  The small-head and upper-interval branches
consume the original StructuralCone estimates. -/
theorem actual_psd_nonflat_middle_energy (w : ℝ) (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (dord : Monotone d) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (hL4 : (∑ i, h i) + (∑ i, d i) ≤ 4 - 6 * w)
    (hw : 1 / 4 ≤ w) (hw1 : w ≤ 1 / 2)
    (hK : (!![2 * (1 - d 8), -(w + h 0 + d 7), -(w + h 1 + d 5);
                -(w + h 0 + d 7), 2 * (1 - d 6), -(w + h 2 + d 4);
                -(w + h 1 + d 5), -(w + h 2 + d 4), 2 * (1 - d 3)] :
      Matrix (Fin 3) (Fin 3) ℝ).PosSemidef) :
    w * ((∑ i, h i) + (∑ i, d i)) + (∑ i, (h i) ^ 2) + (∑ i, (d i) ^ 2) ≤
      if w ≤ (5 - Real.sqrt 17) / 2 then
        4 - 2 * w - 4 * w ^ 2 + w ^ 3 + w ^ 4
      else (4 - 6 * w) * (4 - 5 * w) := by
  change (actualK (fun i => w + h i) d).PosSemidef at hK
  have hw0 : 0 ≤ w := by linarith
  have hdata := shifted_actual_defects w h d ho hn dord hd hL4 hK
  change E w h d ≤ _
  split_ifs with hrho
  · by_cases hsmall : h 0 ≤ 1
    · have he := small_head_energy hdata hw0 hsmall
      have hp : 0 ≤ w ^ 2 * (2 + w + w ^ 2) :=
        mul_nonneg (sq_nonneg _) (by nlinarith only [hw0, sq_nonneg w])
      nlinarith only [he, hp]
    · have hlarge : 1 ≤ h 0 := le_of_lt (lt_of_not_ge hsmall)
      obtain ⟨hflatK, henergy⟩ := shifted_flatHead_energy w h d hw0 hn ho
        (fun i => (hd i).1) dord (by linarith) hK
      obtain ⟨hsum, _, hflat_nonneg, hflat_order⟩ :=
        flatHead_facts h d hn ho (fun i => (hd i).1) dord
      have hrD := (ordered_tail_bounds d (fun i => (hd i).1) dord).2.1
      have hflat_mass : (∑ i, flatHead h d i) ≤ 4 - 6 * w := by
        rw [hsum]
        linarith only [hrD, hL4]
      have hflat_large : 1 ≤ flatHead h d 0 := by
        simp only [flatHead, Matrix.cons_val_zero]
        linarith [hlarge, (hd 6).1, (hd 7).1, (hd 8).1]
      have he := actual_psd_flat_tail_middle_energy w (flatHead h d)
        hflat_order hflat_nonneg hflat_mass hflat_large hw hrho
        (by simpa only [actualK, Pi.zero_apply, sub_zero, mul_one, add_zero] using hflatK)
      exact henergy.trans he
  · simpa only [mul_one] using total_energy_estimate (u := 1) hdata hw0

-- Shift ALL FIVE heads.  Their added 5w mass is paid by 4-6w.
-- This is the live use of the proved 7/2 moment, with no reproof of it.
private theorem shifted_zero_jump_energy (w : ℝ) (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (hw : 0 ≤ w) (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (dord : Monotone d) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (hL4 : H h + D d ≤ 4 - 6 * w)
    (hK : (actualK (fun i => w + h i) d).PosSemidef) :
    E w h d ≤ 7 / 2 + (1 / 4 - w) * (H h - D d) + 5 * w / 4 - 5 * w ^ 2 := by
  have hsum : (∑ i : Fin 5, (w + h i)) = 5 * w + H h := by
    simp [H, Fin.sum_univ_succ] <;> ring
  have hsum2 : (∑ i : Fin 5, (w + h i) ^ 2) = H2 h + 2 * w * H h + 5 * w ^ 2 := by
    simp [H, H2, Fin.sum_univ_succ] <;> ring
  have hmass : (∑ i : Fin 5, (w + h i)) + (∑ i, d i) ≤ 4 := by
    rw [hsum]
    change 5 * w + H h + D d ≤ 4
    linarith only [hL4, hw]
  have hm := actual_psd_zero_jump_moment (fun i => w + h i) d
    (fun i j hij => by simpa only [add_comm] using add_le_add_left (ho hij) w)
    (fun i => add_nonneg hw (hn i)) dord hd hmass
    (by simpa only [actualK] using hK)
  rw [hsum, hsum2] at hm
  change H2 h + 2 * w * H h + 5 * w ^ 2 + D2 d - (5 * w + H h - D d) / 4 ≤ 7 / 2 at hm
  dsimp [E]
  nlinarith only [hm]

/-- The exact small-jump normalized mass/square inequality with the original
natural rounding, for every N ≥ 56.  The sole PSD premise is literal K_w.
The proof consumes the existing 7/2 zero-jump theorem through the five-head
shift, then the original square-completion and rounding suppliers. -/
theorem actual_psd_small_jump_defect_bound (N : ℕ) (hN : 56 ≤ N) (j w : ℝ)
    (hj : 6 ≤ j) (hw : 0 ≤ w) (hw1 : w ≤ 1 / 4)
    (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (ho : Antitone h) (hn : ∀ i, 0 ≤ h i)
    (dord : Monotone d) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (hL4 : (∑ i, h i) + (∑ i, d i) ≤ 4 - 6 * w)
    (hK : (!![2 * (1 - d 8), -(w + h 0 + d 7), -(w + h 1 + d 5);
                -(w + h 0 + d 7), 2 * (1 - d 6), -(w + h 2 + d 4);
                -(w + h 1 + d 5), -(w + h 2 + d 4), 2 * (1 - d 3)] :
      Matrix (Fin 3) (Fin 3) ℝ).PosSemidef) :
    (2 + w) * ((N : ℝ) + w * j + (∑ i, h i) - (∑ i, d i)) - (1 + w) * N +
      (w * ((∑ i, h i) + (∑ i, d i)) + (∑ i, (h i) ^ 2) + (∑ i, (d i) ^ 2)) ≤
      target N * ((N : ℝ) + w * j + (∑ i, h i) - (∑ i, d i)) ^ 2 := by
  change (actualK (fun i => w + h i) d).PosSemidef at hK
  have hm := shifted_zero_jump_energy w h d hw ho hn dord hd hL4 hK
  let S : ℝ := (N : ℝ) + w * j + H h - D d
  let theta : ℝ := commonEnvelope (N : ℝ)
  have hNr : (56 : ℝ) ≤ N := by exact_mod_cast hN
  have hB : 0 < 15 * (N : ℝ) - 4 := by linarith
  have hden : 0 < 80 * (N : ℝ) - 224 := by linarith
  have ht : 0 < theta := by
    dsimp [theta, commonEnvelope]
    exact div_pos (by linarith) (sq_pos_of_pos hB)
  have hlo : 81 / (80 * (N : ℝ) - 224) ≤ theta := by
    dsimp [theta, commonEnvelope]
    apply (div_le_div_iff₀ hden (sq_pos_of_pos hB)).2
    apply sub_nonneg.mp
    have hshift : 0 ≤ (N : ℝ) - 56 := by linarith
    calc
      _ = 975 * ((N : ℝ) - 56) ^ 2 + 54920 * ((N : ℝ) - 56) + 45296 := by ring
      _ ≥ 0 := by positivity
  have hdisc : (9 / 4 : ℝ) ^ 2 ≤ 4 * theta * (5 * (N : ℝ) / 4 - 7 / 2) := by
    have hh := (div_le_iff₀ hden).mp hlo
    nlinarith only [hh]
  have hp : 0 ≤ w * (1 / 4 - w) := mul_nonneg hw (by linarith)
  have hjp := mul_nonneg hp (sub_nonneg.mpr hj)
  have hcoarse : (2 + w) * S - (1 + w) * (N : ℝ) + E w h d ≤
      (9 / 4) * S - (5 * (N : ℝ) / 4 - 7 / 2) := by
    dsimp [S]
    nlinarith only [hm, hp, hjp]
  have hs := square_completion theta (9 / 4) (5 * (N : ℝ) / 4 - 7 / 2) S ht hdisc
  have hcommon : theta ≤ target N := by
    simpa only [theta, target, bulkValue, bulkIndex] using
      common_le_integer_bulk N hN
  have hfinal := hcoarse.trans (hs.trans
    (mul_le_mul_of_nonneg_right hcommon (sq_nonneg S)))
  change (2 + w) * S - (1 + w) * (N : ℝ) + E w h d ≤ target N * S ^ 2
  exact hfinal

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
