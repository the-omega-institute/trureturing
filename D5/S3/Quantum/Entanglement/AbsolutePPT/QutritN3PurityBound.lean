/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN3PurityBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QutritN3PurityBound
   mirror-E: none(waiver:kernel-checked-rational-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN3PurityBound.purity_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN3PurityBound.N
   digest: Literal qutrit APPT density matrices satisfy the sharp purity bound for n = 3. -/

/-
proof_shape: purity_bound: content
escape_witness: QutritSpectralReduction.spectral_reduction supplies ordered
  nonnegative mass-one coordinates, both boundary LMIs and the trace-square
  identity from the literal APPT density matrix on the live proof path.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.partialTranspose
  statement_id: sha256:2373e14505428583f492752adc05d104ae8b1567265ff8182e03646de824c089
  D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef
  statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
Information-escape registration is paused under CLAUDE.md section 3.9.

certificate_bound; proof_shape: bind-only; escape_witness: none; consumer: purity_bound
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
import D5.S3.Weil.ZetaLinear.RankTrace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 32768
open Matrix
open scoped ComplexOrder
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN3PurityBound

private def N : Matrix (Fin 9) (Fin 9) ℝ := !![0, 9, 34, 70, 101, 57, 72, 19, 0; 9, 2, 68, 88, 101, 66, 63, 40, 1; 34, 68, 30, 69, 92, 59, 64, 52, 11; 70, 88, 69, 20, 67, 51, 62, 46, 10; 101, 101, 92, 67, 24, 43, 66, 51, 13; 57, 66, 59, 51, 43, 16, 41, 51, 9; 72, 63, 64, 62, 66, 41, 20, 55, 14; 19, 40, 52, 46, 51, 51, 55, 22, 15; 0, 1, 11, 10, 13, 9, 14, 15, 0]

private theorem certificate_bound (l : Fin 9 → ℝ) (horder : Antitone l)
    (hnonneg : 0 ≤ l 8) (htrace : ∑ i, l i=1)
    (h1 : (QutritSpectralReduction.K1 (QutritSpectralReduction.boundaryValues 0 l)).PosSemidef) (h2 : (QutritSpectralReduction.K2 (QutritSpectralReduction.boundaryValues 0 l)).PosSemidef) :
    ∑ i, (l i)^2 ≤ 17/121  := by
  let K1 (l : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
    !![2*l 8, l 7-l 0, l 5-l 1; l 7-l 0, 2*l 6, l 4-l 2; l 5-l 1, l 4-l 2, 2*l 3]
  let K2 (l : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
    !![2*l 8, l 7-l 0, l 6-l 1; l 7-l 0, 2*l 5, l 4-l 2; l 6-l 1, l 4-l 2, 2*l 3]
  let gap (l : Fin 9 → ℝ) : Fin 9 → ℝ :=
    ![l 0-l 1, l 1-l 2, l 2-l 3, l 3-l 4, l 4-l 5, l 5-l 6, l 6-l 7, l 7-l 8, l 8]
  let A1_1 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; 0, 0, 0]
  let A1_2 : Matrix (Fin 3) (Fin 3) ℝ := !![38, 26, 26; 26, 20, 18; 26, 18, 20]
  have A1_2_psd : A1_2.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 13/19, 1, 0; 13/19, 2/21, 1]
    let D : Fin 3 → ℝ := ![38, 42/19, 46/21]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A1_2, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A1_3 : Matrix (Fin 3) (Fin 3) ℝ := !![36, 27, 18; 27, 28, 16; 18, 16, 16]
  have A1_3_psd : A1_3.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 3/4, 1, 0; 1/2, 10/31, 1]
    let D : Fin 3 → ℝ := ![36, 31/4, 192/31]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A1_3, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A1_4 : Matrix (Fin 3) (Fin 3) ℝ := !![52, 40, 21; 40, 39, 17; 21, 17, 13]
  have A1_4_psd : A1_4.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 10/13, 1, 0; 21/52, 11/107, 1]
    let D : Fin 3 → ℝ := ![52, 107/13, 1897/428]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A1_4, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A1_5 : Matrix (Fin 3) (Fin 3) ℝ := !![73, 52, 19; 52, 46, 14; 19, 14, 9]
  have A1_5_psd : A1_5.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 52/73, 1, 0; 19/73, 17/327, 1]
    let D : Fin 3 → ℝ := ![73, 654/73, 1318/327]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A1_5, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A1_6 : Matrix (Fin 3) (Fin 3) ℝ := !![81, 66, 9; 66, 60, 7; 9, 7, 4]
  have A1_6_psd : A1_6.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 22/27, 1, 0; 1/9, -3/56, 1]
    let D : Fin 3 → ℝ := ![81, 56/9, 167/56]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A1_6, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A1_7 : Matrix (Fin 3) (Fin 3) ℝ := !![89, 45, 9; 45, 28, 5; 9, 5, 5]
  have A1_7_psd : A1_7.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 45/89, 1, 0; 9/89, 40/467, 1]
    let D : Fin 3 → ℝ := ![89, 467/89, 1892/467]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A1_7, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A1_8 : Matrix (Fin 3) (Fin 3) ℝ := !![60, 29, 11; 29, 19, 6; 11, 6, 6]
  have A1_8_psd : A1_8.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 29/60, 1, 0; 11/60, 41/299, 1]
    let D : Fin 3 → ℝ := ![60, 299/60, 1163/299]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A1_8, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A1_9 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; 0, 0, 0]
  let A2_1 : Matrix (Fin 3) (Fin 3) ℝ := !![52, 52, 0; 52, 52, 0; 0, 0, 0]
  have A2_1_psd : A2_1.PosSemidef := by
    have h := (Matrix.posSemidef_vecMulVec_self_star (![1,1,0] : Fin 3 → ℝ)).smul (show (0 : ℝ) ≤ 52 by norm_num)
    convert h using 1 <;> ext j k <;> fin_cases j <;> fin_cases k <;> norm_num [A2_1, vecMulVec]
  let A2_2 : Matrix (Fin 3) (Fin 3) ℝ := !![27, 18, 18; 18, 15, 13; 18, 13, 15]
  have A2_2_psd : A2_2.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 2/3, 1, 0; 2/3, 1/3, 1]
    let D : Fin 3 → ℝ := ![27, 3, 8/3]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A2_2, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A2_3 : Matrix (Fin 3) (Fin 3) ℝ := !![36, 25, 19; 25, 24, 15; 19, 15, 17]
  have A2_3_psd : A2_3.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 25/36, 1, 0; 19/36, 65/239, 1]
    let D : Fin 3 → ℝ := ![36, 239/36, 1549/239]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A2_3, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A2_4 : Matrix (Fin 3) (Fin 3) ℝ := !![45, 31, 18; 31, 29, 14; 18, 14, 12]
  have A2_4_psd : A2_4.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 31/45, 1, 0; 2/5, 9/43, 1]
    let D : Fin 3 → ℝ := ![45, 344/45, 192/43]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A2_4, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A2_5 : Matrix (Fin 3) (Fin 3) ℝ := !![55, 33, 16; 33, 27, 10; 16, 10, 9]
  have A2_5_psd : A2_5.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 3/5, 1, 0; 16/55, 1/18, 1]
    let D : Fin 3 → ℝ := ![55, 36/5, 428/99]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A2_5, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A2_6 : Matrix (Fin 3) (Fin 3) ℝ := !![24, 10, 7; 10, 8, 3; 7, 3, 6]
  have A2_6_psd : A2_6.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 5/12, 1, 0; 7/24, 1/46, 1]
    let D : Fin 3 → ℝ := ![24, 23/6, 91/23]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A2_6, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A2_7 : Matrix (Fin 3) (Fin 3) ℝ := !![64, 29, 10; 29, 18, 5; 10, 5, 6]
  have A2_7_psd : A2_7.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 29/64, 1, 0; 5/32, 30/311, 1]
    let D : Fin 3 → ℝ := ![64, 311/64, 1366/311]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A2_7, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A2_8 : Matrix (Fin 3) (Fin 3) ℝ := !![60, 27, 13; 27, 17, 6; 13, 6, 7]
  have A2_8_psd : A2_8.PosSemidef := by
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 9/20, 1, 0; 13/60, 3/97, 1]
    let D : Fin 3 → ℝ := ![60, 97/20, 1216/291]
    have hp : (diagonal D).PosSemidef := Matrix.PosSemidef.diagonal (by intro j; fin_cases j <;> norm_num [D])
    convert hp.mul_mul_conjTranspose_same L using 1
    ext j k
    fin_cases j <;> fin_cases k <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, A2_8, L, D, diagonal, Matrix.of_apply, Fin.reduceEq, Fin.reduceFinMk, Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  let A2_9 : Matrix (Fin 3) (Fin 3) ℝ := !![72, 72, 0; 72, 72, 0; 0, 0, 0]
  have A2_9_psd : A2_9.PosSemidef := by
    have h := (Matrix.posSemidef_vecMulVec_self_star (![1,1,0] : Fin 3 → ℝ)).smul (show (0 : ℝ) ≤ 72 by norm_num)
    convert h using 1 <;> ext j k <;> fin_cases j <;> fin_cases k <;> norm_num [A2_9, vecMulVec]
  have N_nonnegative (i j : Fin 9) : 0 ≤ N i j := by
    fin_cases i <;> fin_cases j <;> norm_num [N]
  have certificate_identity (l : Fin 9 → ℝ) :
      17 * (∑ i, l i)^2 - 121 * (∑ i, (l i)^2) =
      (∑ i, ∑ j, N i j * gap l i * gap l j) +
        gap l 1 * (A1_2 * K1 l).trace +
        gap l 2 * (A1_3 * K1 l).trace +
        gap l 3 * (A1_4 * K1 l).trace +
        gap l 4 * (A1_5 * K1 l).trace +
        gap l 5 * (A1_6 * K1 l).trace +
        gap l 6 * (A1_7 * K1 l).trace +
        gap l 7 * (A1_8 * K1 l).trace +
        gap l 0 * (A2_1 * K2 l).trace +
        gap l 1 * (A2_2 * K2 l).trace +
        gap l 2 * (A2_3 * K2 l).trace +
        gap l 3 * (A2_4 * K2 l).trace +
        gap l 4 * (A2_5 * K2 l).trace +
        gap l 5 * (A2_6 * K2 l).trace +
        gap l 6 * (A2_7 * K2 l).trace +
        gap l 7 * (A2_8 * K2 l).trace +
        gap l 8 * (A2_9 * K2 l).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]
    simp [N, gap, A1_1, A1_2, A1_3, A1_4, A1_5, A1_6, A1_7, A1_8, A1_9, A2_1, A2_2, A2_3, A2_4, A2_5, A2_6, A2_7, A2_8, A2_9, K1, K2, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  have h1 : (K1 l).PosSemidef := by
    simpa [K1, QutritSpectralReduction.K1, QutritSpectralReduction.boundaryValues] using h1
  have h2 : (K2 l).PosSemidef := by
    simpa [K2, QutritSpectralReduction.K2, QutritSpectralReduction.boundaryValues] using h2
  have hy (i : Fin 9) : 0 ≤ gap l i := by
    fin_cases i <;> simp only [gap, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
    all_goals first | exact hnonneg | exact sub_nonneg.mpr (horder (by decide))
  have hN : 0 ≤ ∑ i, ∑ j, N i j * gap l i * gap l j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (N_nonnegative i j) (hy i)) (hy j)
  have ht1_2 : 0 ≤ gap l 1 * (A1_2 * K1 l).trace :=
    mul_nonneg (hy 1) (RHLinalg.trace_mul_nonneg_of_posSemidef A1_2_psd h1)
  have ht1_3 : 0 ≤ gap l 2 * (A1_3 * K1 l).trace :=
    mul_nonneg (hy 2) (RHLinalg.trace_mul_nonneg_of_posSemidef A1_3_psd h1)
  have ht1_4 : 0 ≤ gap l 3 * (A1_4 * K1 l).trace :=
    mul_nonneg (hy 3) (RHLinalg.trace_mul_nonneg_of_posSemidef A1_4_psd h1)
  have ht1_5 : 0 ≤ gap l 4 * (A1_5 * K1 l).trace :=
    mul_nonneg (hy 4) (RHLinalg.trace_mul_nonneg_of_posSemidef A1_5_psd h1)
  have ht1_6 : 0 ≤ gap l 5 * (A1_6 * K1 l).trace :=
    mul_nonneg (hy 5) (RHLinalg.trace_mul_nonneg_of_posSemidef A1_6_psd h1)
  have ht1_7 : 0 ≤ gap l 6 * (A1_7 * K1 l).trace :=
    mul_nonneg (hy 6) (RHLinalg.trace_mul_nonneg_of_posSemidef A1_7_psd h1)
  have ht1_8 : 0 ≤ gap l 7 * (A1_8 * K1 l).trace :=
    mul_nonneg (hy 7) (RHLinalg.trace_mul_nonneg_of_posSemidef A1_8_psd h1)
  have ht2_1 : 0 ≤ gap l 0 * (A2_1 * K2 l).trace :=
    mul_nonneg (hy 0) (RHLinalg.trace_mul_nonneg_of_posSemidef A2_1_psd h2)
  have ht2_2 : 0 ≤ gap l 1 * (A2_2 * K2 l).trace :=
    mul_nonneg (hy 1) (RHLinalg.trace_mul_nonneg_of_posSemidef A2_2_psd h2)
  have ht2_3 : 0 ≤ gap l 2 * (A2_3 * K2 l).trace :=
    mul_nonneg (hy 2) (RHLinalg.trace_mul_nonneg_of_posSemidef A2_3_psd h2)
  have ht2_4 : 0 ≤ gap l 3 * (A2_4 * K2 l).trace :=
    mul_nonneg (hy 3) (RHLinalg.trace_mul_nonneg_of_posSemidef A2_4_psd h2)
  have ht2_5 : 0 ≤ gap l 4 * (A2_5 * K2 l).trace :=
    mul_nonneg (hy 4) (RHLinalg.trace_mul_nonneg_of_posSemidef A2_5_psd h2)
  have ht2_6 : 0 ≤ gap l 5 * (A2_6 * K2 l).trace :=
    mul_nonneg (hy 5) (RHLinalg.trace_mul_nonneg_of_posSemidef A2_6_psd h2)
  have ht2_7 : 0 ≤ gap l 6 * (A2_7 * K2 l).trace :=
    mul_nonneg (hy 6) (RHLinalg.trace_mul_nonneg_of_posSemidef A2_7_psd h2)
  have ht2_8 : 0 ≤ gap l 7 * (A2_8 * K2 l).trace :=
    mul_nonneg (hy 7) (RHLinalg.trace_mul_nonneg_of_posSemidef A2_8_psd h2)
  have ht2_9 : 0 ≤ gap l 8 * (A2_9 * K2 l).trace :=
    mul_nonneg (hy 8) (RHLinalg.trace_mul_nonneg_of_posSemidef A2_9_psd h2)
  have heq := certificate_identity l
  rw [htrace] at heq
  norm_num only [one_pow, mul_one] at heq
  linarith only [heq, hN, ht1_2, ht1_3, ht1_4, ht1_5, ht1_6, ht1_7, ht1_8, ht2_1, ht2_2, ht2_3, ht2_4, ht2_5, ht2_6, ht2_7, ht2_8, ht2_9]

theorem purity_bound
    (rho : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1)
    (happt : QutritPerturbationAttainment.APPT rho) :
    (rho*rho).trace.re ≤ 17/121 := by
  obtain ⟨l, ho, hn, ht, h1, h2, hp⟩ :=
    QutritSpectralReduction.spectral_reduction 0 rho hrho htrace happt
  rw [hp]
  exact certificate_bound l ho (hn 8) ht h1 h2

#print axioms purity_bound
end D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN3PurityBound
