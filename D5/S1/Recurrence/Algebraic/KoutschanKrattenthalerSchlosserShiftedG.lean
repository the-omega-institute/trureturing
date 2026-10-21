/- GID: D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prove the Koutschan-Krattenthaler-Schlosser determinant identities. -/

/- Formalization classification:
   proof_shape: binom: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.G
   proof_shape: G: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.claim
   proof_shape: claim: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.result
   proof_shape: invLin: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.coeff_invLin
   proof_shape: coeff_invLin: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.constantCoeff_invLin
   proof_shape: constantCoeff_invLin: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.source_head
   proof_shape: coeff_scaled_shift: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.coeff_shift_invLin
   proof_shape: coeff_shift_invLin: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.columns_regular
   proof_shape: choose_reflect: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.columns_regular
   proof_shape: D: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.h
   proof_shape: h: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.hD
   proof_shape: hD: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.difference
   proof_shape: h_constant: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.source_head
   proof_shape: lin_pow_invLin: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.difference
   proof_shape: difference: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.difference_shifted
   proof_shape: difference_shifted: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.shifted_difference
   proof_shape: smat: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.toeplitz_mul
   proof_shape: toeplitz: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.toeplitz_mul
   proof_shape: diff: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.det_diff
   proof_shape: toeplitz_mul: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.det_smat_mul
   proof_shape: det_toeplitz: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.det_smat_mul
   proof_shape: det_smat_mul: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.shiftedG_all
   proof_shape: det_diff: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.shiftedG_all
   proof_shape: det_first_row: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.det_shift
   proof_shape: det_shift: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.shiftedG_all
   proof_shape: det_blocks: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.shared_columns
   proof_shape: shared_columns: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.det_comparison
   proof_shape: entry: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.columns
   proof_shape: columns: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.G_eq_smat
   proof_shape: G_eq_smat: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.shiftedG_all
   proof_shape: regular: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.columns_regular
   proof_shape: columns_regular: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.source_gf
   proof_shape: source_gf: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.shifted_difference
   proof_shape: target_gf: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.shifted_difference
   proof_shape: shifted_difference: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.shiftedG_all
   proof_shape: source_head: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.shiftedG_all
   proof_shape: shiftedG_all: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.result
   proof_shape: result: bind-only; consumer: none (settling result)
   proof_shape: gf_T: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.p_shifted_difference
   proof_shape: gf_B: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans_B
   proof_shape: gf_C: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans_B
   proof_shape: gf_D: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans2_P
   proof_shape: gf_E: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans3_P
   proof_shape: gf_F: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans_T
   proof_shape: gf_H: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans_H
   proof_shape: gf_I: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans_H
   proof_shape: gf_V: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans_V
   proof_shape: gf_J: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans_V
   proof_shape: gf_K: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans2_V
   proof_shape: gf_Q: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.prop_B
   proof_shape: p_gf: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.p_shifted_difference
   proof_shape: p_shifted_difference: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans2_P
   proof_shape: trans: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.det_trans
   proof_shape: det_trans: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.det_transN
   proof_shape: det_transN: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.det_comparison
   proof_shape: trans_succ: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans_T
   proof_shape: trans_T: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans2_P
   proof_shape: trans_V: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans2_V
   proof_shape: trans_H: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.link_HI
   proof_shape: trans_B: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.link_BC
   proof_shape: trans2_V: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.link_VK
   proof_shape: trans2_P: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.trans3_P
   proof_shape: trans3_P: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.link_PE
   proof_shape: det_comparison: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.link_BC
   proof_shape: columns_vanish: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.link_BC
   proof_shape: link_BC: bind-only; consumer: KoutschanKrattenthalerSchlosserTenTen.result
   proof_shape: link_PD: bind-only; consumer: KoutschanKrattenthalerSchlosserTenTen.result
   proof_shape: link_PE: bind-only; consumer: KoutschanKrattenthalerSchlosserTenTen.result
   proof_shape: link_TF: bind-only; consumer: KoutschanKrattenthalerSchlosserTenTen.result
   proof_shape: link_HI: bind-only; consumer: KoutschanKrattenthalerSchlosserTenEleven.result
   proof_shape: link_VJ: bind-only; consumer: KoutschanKrattenthalerSchlosserTenEleven.result
   proof_shape: link_VK: bind-only; consumer: KoutschanKrattenthalerSchlosserTenEleven.result
   proof_shape: entry_shift: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.columns_shift
   proof_shape: columns_shift: bind-only; consumer: KoutschanKrattenthalerSchlosserShiftedG.prop_H
   proof_shape: prop_H: bind-only; consumer: KoutschanKrattenthalerSchlosserTenEleven.result
   proof_shape: prop_B: bind-only; consumer: KoutschanKrattenthalerSchlosserTenTen.result
   proof_shape: p_shift_all: bind-only; consumer: KoutschanKrattenthalerSchlosserTenTen.result
   escape_witness: none
   admission_basis: open-problem-resolution (#19228; Proved)
   Direct frozen dependencies: none (pinned Mathlib only).
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19547
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.NormNum.NatFactorial

open PowerSeries Matrix

namespace D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserShiftedG

set_option maxHeartbeats 800000

/-- The binomial coefficient (1.2): `α(α−1)⋯(α−p+1)/p!` for `p ≥ 0` and `0` for `p < 0`. -/
noncomputable def binom (x : ℚ) (p : ℤ) : ℚ :=
  if p < 0 then 0 else Ring.choose x p.toNat

/-- `G_{α,β,γ,δ}(n) = det_{0≤i,j≤n−1} (2^{i+β} binom(i+4j+γ, 4j+α) + binom(−i+4j+δ, 4j+α))`. -/
noncomputable def G (α β γ δ : ℤ) (n : ℕ) : ℚ :=
  (Matrix.of fun i j : Fin n =>
    (2 : ℚ) ^ ((i : ℤ) + β) * binom ((i : ℚ) + 4 * (j : ℚ) + γ) (4 * (j : ℤ) + α)
      + binom (-(i : ℚ) + 4 * (j : ℚ) + δ) (4 * (j : ℤ) + α)).det

/-- Equation (10.12): `G_{2,1,2,0}(n) = 2 G_{7,4,7,−1}(n−1)` for all `n ≥ 3`. -/
def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n → G 2 1 2 0 n = 2 * G 7 4 7 (-1) (n - 1)

private noncomputable def invLin (a : ℚ) (d : ℕ) : PowerSeries ℚ :=
  rescale a (invOneSubPow ℚ d).val

private lemma coeff_invLin (a : ℚ) (d i : ℕ) :
    coeff i (invLin a (d+1)) = a^i * (Nat.choose (d+i) d : ℚ) := by
  simp [invLin, coeff_rescale, invOneSubPow_val_succ_eq_mk_add_choose]

private lemma constantCoeff_invLin (a : ℚ) (d : ℕ) : constantCoeff (invLin a d) = 1 := by
  cases d with
  | zero => simp [invLin, invOneSubPow_zero]
  | succ d =>
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_invLin]
    simp

private lemma coeff_scaled_shift (a : ℚ) (ha : a ≠ 0) (b : ℤ) (r k i : ℕ) (hk : k ≤ r) :
    coeff i (C (a^(b+(k:ℤ))) * X^k * invLin a (r+1)) =
      a^((i:ℤ)+b) * (Nat.choose (r+i-k) r : ℚ) := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with hi
  · rw [coeff_invLin]
    have he : r+(i-k)=r+i-k := by exact Eq.symm (Nat.add_sub_assoc hi r)
    rw [he, ← mul_assoc, ← zpow_natCast a (i-k), ← zpow_add₀ ha]
    congr 2
    omega
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

private lemma coeff_shift_invLin (r k i : ℕ) (hk : k ≤ r) :
    coeff i (X^k * invLin 1 (r+1)) = (Nat.choose (r+i-k) r : ℚ)  := by
  simpa only [one_zpow, map_one, one_mul] using coeff_scaled_shift 1 (by norm_num) 0 r k i hk

private lemma choose_reflect (x : ℚ) (r : ℕ) :
    Ring.choose x r = (-1 : ℚ)^r * Ring.choose ((r : ℚ)-x-1) r := by
  have h := Ring.choose_neg (-x) r
  simpa only [neg_neg, Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast,
    show (-x + (r : ℚ) - 1) = (r : ℚ)-x-1 by ring] using h

private noncomputable def D : PowerSeries ℚ := (1-X)*(1-C 2*X)*(1-C 2*X+C 2*X^2)
private noncomputable def h : PowerSeries ℚ := invOfUnit D 1

private lemma hD : h * D = 1 := by
  exact invOfUnit_mul D 1 (by simp [D])
private lemma h_constant : constantCoeff h = 1 := by simp [h]

private lemma lin_pow_invLin (a : ℚ) (d e : ℕ) :
    (1-C a*X)^e * invLin a (d+e) = invLin a d := by
  have hi := congrArg (rescale a)
    (one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ d e)
  simpa [invLin, rescale_X] using hi

private lemma difference (a b : ℚ) (r s q : ℕ) :
    h * ((C a * X^s * invLin 2 (r+5) + C b * X^(q+4) * invLin 1 (r+5)) -
      (C a * X^s * invLin 2 (r+1) + C b * X^q * invLin 1 (r+1))) =
    C (8*a) * X^(s+1) * invLin 2 (r+6) - C b * X^q * invLin 1 (r+6) := by
  have hm : D * (C (8*a) * X^(s+1) * invLin 2 (r+6) - C b * X^q * invLin 1 (r+6)) =
      (C a * X^s * invLin 2 (r+5) + C b * X^(q+4) * invLin 1 (r+5)) -
      (C a * X^s * invLin 2 (r+1) + C b * X^q * invLin 1 (r+1)) := by
    have ha1 := lin_pow_invLin 2 (r+5) 1
    have ha5 := lin_pow_invLin 2 (r+1) 5
    have hb1 := lin_pow_invLin 1 (r+5) 1
    have hb5 := lin_pow_invLin 1 (r+1) 5
    norm_num only [Nat.add_assoc, pow_one, map_one, one_mul] at ha1 ha5 hb1 hb5
    rw [← ha1, ← ha5, ← hb1, ← hb5]
    simp only [D, map_mul, map_ofNat, pow_add, pow_one]
    ring
  rw [← hm, ← mul_assoc, hD, one_mul]

private lemma difference_shifted (j : ℕ) :
    h * ((C 2 * invLin 2 (4*(j+1)+3) + X^(4*(j+1)+1) * invLin 1 (4*(j+1)+3)) -
      (C 2 * invLin 2 (4*j+3) + X^(4*j+1) * invLin 1 (4*j+3))) =
    X * (C 16 * invLin 2 (4*j+8) - X^(4*j) * invLin 1 (4*j+8)) := by
  have hd := difference 2 1 (4*j+2) 0 (4*j+1)
  norm_num only [map_one, map_ofNat, pow_zero, mul_one, Nat.reduceAdd] at hd
  convert hd using 1 <;> norm_num only [map_ofNat] <;> ring_nf

private noncomputable def smat (f : ℕ → PowerSeries ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => coeff i.val (f j.val)
private noncomputable def toeplitz (w : PowerSeries ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if j.val ≤ i.val then coeff (i.val-j.val) w else 0
private noncomputable def diff (f : ℕ → PowerSeries ℚ) (j : ℕ) : PowerSeries ℚ :=
  if j=0 then f 0 else f j - f (j-1)

private lemma toeplitz_mul (w : PowerSeries ℚ) (f : ℕ → PowerSeries ℚ) (n : ℕ) :
    toeplitz w n * smat f n = smat (fun j => w * f j) n := by
  ext i j
  simp only [Matrix.mul_apply, toeplitz, smat, ite_mul, zero_mul]
  rw [Fin.sum_univ_eq_sum_range
    (fun r : ℕ => if r ≤ i.val then coeff (i.val-r) w * coeff r (f j.val) else 0) n]
  rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    (∑ r ∈ Finset.range n,
      if r ≤ i.val then coeff (i.val-r) w * coeff r (f j.val) else 0) =
      ∑ r ∈ Finset.range (i.val+1),
        if r ≤ i.val then coeff (i.val-r) w * coeff r (f j.val) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro r _ hr
      simp only [Finset.mem_range, not_lt] at hr
      simp [show ¬ r ≤ i.val by omega]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_range] at hr
      simp [show r ≤ i.val by omega]

private lemma det_toeplitz (w : PowerSeries ℚ) (hw : constantCoeff w = 1) (n : ℕ) :
    (toeplitz w n).det = 1 := by
  have hl : (toeplitz w n).IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    simp [toeplitz, show ¬j.val ≤ i.val by omega]
  rw [Matrix.det_of_isLowerTriangular _ hl]
  simp [toeplitz, coeff_zero_eq_constantCoeff_apply, hw]

private lemma det_smat_mul (w : PowerSeries ℚ) (hw : constantCoeff w = 1)
    (f : ℕ → PowerSeries ℚ) (n : ℕ) :
    (smat (fun j => w*f j) n).det = (smat f n).det := by
  rw [← toeplitz_mul, Matrix.det_mul, det_toeplitz _ hw, one_mul]

private lemma det_diff (f : ℕ → PowerSeries ℚ) (n : ℕ) :
    (smat (diff f) n).det = (smat f n).det := by
  cases n with
  | zero => simp
  | succ n =>
    symm
    apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (fun _ => (1 : ℚ))
    · intro i
      simp [smat, diff]
    · intro i j
      simp only [smat, Fin.val_succ, Fin.val_castSucc, diff,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
        map_sub, one_mul]
      ring

private lemma det_first_row {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hz : ∀ j : Fin n, A 0 j.succ = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [hz]

private lemma det_shift (f g : ℕ → PowerSeries ℚ) (a : ℚ)
    (hzero : coeff 0 (f 0) = a)
    (hcols : ∀ j, f (j+1) = X*g j) (n : ℕ) :
    (smat f (n+1)).det = a * (smat g n).det := by
  rw [det_first_row]
  · rw [show smat f (n+1) 0 0 = a from hzero]
    congr 1
    congr 1
    ext i j
    simp only [smat, Matrix.submatrix_apply, Fin.val_succ, hcols]
    simp
  · intro j
    simp [smat, hcols]

private lemma det_blocks {m n : ℕ} (A : Matrix (Fin (m+n)) (Fin (m+n)) ℚ)
    (hz : ∀ i : Fin m, ∀ j : Fin n, A (i.castAdd n) (j.natAdd m) = 0) :
    A.det = (A.submatrix (Fin.castAdd n) (Fin.castAdd n)).det *
      (A.submatrix (Fin.natAdd m) (Fin.natAdd m)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv A]
  have heq : A.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks
      (A.submatrix (Fin.castAdd n) (Fin.castAdd n)) 0
      (A.submatrix (Fin.natAdd m) (Fin.castAdd n))
      (A.submatrix (Fin.natAdd m) (Fin.natAdd m)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.submatrix, hz]
  rw [heq, Matrix.det_fromBlocks_zero₁₂]

private lemma shared_columns {m n : ℕ} (A B : Matrix (Fin (m+n)) (Fin (m+n)) ℚ)
    (hzA : ∀ i : Fin m, ∀ j : Fin n, A (i.castAdd n) (j.natAdd m) = 0)
    (hc : ∀ i : Fin (m+n), ∀ j : Fin n, A i (j.natAdd m) = B i (j.natAdd m)) :
    (B.submatrix (Fin.castAdd n) (Fin.castAdd n)).det * A.det =
      (A.submatrix (Fin.castAdd n) (Fin.castAdd n)).det * B.det := by
  have hzB : ∀ i : Fin m, ∀ j : Fin n, B (i.castAdd n) (j.natAdd m) = 0 := by
    intro i j
    rw [← hc, hzA]
  rw [det_blocks A hzA, det_blocks B hzB]
  have heq : A.submatrix (Fin.natAdd m) (Fin.natAdd m) =
      B.submatrix (Fin.natAdd m) (Fin.natAdd m) := by exact Matrix.ext fun i => hc (Fin.natAdd m i)
  rw [heq]
  ring

private noncomputable def entry (a b c d : ℤ) (i j : ℕ) : ℚ :=
  (2 : ℚ)^((i:ℤ)+b) * binom ((i:ℚ)+4*(j:ℚ)+c) (4*(j:ℤ)+a) +
    binom (-(i:ℚ)+4*(j:ℚ)+d) (4*(j:ℤ)+a)
private noncomputable def columns (a b c d : ℤ) (j : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun i => entry a b c d i j)

private lemma G_eq_smat (a b c d : ℤ) (n : ℕ) : G a b c d n = (smat (columns a b c d) n).det := by
  unfold G
  congr 1
  ext i j
  simp [smat, columns, entry]

private noncomputable def regular (a b g d : ℤ) (j : ℕ) : PowerSeries ℚ :=
  C ((2:ℚ)^(b+a-g)) * X^((a-g).toNat) * invLin 2 ((4*(j:ℤ)+a+1).toNat) +
  C ((-1:ℚ)^a) * X^((4*(j:ℤ)+d+1).toNat) * invLin 1 ((4*(j:ℤ)+a+1).toNat)

private lemma columns_regular (a b g d : ℤ) (j : ℕ)
    (hr : 0 ≤ 4*(j:ℤ)+a) (hc : 0 ≤ 4*(j:ℤ)+g)
    (hs : 0 ≤ a-g) (hq : 0 ≤ 4*(j:ℤ)+d+1) (hc' : 0 ≤ a-d-1) :
    columns a b g d j = regular a b g d j := by
  let r := (4*(j:ℤ)+a).toNat
  let s := (a-g).toNat
  let q := (4*(j:ℤ)+d+1).toNat
  have hr' : (r:ℤ) = 4*(j:ℤ)+a := Int.toNat_of_nonneg hr
  have hs' : (s:ℤ) = a-g := Int.toNat_of_nonneg hs
  have hq' : (q:ℤ) = 4*(j:ℤ)+d+1 := Int.toNat_of_nonneg hq
  have hs_le : s ≤ r := by omega
  have hq_le : q ≤ r := by omega
  have hd : (4*(j:ℤ)+a+1).toNat = r+1 := by exact Int.toNat_add_nat hr 1
  ext i
  simp only [columns, coeff_mk, entry, binom, regular, map_add]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  change (2:ℚ)^((i:ℤ)+b) * Ring.choose ((i:ℚ)+4*(j:ℚ)+g) r +
    Ring.choose (-(i:ℚ)+4*(j:ℚ)+d) r = _
  rw [hd]
  have hb : b+a-g = b+(s:ℤ) := by omega
  rw [hb, coeff_scaled_shift 2 (by norm_num) b r s i hs_le]
  rw [mul_assoc (C _) (X^q), coeff_C_mul,
    coeff_shift_invLin r q i hq_le]
  have hn1 : (i:ℚ)+4*(j:ℚ)+g = ((r+i-s:ℕ):ℚ) := by
    have hl : s ≤ r+i := by exact Nat.le_add_right_of_le hs_le
    rw [Nat.cast_sub hl]
    have he1 : (r:ℚ) = 4*(j:ℚ)+(a:ℚ) := by exact_mod_cast hr'
    have he2 : (s:ℚ) = (a:ℚ)-(g:ℚ) := by exact_mod_cast hs'
    push_cast
    rw [he1, he2]
    ring
  have hn2 : ((r:ℚ)- (-(i:ℚ)+4*(j:ℚ)+d)-1) = ((r+i-q:ℕ):ℚ) := by
    have hl : q ≤ r+i := by exact Nat.le_add_right_of_le hq_le
    rw [Nat.cast_sub hl]
    have he1 : (r:ℚ) = 4*(j:ℚ)+(a:ℚ) := by exact_mod_cast hr'
    have he2 : (q:ℚ) = 4*(j:ℚ)+(d:ℚ)+1 := by exact_mod_cast hq'
    push_cast
    rw [he1, he2]
    ring
  rw [hn1, Ring.choose_natCast, choose_reflect, hn2, Ring.choose_natCast]
  have he : (-1:ℚ)^r = (-1:ℚ)^a := by
    rw [← zpow_natCast, hr', zpow_add₀ (by norm_num)]
    have h4 : (-1:ℚ)^(4*(j:ℤ)) = 1 := by
      rw [_root_.zpow_mul]
      norm_num
    rw [h4, one_mul]
  rw [he]

private lemma source_gf (j : ℕ) : columns 2 1 2 0 j =
    C 2 * invLin 2 (4*j+3) + X^(4*j+1) * invLin 1 (4*j+3)  := by
  rw [columns_regular 2 1 2 0 j (by omega) (by omega) (by omega) (by omega) (by omega)]
  simp only [regular]
  have hd : (4*(j:ℤ)+2+1).toNat = 4*j+3 := by exact Eq.symm (Nat.add_succ (4 * j) 2)
  have hq : (4*(j:ℤ)+0+1).toNat = 4*j+1 := by exact Eq.symm (Nat.add_succ (4 * j) 0)
  rw [hd, hq]
  norm_num

private lemma target_gf (j : ℕ) : columns 7 4 7 (-1) j =
    C 16 * invLin 2 (4*j+8) - X^(4*j) * invLin 1 (4*j+8)  := by
  rw [columns_regular 7 4 7 (-1) j (by omega) (by omega) (by omega) (by omega) (by omega)]
  simp only [regular]
  have hd : (4*(j:ℤ)+7+1).toNat = 4*j+8 := by exact Eq.symm (Nat.add_succ (4 * j) 7)
  have hq : (4*(j:ℤ)+(-1)+1).toNat = 4*j := by omega
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma shifted_difference (j : ℕ) :
    h * diff (columns 2 1 2 0) (j+1) = X * columns 7 4 7 (-1) j := by
  simp only [diff, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, source_gf, target_gf]
  exact difference_shifted j

private lemma source_head : coeff 0 (h * diff (columns 2 1 2 0) 0) = 2 := by
  simp only [diff, ↓reduceIte, source_gf, coeff_zero_eq_constantCoeff_apply,
    map_mul, map_add, map_pow, constantCoeff_X, constantCoeff_C,
    constantCoeff_invLin, h_constant]
  norm_num [sub_eq_add_neg]

private lemma shiftedG_all (n : ℕ) : G 2 1 2 0 (n+1) = 2 * G 7 4 7 (-1) n := by
  rw [G_eq_smat, G_eq_smat]
  calc
    (smat (columns 2 1 2 0) (n+1)).det =
        (smat (fun j => h * diff (columns 2 1 2 0) j) (n+1)).det := by
      rw [det_smat_mul h h_constant, det_diff]
    _ = 2 * (smat (columns 7 4 7 (-1)) n).det :=
      det_shift _ _ _ source_head shifted_difference n

theorem result : claim := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n=m+1 := ⟨n-1, by omega⟩
  simpa using shiftedG_all m

private lemma gf_T (j : ℕ) : columns 8 3 8 2 j =
    C 8 * invLin 2 (4*j+9) + X^(4*j+3) * invLin 1 (4*j+9) := by
  rw [columns_regular 8 3 8 2 j (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(j:ℤ)+8+1).toNat = 4*j+9 := by exact Eq.symm (Nat.add_succ (4 * j) 8)
  have hq : (4*(j:ℤ)+2+1).toNat = 4*j+3 := by exact Eq.symm (Nat.add_succ (4 * j) 2)
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_B (j : ℕ) : columns 0 1 (-2) (-4) (j+1) =
    C 8 * X^2 * invLin 2 (4*j+5) + X^(4*j+1) * invLin 1 (4*j+5) := by
  rw [columns_regular 0 1 (-2) (-4) (j+1) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(((j+1):ℕ):ℤ)+0+1).toNat = 4*j+5 := by exact Eq.symm (Nat.add_succ (4 * j) 4)
  have hq : (4*(((j+1):ℕ):ℤ)+(-4)+1).toNat = 4*j+1 := by omega
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_C (j : ℕ) : columns 1 3 (-2) (-8) (j+2) =
    C 64 * X^3 * invLin 2 (4*j+10) - X^(4*j+1) * invLin 1 (4*j+10) := by
  rw [columns_regular 1 3 (-2) (-8) (j+2) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(((j+2):ℕ):ℤ)+1+1).toNat = 4*j+10 := by exact Eq.symm (Nat.add_succ (4 * j) 9)
  have hq : (4*(((j+2):ℕ):ℤ)+(-8)+1).toNat = 4*j+1 := by omega
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_D (j : ℕ) : columns 5 4 3 (-5) (j+1) =
    C 64 * X^2 * invLin 2 (4*j+10) - X^(4*j+0) * invLin 1 (4*j+10) := by
  rw [columns_regular 5 4 3 (-5) (j+1) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(((j+1):ℕ):ℤ)+5+1).toNat = 4*j+10 := by exact Eq.symm (Nat.add_succ (4 * j) 9)
  have hq : (4*(((j+1):ℕ):ℤ)+(-5)+1).toNat = 4*j+0 := by omega
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_E (j : ℕ) : columns 6 6 3 (-9) (j+2) =
    C 512 * X^3 * invLin 2 (4*j+15) + X^(4*j+0) * invLin 1 (4*j+15) := by
  rw [columns_regular 6 6 3 (-9) (j+2) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(((j+2):ℕ):ℤ)+6+1).toNat = 4*j+15 := by exact Eq.symm (Nat.add_succ (4 * j) 14)
  have hq : (4*(((j+2):ℕ):ℤ)+(-9)+1).toNat = 4*j+0 := by omega
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_F (j : ℕ) : columns 9 5 8 (-2) (j+1) =
    C 64 * X^1 * invLin 2 (4*j+14) - X^(4*j+3) * invLin 1 (4*j+14) := by
  rw [columns_regular 9 5 8 (-2) (j+1) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(((j+1):ℕ):ℤ)+9+1).toNat = 4*j+14 := by exact Eq.symm (Nat.add_succ (4 * j) 13)
  have hq : (4*(((j+1):ℕ):ℤ)+(-2)+1).toNat = 4*j+3 := by omega
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_H (j : ℕ) : columns 1 1 0 (-2) (j+1) =
    C 4 * X^1 * invLin 2 (4*j+6) - X^(4*j+3) * invLin 1 (4*j+6) := by
  rw [columns_regular 1 1 0 (-2) (j+1) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(((j+1):ℕ):ℤ)+1+1).toNat = 4*j+6 := by exact Eq.symm (Nat.add_succ (4 * j) 5)
  have hq : (4*(((j+1):ℕ):ℤ)+(-2)+1).toNat = 4*j+3 := by omega
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_I (j : ℕ) : columns 2 3 0 (-6) (j+2) =
    C 32 * X^2 * invLin 2 (4*j+11) + X^(4*j+3) * invLin 1 (4*j+11) := by
  rw [columns_regular 2 3 0 (-6) (j+2) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(((j+2):ℕ):ℤ)+2+1).toNat = 4*j+11 := by exact Eq.symm (Nat.add_succ (4 * j) 10)
  have hq : (4*(((j+2):ℕ):ℤ)+(-6)+1).toNat = 4*j+3 := by omega
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_V (j : ℕ) : columns 5 2 5 1 j =
    C 4 * invLin 2 (4*j+6) - X^(4*j+2) * invLin 1 (4*j+6) := by
  rw [columns_regular 5 2 5 1 j (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(j:ℤ)+5+1).toNat = 4*j+6 := by exact Eq.symm (Nat.add_succ (4 * j) 5)
  have hq : (4*(j:ℤ)+1+1).toNat = 4*j+2 := by exact Eq.symm (Nat.add_succ (4 * j) 1)
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_J (j : ℕ) : columns 6 4 5 (-3) (j+1) =
    C 32 * X^1 * invLin 2 (4*j+11) + X^(4*j+2) * invLin 1 (4*j+11) := by
  rw [columns_regular 6 4 5 (-3) (j+1) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(((j+1):ℕ):ℤ)+6+1).toNat = 4*j+11 := by exact Eq.symm (Nat.add_succ (4 * j) 10)
  have hq : (4*(((j+1):ℕ):ℤ)+(-3)+1).toNat = 4*j+2 := by omega
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_K (j : ℕ) : columns 7 6 5 (-7) (j+2) =
    C 256 * X^2 * invLin 2 (4*j+16) - X^(4*j+2) * invLin 1 (4*j+16) := by
  rw [columns_regular 7 6 5 (-7) (j+2) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(((j+2):ℕ):ℤ)+7+1).toNat = 4*j+16 := by exact Eq.symm (Nat.add_succ (4 * j) 15)
  have hq : (4*(((j+2):ℕ):ℤ)+(-7)+1).toNat = 4*j+2 := by omega
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma gf_Q (j : ℕ) : columns 4 2 3 (-1) j =
    C 8 * X * invLin 2 (4*j+5) + X^(4*j) * invLin 1 (4*j+5) := by
  rw [columns_regular 4 2 3 (-1) j (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hd : (4*(j:ℤ)+4+1).toNat=4*j+5 := by exact Eq.symm (Nat.add_succ (4 * j) 4)
  have hq : (4*(j:ℤ)+(-1)+1).toNat=4*j := by omega
  unfold regular
  rw [hd, hq]
  norm_num [sub_eq_add_neg]

private lemma p_gf (j : ℕ) : columns 3 0 3 3 j =
    1 + invLin 2 (4*j+4) - X^(4*j+4) * invLin 1 (4*j+4) := by
  ext i
  cases i with
  | zero =>
    simp only [columns, coeff_mk, entry, binom]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have ht : (4*(j:ℤ)+3).toNat = 4*j+3 := by exact Eq.symm (Nat.add_succ (4 * j) 2)
    have hq : (0:ℚ)+4*(j:ℚ)+3 = ((4*j+3:ℕ):ℚ) := by push_cast; ring
    rw [ht]
    norm_num only [Int.natCast_zero, zero_add, add_zero, neg_zero, zpow_zero, one_mul]
    have he : (4:ℚ)*j+3 = ((4*j+3:ℕ):ℚ) := by push_cast; ring
    rw [he, Ring.choose_natCast]
    simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_invLin]
  | succ i =>
    simp only [columns, coeff_mk, entry, binom]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have ht : (4*(j:ℤ)+3).toNat = 4*j+3 := by exact Eq.symm (Nat.add_succ (4 * j) 2)
    rw [ht]
    simp only [map_sub, map_add, coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add]
    rw [show 4*j+4 = (4*j+3)+1 by omega, coeff_invLin]
    norm_num only [Int.cast_ofNat, Int.cast_zero, add_zero, zpow_natCast]
    rw [choose_reflect (-(i.succ:ℚ)+4*(j:ℚ)+3) (4*j+3)]
    have he : (-1:ℚ)^(4*j+3) = -1 := by
      rw [show 4*j+3=2*(2*j+1)+1 by omega, pow_succ, pow_mul]
      norm_num [sub_eq_add_neg]
    rw [he]
    have hn1 : (i.succ:ℚ)+4*j+3 = ((4*j+3+i.succ:ℕ):ℚ) := by push_cast; ring
    have hn2 : ((4*j+3:ℕ):ℚ)-(-(i.succ:ℚ)+4*j+3)-1 = (i:ℚ) := by push_cast; ring
    rw [hn1, hn2, Ring.choose_natCast, Ring.choose_natCast]
    rw [coeff_X_pow_mul']
    by_cases hi : 4*j+3+1 ≤ i.succ
    · rw [ite_eq_left hi, coeff_invLin]
      have hchoose : 4*j+3+(i.succ-(4*j+3+1)) = i := by omega
      rw [hchoose]
      norm_num [sub_eq_add_neg]
    · have hzero : i.choose (4*j+3) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [ite_eq_right hi, hzero]
      norm_num [sub_eq_add_neg]

private lemma p_shifted_difference (j : ℕ) :
    h * diff (columns 3 0 3 3) (j+1) = X * columns 8 3 8 2 j := by
  simp only [diff, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, p_gf, gf_T]
  have hd := difference 1 (-1) (4*j+3) 0 (4*j+4)
  convert hd using 1 <;>
    norm_num only [map_one, map_neg, map_ofNat, pow_zero, pow_one, mul_one, one_mul, neg_mul] <;> ring_nf

private noncomputable def trans (f : ℕ → PowerSeries ℚ) (j : ℕ) : PowerSeries ℚ := h * diff f j
private lemma det_trans (f : ℕ → PowerSeries ℚ) (n : ℕ) : (smat (trans f) n).det = (smat f n).det := by
  change (smat (fun j => h * diff f j) n).det = _
  rw [det_smat_mul h h_constant, det_diff]
private lemma det_transN (k : ℕ) (f : ℕ → PowerSeries ℚ) (n : ℕ) :
    (smat ((trans^[k]) f) n).det = (smat f n).det := by
  have hi : (fun f : ℕ → PowerSeries ℚ => (smat f n).det) ∘ trans =
      (fun f : ℕ → PowerSeries ℚ => (smat f n).det) := by
    funext f
    exact det_trans f n
  exact congrFun (Function.iterate_invariant hi k) f
private lemma trans_succ (f : ℕ → PowerSeries ℚ) (j : ℕ) : trans f (j+1) = h*(f (j+1)-f j) := by
  exact PowerSeries.ext (congrFun rfl)

private lemma trans_T (j : ℕ) : trans (columns 8 3 8 2) (j+1) = columns 9 5 8 (-2) (j+1) := by
  rw [trans_succ, gf_T (j+1), gf_T j, gf_F j]
  convert difference 8 1 (4*j+8) 0 (4*j+3) using 1 <;>
    norm_num only [map_ofNat, map_one, pow_zero, pow_one, mul_one, one_mul] <;> ring_nf

private lemma trans_V (j : ℕ) : trans (columns 5 2 5 1) (j+1) = columns 6 4 5 (-3) (j+1) := by
  rw [trans_succ, gf_V (j+1), gf_V j, gf_J j]
  convert difference 4 (-1) (4*j+5) 0 (4*j+2) using 1 <;>
    norm_num only [map_ofNat, map_one, map_neg, pow_zero, pow_one, mul_one, one_mul, neg_mul] <;> ring_nf

private lemma trans_H (j : ℕ) : trans (columns 1 1 0 (-2)) (j+2) = columns 2 3 0 (-6) (j+2) := by
  have h1 := gf_H (j+1)
  have h0 := gf_H j
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1
  rw [show j+2=(j+1)+1 by omega, trans_succ]
  rw [show (j+1)+1=j+2 by omega, h1, h0, gf_I]
  convert difference 4 (-1) (4*j+5) 1 (4*j+3) using 1 <;>
    norm_num only [map_ofNat, map_one, map_neg, pow_zero, pow_one, mul_one, one_mul, neg_mul] <;> ring_nf

private lemma trans_B (j : ℕ) : trans (columns 0 1 (-2) (-4)) (j+3) = columns 1 3 (-2) (-8) (j+3) := by
  have h1 := gf_B (j+2)
  have h0 := gf_B (j+1)
  have hc := gf_C (j+1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h0 hc
  rw [show j+3=(j+2)+1 by omega, trans_succ]
  rw [show (j+2)+1=j+3 by omega, h1, h0, hc]
  convert difference 8 1 (4*j+8) 2 (4*j+5) using 1 <;>
    norm_num only [map_ofNat, map_one, pow_zero, pow_one, mul_one, one_mul] <;> ring_nf

private lemma trans2_V (j : ℕ) : (trans^[2]) (columns 5 2 5 1) (j+2) = columns 7 6 5 (-7) (j+2) := by
  change trans (trans (columns 5 2 5 1)) (j+2) = _
  rw [show j+2=(j+1)+1 by omega, trans_succ, trans_V (j+1), trans_V j]
  rw [gf_J (j+1), gf_J j, show (j+1)+1=j+2 by omega, gf_K j]
  convert difference 32 1 (4*j+10) 1 (4*j+2) using 1 <;>
    norm_num only [map_ofNat, map_one, pow_zero, pow_one, mul_one, one_mul] <;> ring_nf

private lemma trans2_P (j : ℕ) : (trans^[2]) (columns 3 0 3 3) (j+2) = columns 5 4 3 (-5) (j+2) := by
  change trans (trans (columns 3 0 3 3)) (j+2) = _
  rw [show j+2=(j+1)+1 by omega, trans_succ]
  change h * (h * diff (columns 3 0 3 3) ((j+1)+1) - h * diff (columns 3 0 3 3) (j+1)) = _
  rw [p_shifted_difference (j+1), p_shifted_difference j]
  rw [show h*(X*columns 8 3 8 2 (j+1)-X*columns 8 3 8 2 j) = X*trans (columns 8 3 8 2) (j+1) by rw [trans_succ]; ring]
  rw [trans_T, gf_F j]
  have hg := gf_D (j+1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hg
  rw [hg]
  norm_num only [map_ofNat, pow_succ]
  ring_nf

private lemma trans3_P (j : ℕ) : (trans^[3]) (columns 3 0 3 3) (j+3) = columns 6 6 3 (-9) (j+3) := by
  change trans ((trans^[2]) (columns 3 0 3 3)) (j+3) = _
  rw [show j+3=(j+2)+1 by omega, trans_succ]
  rw [show (j+2)+1=(j+1)+2 by omega, trans2_P (j+1), trans2_P j]
  have h1 := gf_D (j+2)
  have h0 := gf_D (j+1)
  have hc := gf_E (j+1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h0 hc
  rw [h1, h0, show (j+1)+2=j+3 by omega, hc]
  convert difference 64 (-1) (4*j+13) 2 (4*j+4) using 1 <;>
    norm_num only [map_ofNat, map_one, map_neg, pow_zero, pow_one, mul_one, one_mul, neg_mul] <;> ring_nf

private lemma det_comparison (f g : ℕ → PowerSeries ℚ) (k m N : ℕ) (hN : m ≤ N)
    (hc : ∀ j, (trans^[k]) f (j+m) = g (j+m))
    (hz : ∀ i j : ℕ, i < m → m ≤ j → coeff i (g j) = 0) :
    (smat g m).det * (smat f N).det = (smat f m).det * (smat g N).det := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
  let A := smat ((trans^[k]) f) (m+n)
  let B := smat g (m+n)
  have hcommon : ∀ i : Fin (m+n), ∀ j : Fin n, A i (j.natAdd m) = B i (j.natAdd m) := by
    intro i j
    change coeff i.val ((trans^[k]) f (m+j.val)) = coeff i.val (g (m+j.val))
    rw [Nat.add_comm m j.val, hc]
  have hzero : ∀ i : Fin m, ∀ j : Fin n, A (i.castAdd n) (j.natAdd m) = 0 := by
    intro i j
    rw [hcommon]
    exact hz i.val (m+j.val) i.isLt (by omega)
  have hd := shared_columns A B hzero hcommon
  change (smat g m).det * (smat ((trans^[k]) f) (m+n)).det =
    (smat ((trans^[k]) f) m).det * (smat g (m+n)).det at hd
  simpa only [det_transN] using hd

private lemma columns_vanish (a b g d : ℤ) (j i : ℕ)
    (hr : 0 ≤ 4*(j:ℤ)+a) (hc : 0 ≤ 4*(j:ℤ)+g)
    (hs : 0 ≤ a-g) (hq : 0 ≤ 4*(j:ℤ)+d+1) (hc' : 0 ≤ a-d-1)
    (hi1 : i < (a-g).toNat) (hi2 : i < (4*(j:ℤ)+d+1).toNat) :
    coeff i (columns a b g d j) = 0 := by
  rw [columns_regular a b g d j hr hc hs hq hc']
  simp only [regular, map_add, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp [show ¬ (a-g).toNat ≤ i by omega,
    show ¬ (4*(j:ℤ)+d+1).toNat ≤ i by omega]

lemma link_BC (N : ℕ) (hN : 3 ≤ N) : G 1 3 (-2) (-8) N = -448 * G 0 1 (-2) (-4) N := by
  have boundary_C3 : G 1 3 (-2) (-8) 3 = (-10752) := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have boundary_B3 : G 0 1 (-2) (-4) 3 = 24 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have hc : ∀ j, (trans^[1]) (columns 0 1 (-2) (-4)) (j+3) = columns 1 3 (-2) (-8) (j+3) := by
    intro j
    exact trans_B j
  have hz : ∀ i j : ℕ, i < 3 → 3 ≤ j → coeff i (columns 1 3 (-2) (-8) j) = 0 := by
    intro i j hi hj
    exact columns_vanish _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hd := det_comparison (columns 0 1 (-2) (-4)) (columns 1 3 (-2) (-8)) 1 3 N hN hc hz
  simp only [← G_eq_smat, boundary_B3, boundary_C3] at hd
  linarith

lemma link_PD (N : ℕ) (hN : 2 ≤ N) : G 5 4 3 (-5) N = 63 * G 3 0 3 3 N := by
  have boundary_D2 : G 5 4 3 (-5) 2 = 1008 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have boundary_P2 : G 3 0 3 3 2 = 16 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have hc : ∀ j, (trans^[2]) (columns 3 0 3 3) (j+2) = columns 5 4 3 (-5) (j+2) := by exact fun j => trans2_P j
  have hz : ∀ i j : ℕ, i < 2 → 2 ≤ j → coeff i (columns 5 4 3 (-5) j) = 0 := by
    intro i j hi hj
    exact columns_vanish _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hd := det_comparison (columns 3 0 3 3) (columns 5 4 3 (-5)) 2 2 N hN hc hz
  simp only [← G_eq_smat, boundary_P2, boundary_D2] at hd
  linarith

lemma link_PE (N : ℕ) (hN : 3 ≤ N) : G 6 6 3 (-9) N = 1002001 / 4 * G 3 0 3 3 N := by
  have boundary_E3 : G 6 6 3 (-9) 3 = 256512256 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have boundary_P3 : G 3 0 3 3 3 = 1024 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have hc : ∀ j, (trans^[3]) (columns 3 0 3 3) (j+3) = columns 6 6 3 (-9) (j+3) := by exact fun j => trans3_P j
  have hz : ∀ i j : ℕ, i < 3 → 3 ≤ j → coeff i (columns 6 6 3 (-9) j) = 0 := by
    intro i j hi hj
    exact columns_vanish _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hd := det_comparison (columns 3 0 3 3) (columns 6 6 3 (-9)) 3 3 N hN hc hz
  simp only [← G_eq_smat, boundary_P3, boundary_E3] at hd
  linarith

lemma link_TF (N : ℕ) (hN : 1 ≤ N) : G 8 3 8 2 N = -(4 / 5) * G 9 5 8 (-2) N := by
  have boundary_F1 : G 9 5 8 (-2) 1 = (-10) := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have boundary_T1 : G 8 3 8 2 1 = 8 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have hc : ∀ j, (trans^[1]) (columns 8 3 8 2) (j+1) = columns 9 5 8 (-2) (j+1) := by
    intro j
    exact trans_T j
  have hz : ∀ i j : ℕ, i < 1 → 1 ≤ j → coeff i (columns 9 5 8 (-2) j) = 0 := by
    intro i j hi hj
    exact columns_vanish _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hd := det_comparison (columns 8 3 8 2) (columns 9 5 8 (-2)) 1 1 N hN hc hz
  simp only [← G_eq_smat, boundary_T1, boundary_F1] at hd
  linarith

lemma link_HI (N : ℕ) (hN : 2 ≤ N) : G 1 1 0 (-2) N = -(1 / 49) * G 2 3 0 (-6) N := by
  have boundary_I2 : G 2 3 0 (-6) 2 = 392 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have boundary_H2 : G 1 1 0 (-2) 2 = (-8) := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have hc : ∀ j, (trans^[1]) (columns 1 1 0 (-2)) (j+2) = columns 2 3 0 (-6) (j+2) := by
    intro j
    exact trans_H j
  have hz : ∀ i j : ℕ, i < 2 → 2 ≤ j → coeff i (columns 2 3 0 (-6) j) = 0 := by
    intro i j hi hj
    exact columns_vanish _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hd := det_comparison (columns 1 1 0 (-2)) (columns 2 3 0 (-6)) 1 2 N hN hc hz
  simp only [← G_eq_smat, boundary_H2, boundary_I2] at hd
  linarith

lemma link_VJ (N : ℕ) (hN : 1 ≤ N) : G 5 2 5 1 N = 1 / 7 * G 6 4 5 (-3) N := by
  have boundary_J1 : G 6 4 5 (-3) 1 = 28 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have boundary_V1 : G 5 2 5 1 1 = 4 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have hc : ∀ j, (trans^[1]) (columns 5 2 5 1) (j+1) = columns 6 4 5 (-3) (j+1) := by
    intro j
    exact trans_V j
  have hz : ∀ i j : ℕ, i < 1 → 1 ≤ j → coeff i (columns 6 4 5 (-3) j) = 0 := by
    intro i j hi hj
    exact columns_vanish _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hd := det_comparison (columns 5 2 5 1) (columns 6 4 5 (-3)) 1 1 N hN hc hz
  simp only [← G_eq_smat, boundary_V1, boundary_J1] at hd
  linarith

lemma link_VK (N : ℕ) (hN : 2 ≤ N) : G 5 2 5 1 N = 2 / 5577 * G 7 6 5 (-7) N := by
  have boundary_K2 : G 7 6 5 (-7) 2 = 356928 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have boundary_V2 : G 5 2 5 1 2 = 128 := by
    norm_num [G, binom, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_unique,
      Ring.choose_eq_smul, descPochhammer_succ_left, descPochhammer_zero,
      Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast, smul_eq_mul]
  have hc : ∀ j, (trans^[2]) (columns 5 2 5 1) (j+2) = columns 7 6 5 (-7) (j+2) := by exact fun j => trans2_V j
  have hz : ∀ i j : ℕ, i < 2 → 2 ≤ j → coeff i (columns 7 6 5 (-7) j) = 0 := by
    intro i j hi hj
    exact columns_vanish _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hd := det_comparison (columns 5 2 5 1) (columns 7 6 5 (-7)) 2 2 N hN hc hz
  simp only [← G_eq_smat, boundary_V2, boundary_K2] at hd
  linarith

private lemma entry_shift (a b g d : ℤ) (i j : ℕ) :
    entry a b g d (i+1) (j+1) = entry (a+4) (b+1) (g+5) (d+3) i j := by
  have he : ((i+1:ℕ):ℤ)+b=(i:ℤ)+(b+1) := by omega
  have hn : 4*((j+1:ℕ):ℤ)+a=4*(j:ℤ)+(a+4) := by omega
  have ht1 : ((i+1:ℕ):ℚ)+4*((j+1:ℕ):ℚ)+(g:ℚ) = (i:ℚ)+4*(j:ℚ)+((g+5:ℤ):ℚ) := by push_cast; ring
  have ht2 : -((i+1:ℕ):ℚ)+4*((j+1:ℕ):ℚ)+(d:ℚ) = -(i:ℚ)+4*(j:ℚ)+((d+3:ℤ):ℚ) := by push_cast; ring
  simp only [entry, he, hn, ht1, ht2]

private lemma columns_shift (a b g d : ℤ) (j : ℕ) (hz : coeff 0 (columns a b g d (j+1))=0) :
    columns a b g d (j+1) = X * columns (a+4) (b+1) (g+5) (d+3) j := by
  ext i
  cases i with
  | zero => rw [hz, coeff_zero_X_mul]
  | succ i =>
    rw [coeff_succ_X_mul]
    simpa only [columns, coeff_mk] using entry_shift a b g d i j

lemma prop_H (n : ℕ) : G 1 1 0 (-2) (n+1) = -2 * G 5 2 5 1 n := by
  rw [G_eq_smat, G_eq_smat]
  apply det_shift
  · norm_num [columns, entry, binom, coeff_mk, Ring.choose_eq_smul,
      descPochhammer_succ_left, descPochhammer_zero, Polynomial.smeval_mul,
      Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, smul_eq_mul]
  · intro j
    apply columns_shift
    rw [gf_H j]
    simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_invLin]

lemma prop_B (n : ℕ) : G 0 1 (-2) (-4) (n+2) = 3 * G 8 3 8 2 n := by
  have hB : ∀ j, columns 0 1 (-2) (-4) (j+1) = X * columns 4 2 3 (-1) j := by
    intro j
    apply columns_shift
    rw [gf_B j]
    simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_invLin]
  have hQ : ∀ j, columns 4 2 3 (-1) (j+1) = X * columns 8 3 8 2 j := by
    intro j
    apply columns_shift
    rw [gf_Q (j+1)]
    simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_invLin]
  have hbhead : coeff 0 (columns 0 1 (-2) (-4) 0) = 3 := by
    norm_num [columns, coeff_mk, entry, binom]
  have hqhead : coeff 0 (columns 4 2 3 (-1) 0) = 1 := by
    rw [gf_Q 0]
    norm_num [coeff_zero_eq_constantCoeff_apply, constantCoeff_invLin]
  have hb := det_shift _ _ _ hbhead hB (n+1)
  have hq := det_shift _ _ _ hqhead hQ n
  simp only [← G_eq_smat] at hb hq
  simpa only [Nat.add_assoc, Nat.reduceAdd, hq, mul_one, one_mul] using hb

lemma p_shift_all (n : ℕ) : G 3 0 3 3 (n+1) = 2 * G 8 3 8 2 n := by
  have hphead : coeff 0 (trans (columns 3 0 3 3) 0) = 2 := by
    norm_num [trans, diff, p_gf, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_invLin, h_constant]
  rw [G_eq_smat, G_eq_smat, ← det_trans (columns 3 0 3 3)]
  exact det_shift _ _ _ hphead p_shifted_difference n

end D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserShiftedG
