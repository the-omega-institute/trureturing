/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportInertia
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportInertia
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact mixed-sign inertia of the full six-support Schur operator. -/

import D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra
import D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback
import Mathlib.Tactic

/-! Source: the complete low-spectrum and mixed-inertia sections at
revision b93becea662a746badeadba42fdc3d3eb3db9382, respectively blobs
10576d85188447cea8efba1549722d8e14c050f2 and
ea37044cd1ad3bcff6e1a5a3bf4e91fa8219961d.
The operator, singular cases, multiplicities and strict intervals are separate
from the already proved complete integer-parameter graph classification. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportInertia
open Matrix Polynomial Finset
open D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback

/-- Algebraic negative-root count, including multiplicities. -/
def negativeCount {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : ℕ := A.charpoly.roots.countP (fun t => t < 0)

/-- Algebraic multiplicity of the zero eigenvalue. -/
def zeroCount {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : ℕ := A.charpoly.roots.countP (fun t => t = 0)

theorem negativeCount_eq {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    negativeCount A = RHLinalg.negIndex hA := by
  classical
  simp [negativeCount, RHLinalg.negIndex, hA.roots_charpoly_eq_eigenvalues,
    Multiset.countP_map, Finset.card_def]

theorem zeroCount_eq {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    zeroCount A = Fintype.card n - A.rank := by
  classical
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hp := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i : n => hA.eigenvalues i = 0)
  have hz : zeroCount A = #{i | hA.eigenvalues i = 0} := by
    simp [zeroCount, hA.roots_charpoly_eq_eigenvalues,
      Multiset.countP_map, Finset.card_def]
  rw [hz]
  apply Nat.eq_sub_of_add_eq
  simpa only [Finset.card_univ] using hp

theorem congruence_counts {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (B : Matrix n n ℝ)
    (hB : IsUnit B.det) :
    negativeCount (Bᴴ * A * B) = negativeCount A ∧
      zeroCount (Bᴴ * A * B) = zeroCount A := by
  have h := inertia_invariant_of_isUnit_det hA B hB
  have hBA := Matrix.isHermitian_conjTranspose_mul_mul B hA
  constructor
  · rw [negativeCount_eq hBA, negativeCount_eq hA]
    exact h.2
  · rw [zeroCount_eq hBA, zeroCount_eq hA,
      Matrix.rank_mul_eq_left_of_isUnit_det B (Bᴴ * A) hB,
      Matrix.rank_mul_eq_right_of_isUnit_det Bᴴ A (by simpa using hB)]

theorem diagonal_counts {n : Type} [Fintype n] [DecidableEq n]
    (d : n → ℝ) :
    negativeCount (diagonal d) = #{i | d i < 0} ∧
      zeroCount (diagonal d) = #{i | d i = 0} := by
  classical
  have hr : (diagonal d).charpoly.roots = Finset.univ.val.map d := by
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _
  simp [negativeCount, zeroCount, hr, Multiset.countP_map, Finset.card_def]

theorem block_counts {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (A : Matrix n n ℝ) (D : Matrix m m ℝ) :
    negativeCount (fromBlocks A 0 0 D) = negativeCount A + negativeCount D ∧
      zeroCount (fromBlocks A 0 0 D) = zeroCount A + zeroCount D := by
  have hn : A.charpoly * D.charpoly ≠ 0 :=
    mul_ne_zero A.charpoly_monic.ne_zero D.charpoly_monic.ne_zero
  simp [negativeCount, zeroCount, Matrix.charpoly_fromBlocks_zero₁₂,
    Polynomial.roots_mul hn]

/-- The entire diagonal-minus-rank-one operator, with no sign restriction. -/
def rankOne (k v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal k - vecMulVec v v

private def last (t : ℝ) : Matrix Unit Unit ℝ := diagonal (fun _ => t)
private def border (k v : Fin 3 → ℝ) : Matrix (Fin 3 ⊕ Unit) (Fin 3 ⊕ Unit) ℝ :=
  fromBlocks (diagonal k) (Matrix.of fun i _ => v i) (Matrix.of fun _ j => v j) (last 1)
private def eliminateLast (v : Fin 3 → ℝ) :
    Matrix (Fin 3 ⊕ Unit) (Fin 3 ⊕ Unit) ℝ :=
  fromBlocks 1 0 (Matrix.of fun _ j => -v j) 1
private def eliminateDiagonal (k v : Fin 3 → ℝ) :
    Matrix (Fin 3 ⊕ Unit) (Fin 3 ⊕ Unit) ℝ :=
  fromBlocks 1 (Matrix.of fun i _ => -v i / k i) 0 1

private theorem border_hermitian (k v : Fin 3 → ℝ) : (border k v).IsHermitian := by
  ext i j
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
    simp [border, last, Matrix.fromBlocks, conjTranspose_apply, diagonal_apply, eq_comm]
  split_ifs <;> simp_all

private theorem eliminateLast_det (v : Fin 3 → ℝ) :
    (eliminateLast v).det = 1 := by
  unfold eliminateLast
  rw [Matrix.det_fromBlocks_zero₁₂]
  simp

private theorem eliminateDiagonal_det (k v : Fin 3 → ℝ) :
    (eliminateDiagonal k v).det = 1 := by
  unfold eliminateDiagonal
  rw [Matrix.det_fromBlocks_zero₂₁]
  simp

private theorem eliminateLast_identity (k v : Fin 3 → ℝ) :
    (eliminateLast v)ᴴ * border k v * eliminateLast v =
      fromBlocks (rankOne k v) 0 0 (last 1) := by
  ext i j
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals norm_num [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
    eliminateLast, border, rankOne, last, conjTranspose_apply, diagonal_apply,
    Matrix.one_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec, Matrix.fromBlocks]
  all_goals ring

private theorem eliminateDiagonal_identity (k v : Fin 3 → ℝ) (hk : ∀ i, k i ≠ 0) :
    (eliminateDiagonal k v)ᴴ * border k v * eliminateDiagonal k v =
      fromBlocks (diagonal k) 0 0 (last (1 - ∑ i, (v i)^2 / k i)) := by
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  ext i j
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals norm_num [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
    eliminateDiagonal, border, last, conjTranspose_apply, diagonal_apply,
    Matrix.one_apply, Matrix.fromBlocks]
  all_goals field_simp [h0,h1,h2]
  all_goals ring

/-- Every mixed-sign nonsingular diagonal: the full original rank-one
inertia formula, including the zero value of its scalar Schur complement. -/
theorem nonsingular_diagonal (k v : Fin 3 → ℝ) (hk : ∀ i, k i ≠ 0) :
    negativeCount (rankOne k v) = #{i | k i < 0} +
      (if 1 - ∑ i, (v i)^2 / k i < 0 then 1 else 0) ∧
    zeroCount (rankOne k v) =
      (if 1 - ∑ i, (v i)^2 / k i = 0 then 1 else 0) := by
  classical
  have hL := congruence_counts (border_hermitian k v) (eliminateLast v)
    (by rw [eliminateLast_det]; exact isUnit_one)
  have hD := congruence_counts (border_hermitian k v) (eliminateDiagonal k v)
    (by rw [eliminateDiagonal_det]; exact isUnit_one)
  rw [eliminateLast_identity] at hL
  rw [eliminateDiagonal_identity k v hk] at hD
  have bL := block_counts (rankOne k v) (last 1)
  have bD := block_counts (diagonal k) (last (1-∑ i, (v i)^2/k i))
  have dK := diagonal_counts k
  have d1 := diagonal_counts (fun _ : Unit => (1 : ℝ))
  have dF := diagonal_counts (fun _ : Unit => 1-∑ i, (v i)^2/k i)
  have hz : #{i | k i = 0} = 0 := by simp [hk]
  rw [bL.1,bL.2] at hL
  rw [bD.1,bD.2,dK.1,dK.2,hz] at hD
  change negativeCount (last 1) = _ ∧ zeroCount (last 1) = _ at d1
  change negativeCount (last (1-∑ i, (v i)^2/k i)) = _ ∧
    zeroCount (last (1-∑ i, (v i)^2/k i)) = _ at dF
  rw [d1.1,d1.2] at hL
  rw [dF.1,dF.2] at hD
  simp only [Finset.univ_unique, Finset.filter_singleton] at hL hD
  split_ifs at * <;> norm_num at * <;> constructor <;> omega

private def pivotCoordinates (v : Fin 3 → ℝ) (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i l => if i = j then if l = j then (v j)⁻¹ else -v l / v j
    else if i = l then 1 else 0

private def pivotInverse (v : Fin 3 → ℝ) (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i l => if i = j then v l else if i = l then 1 else 0

private theorem pivot_inverse (v : Fin 3 → ℝ) (j : Fin 3) (hv : v j ≠ 0) :
    pivotInverse v j * pivotCoordinates v j = 1 := by
  ext i l
  fin_cases j <;> fin_cases i <;> fin_cases l <;>
    norm_num [pivotInverse, pivotCoordinates, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply] at hv ⊢ <;> field_simp <;> ring

private theorem pivot_det (v : Fin 3 → ℝ) (j : Fin 3) (hv : v j ≠ 0) :
    IsUnit (pivotCoordinates v j).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have h := congrArg Matrix.det (pivot_inverse v j hv)
  rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at h
  norm_num at h

private theorem pivot_identity (k v : Fin 3 → ℝ) (j : Fin 3)
    (hk : k j = 0) (hv : v j ≠ 0) :
    (pivotCoordinates v j)ᴴ * rankOne k v * pivotCoordinates v j =
      diagonal (fun i => if i = j then -1 else k i) := by
  ext i l
  fin_cases j <;> fin_cases i <;> fin_cases l <;>
    norm_num [pivotCoordinates, rankOne, Matrix.mul_apply, Fin.sum_univ_three,
      conjTranspose_apply, diagonal_apply, Matrix.vecMulVec_apply] at hk hv ⊢ <;>
    simp only [hk] <;> field_simp <;> ring <;> simp_all

private theorem pivot_cardinalities (k : Fin 3 → ℝ) (j : Fin 3) (hk : k j = 0) :
    #{i | (if i = j then (-1 : ℝ) else k i) < 0} = #{i | k i < 0} + 1 ∧
    #{i | (if i = j then (-1 : ℝ) else k i) = 0} + 1 = #{i | k i = 0} := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  fin_cases j <;> simp_all <;> split_ifs <;> omega

/-- Every singular diagonal, including two or three zero entries. The
positive source vector makes any zero coordinate a lawful pivot. -/
theorem singular_diagonal (k v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i)
    (hz : ∃ j, k j = 0) :
    negativeCount (rankOne k v) = #{i | k i < 0} + 1 ∧
      zeroCount (rankOne k v) + 1 = #{i | k i = 0} := by
  classical
  obtain ⟨j,hj⟩ := hz
  have hK : (rankOne k v).IsHermitian := by
    ext i l
    simp [rankOne, Matrix.vecMulVec, conjTranspose_apply, diagonal_apply, eq_comm, mul_comm]
    split_ifs <;> simp_all
  have h := congruence_counts hK (pivotCoordinates v j)
    (pivot_det v j (hv j).ne')
  rw [pivot_identity k v j hj (hv j).ne'] at h
  have hd := diagonal_counts (fun i => if i = j then (-1 : ℝ) else k i)
  have hc := pivot_cardinalities k j hj
  omega

/-- The literal three diagonal values in the original six-support Schur
complement; the index enumerates a,b,c, including repeated parameters. -/
def schurDiagonal (a b c x : ℝ) : Fin 3 → ℝ := fun i =>
  a+b+c-x-x*a*b*c/(![a,b,c] i * (![a,b,c] i-x))

/-- The actual full real Schur operator, retaining all off-diagonal terms. -/
def schur (a b c x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rankOne (schurDiagonal a b c x) ![Real.sqrt a, Real.sqrt b, Real.sqrt c]

/-- Complete nonsingular-diagonal formula on the entire original real
domain. The scalar F may be positive, negative or zero. -/
theorem schur_nonsingular (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (_hx : 0 < x) (_hxa : x < a)
    (hk : ∀ i, schurDiagonal a b c x i ≠ 0) :
    negativeCount (schur a b c x) = #{i | schurDiagonal a b c x i < 0} +
      (if 1-∑ i, ![a,b,c] i / schurDiagonal a b c x i < 0 then 1 else 0) ∧
    zeroCount (schur a b c x) =
      (if 1-∑ i, ![a,b,c] i / schurDiagonal a b c x i = 0 then 1 else 0) := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hs : ∀ i : Fin 3, (![Real.sqrt a,Real.sqrt b,Real.sqrt c] i)^2 = ![a,b,c] i := by
    intro i
    fin_cases i <;> simp [Real.sq_sqrt, ha.le, hb.le, hc.le]
  simpa only [schur, hs] using
    nonsingular_diagonal (schurDiagonal a b c x) ![Real.sqrt a,Real.sqrt b,Real.sqrt c] hk

/-- The complete singular-diagonal source formula at every allowed x. -/
theorem schur_singular (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (_hx : 0 < x) (_hxa : x < a)
    (hz : ∃ j, schurDiagonal a b c x j = 0) :
    negativeCount (schur a b c x) = #{i | schurDiagonal a b c x i < 0} + 1 ∧
      zeroCount (schur a b c x) + 1 = #{i | schurDiagonal a b c x i = 0} := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  exact singular_diagonal _ _
    (by intro i; fin_cases i <;> simp <;> positivity) hz


open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra

private def pairedShift (a b c x : ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.reindex ((finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin (3+3)).symm)
    (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin (3+3)).symm (symmetric a b c - Matrix.scalar (Fin 6) x)

private def eliminatePair (a b c x : ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks 1 0
    (diagonal (fun i => (Real.sqrt a*Real.sqrt b*Real.sqrt c)/(![a,b,c] i-x))) 1

private theorem pair_det (a b c x : ℝ) : (eliminatePair a b c x).det = 1 := by
  unfold eliminatePair
  rw [Matrix.det_fromBlocks_zero₁₂]
  simp

private theorem pair_hermitian (a b c x : ℝ) : (pairedShift a b c x).IsHermitian := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [pairedShift, symmetric, conjTranspose_apply, Matrix.submatrix_apply,
      Matrix.scalar, Matrix.diagonal_apply, finSumFinEquiv, Matrix.reindex_apply]

private theorem pair_elimination (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hax : a-x ≠ 0) (hbx : b-x ≠ 0) (hcx : c-x ≠ 0) :
    (eliminatePair a b c x)ᴴ * pairedShift a b c x * eliminatePair a b c x =
      fromBlocks (schur a b c x) 0 0 (diagonal (fun i => ![a,b,c] i-x)) := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have h0 := hax
  have h1 := hbx
  have h2 := hcx
  have hp : (Real.sqrt a*Real.sqrt b*Real.sqrt c)^2 = a*b*c := by
    rw [mul_pow,mul_pow,Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc.le]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals fin_cases i <;> fin_cases j
  all_goals norm_num [eliminatePair,pairedShift,Matrix.mul_apply,Fintype.sum_sum_type,
    Fin.sum_univ_three,Matrix.fromBlocks,symmetric,schur,schurDiagonal,rankOne,
    Matrix.vecMulVec,conjTranspose_apply,Matrix.submatrix_apply,Matrix.scalar,
    Matrix.diagonal_apply,Matrix.one_apply,finSumFinEquiv,Matrix.reindex_apply]
  all_goals try field_simp [h0,h1,h2,ha.ne',hb.ne',hc.ne']
  all_goals ring_nf
  all_goals simp [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc.le]
  all_goals ring

set_option maxHeartbeats 4000000 in
/-- The actual six-cell shifted operator has exactly the negative and zero
multiplicities of its full three-cell Schur complement. -/
theorem six_support_shift (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hxa : x < a) :
    negativeCount (symmetric a b c - Matrix.scalar (Fin 6) x) = negativeCount (schur a b c x) ∧
    zeroCount (symmetric a b c - Matrix.scalar (Fin 6) x) = zeroCount (schur a b c x) := by
  have h := congruence_counts (pair_hermitian a b c x) (eliminatePair a b c x)
    (by rw [pair_det]; exact isUnit_one)
  rw [pair_elimination a b c x ha hab hbc
    (sub_pos.mpr hxa).ne' (sub_pos.mpr (hxa.trans_le hab)).ne'
    (sub_pos.mpr ((hxa.trans_le hab).trans_le hbc)).ne'] at h
  have hd := diagonal_counts (fun i : Fin 3 => ![a,b,c] i-x)
  have hn : #{i : Fin 3 | ![a,b,c] i-x < 0} = 0 := by
    have h : ∀ i : Fin 3, ¬ (![a,b,c] i-x < 0) := by
      intro i
      fin_cases i <;> simp <;> linarith
    simp only [h, Finset.filter_false, Finset.card_empty]
  have hz : #{i : Fin 3 | ![a,b,c] i-x = 0} = 0 := by
    have h : ∀ i : Fin 3, ¬ (![a,b,c] i-x = 0) := by
      intro i
      fin_cases i <;> simp <;> linarith
    simp only [h, Finset.filter_false, Finset.card_empty]
  have hb := block_counts (schur a b c x) (diagonal (fun i => ![a,b,c] i-x))
  have hnD : negativeCount (diagonal (fun i : Fin 3 => ![a,b,c] i-x)) = 0 := hd.1.trans hn
  have hzD : zeroCount (diagonal (fun i : Fin 3 => ![a,b,c] i-x)) = 0 := hd.2.trans hz
  have hbn : negativeCount (fromBlocks (schur a b c x) 0 0
      (diagonal (fun i : Fin 3 => ![a,b,c] i-x))) = negativeCount (schur a b c x) :=
    hb.1.trans ((congrArg (fun n : ℕ => negativeCount (schur a b c x)+n) hnD).trans
      (Nat.add_zero _))
  have hbz : zeroCount (fromBlocks (schur a b c x) 0 0
      (diagonal (fun i : Fin 3 => ![a,b,c] i-x))) = zeroCount (schur a b c x) :=
    hb.2.trans ((congrArg (fun n : ℕ => zeroCount (schur a b c x)+n) hzD).trans
      (Nat.add_zero _))
  have heq : (pairedShift a b c x).charpoly =
      (symmetric a b c-Matrix.scalar (Fin 6) x).charpoly := by
    unfold pairedShift
    exact Matrix.charpoly_reindex ((finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin (3+3)).symm)
      (symmetric a b c-Matrix.scalar (Fin 6) x)
  have hnr := congrArg (fun p : Polynomial ℝ => p.roots.countP (fun t => t < 0)) heq
  have hzr := congrArg (fun p : Polynomial ℝ => p.roots.countP (fun t => t = 0)) heq
  exact ⟨hnr.symm.trans (h.1.symm.trans hbn), hzr.symm.trans (h.2.symm.trans hbz)⟩

/-- Full shifted inertia at every nonsingular pair-support pivot. It includes
all shifts above, between and below the three parameters. -/
theorem shifted_counts (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hax : a-x ≠ 0) (hbx : b-x ≠ 0) (hcx : c-x ≠ 0) :
    negativeCount (symmetric a b c-Matrix.scalar (Fin 6) x) =
      negativeCount (schur a b c x)+#{i : Fin 3 | ![a,b,c] i-x < 0} ∧
    zeroCount (symmetric a b c-Matrix.scalar (Fin 6) x) =
      zeroCount (schur a b c x)+#{i : Fin 3 | ![a,b,c] i-x = 0} := by
  have h := congruence_counts (pair_hermitian a b c x) (eliminatePair a b c x)
    (by rw [pair_det]; exact isUnit_one)
  rw [pair_elimination a b c x ha hab hbc hax hbx hcx] at h
  have hb := block_counts (schur a b c x) (diagonal (fun i : Fin 3 => ![a,b,c] i-x))
  have hd := diagonal_counts (fun i : Fin 3 => ![a,b,c] i-x)
  have heq : (pairedShift a b c x).charpoly =
      (symmetric a b c-Matrix.scalar (Fin 6) x).charpoly := by
    unfold pairedShift
    exact Matrix.charpoly_reindex ((finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin (3+3)).symm) _
  have hn := congrArg (fun p : Polynomial ℝ => p.roots.countP (fun t => t < 0)) heq
  have hz := congrArg (fun p : Polynomial ℝ => p.roots.countP (fun t => t = 0)) heq
  rw [hb.1,hd.1] at h
  rw [hb.2,hd.2] at h
  exact ⟨hn.symm.trans h.1.symm,hz.symm.trans h.2.symm⟩

theorem symmetric_charpoly (a b c : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    (symmetric a b c).charpoly = X * quintic a b c := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hg := quotient_geometry a b c ha hb hc
  let D := diagonal (rootWeights a b c)
  let E := diagonal (fun i => (rootWeights a b c i)⁻¹)
  have hpos (i : Fin 6) : 0 < rootWeights a b c i := by
    fin_cases i <;> simp [rootWeights] <;> positivity
  have hED : E*D = 1 := by
    simp only [E,D,diagonal_mul_diagonal]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hpos i).ne'
  have hs : (symmetric a b c).charpoly = (quotient a b c).charpoly := by
    rw [hg.2.2.1,Matrix.charpoly_mul_comm,← Matrix.mul_assoc]
    change (E*D*(quotient a b c).submatrix supportPermutation supportPermutation).charpoly = _
    rw [hED,Matrix.one_mul]
    exact Matrix.charpoly_reindex supportPermutation.symm _
  rw [hs]
  change (D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial.quotientOver a b c).charpoly = _
  rw [D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial.charpoly_zero_factor,
    quintic_eq_reduced]

/-- Counts on the actual quotient characteristic multiset, retaining algebraic multiplicities. -/
def positiveBelow (a b c x : ℝ) : ℕ :=
  (quotient a b c).charpoly.roots.countP (fun t => 0 < t ∧ t < x)

/-- Multiplicity at the specified real value in the actual quotient. -/
def multiplicity (a b c x : ℝ) : ℕ :=
  (quotient a b c).charpoly.roots.countP (fun t => t = x)

/-- Complete source count, including all mixed and singular Schur cases:
the single zero eigenvalue is subtracted exactly once. -/
theorem positive_root_counts (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hx : 0 < x) (hxa : x < a) :
    positiveBelow a b c x + 1 = negativeCount (schur a b c x) ∧
    multiplicity a b c x = zeroCount (schur a b c x) := by
  classical
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hs := symmetric_charpoly a b c ha hab hbc
  have hq : (quotient a b c).charpoly = X * quintic a b c := by
    change (D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial.quotientOver a b c).charpoly = _
    rw [D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial.charpoly_zero_factor,
      quintic_eq_reduced]
  have hnonzero : (X * quintic a b c : Polynomial ℝ) ≠ 0 := hq ▸ (quotient a b c).charpoly_monic.ne_zero
  have hr : (symmetric a b c).charpoly.roots = 0 ::ₘ (quintic a b c).roots := by
    rw [hs,Polynomial.roots_mul hnonzero,Polynomial.roots_X]
    simp
  have hrq : (quotient a b c).charpoly.roots = 0 ::ₘ (quintic a b c).roots := by simpa only [hs,hq] using hr
  have hzero : (quintic a b c).eval 0 ≠ 0 := by
    have hp : 0 < a*b*c*(a+b+c)*(a+b+c+a*b+a*c+b*c) := by positivity
    have he : (quintic a b c).eval 0 = -(a*b*c*(a+b+c)*(a+b+c+a*b+a*c+b*c)) := by
      simp [quintic]
      ring
    rw [he]
    exact neg_ne_zero.mpr hp.ne'
  have hpositive : ∀ t ∈ (quintic a b c).roots, 0 < t := by
    intro t ht
    have hps := (quotient_geometry a b c ha hb hc).2.1
    have hm : t ∈ (symmetric a b c).charpoly.roots := by rw [hr]; exact Multiset.mem_cons_of_mem ht
    rw [hps.1.roots_charpoly_eq_eigenvalues] at hm
    obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp hm
    have hn := hps.eigenvalues_nonneg i
    have hz : hps.1.eigenvalues i ≠ 0 := by
      intro he
      have heval := (Polynomial.mem_roots (mul_ne_zero_iff.mp hnonzero).2).mp ht
      change (quintic a b c).eval (hps.1.eigenvalues i) = 0 at heval
      rw [he] at heval
      exact hzero heval
    exact lt_of_le_of_ne hn (Ne.symm hz)
  have hshift : (symmetric a b c-Matrix.scalar (Fin 6) x).charpoly.roots =
      (symmetric a b c).charpoly.roots.map (fun t => t-x) := by
    rw [Matrix.charpoly_sub_scalar]
    simpa using Polynomial.roots_comp_C_mul_X_add_C (symmetric a b c).charpoly 1 x isUnit_one
  have hp : positiveBelow a b c x = (quintic a b c).roots.countP (fun t => t < x) := by
    rw [positiveBelow,hrq,Multiset.countP_cons_of_neg _ (by simp)]
    apply Multiset.countP_congr rfl
    intro t ht
    simp [hpositive t ht]
  have hm : multiplicity a b c x = (quintic a b c).roots.countP (fun t => t = x) := by
    rw [multiplicity,hrq]
    exact Multiset.countP_cons_of_neg (p := fun t : ℝ => t = x) _ hx.ne
  have hn : negativeCount (symmetric a b c-Matrix.scalar (Fin 6) x) =
      (quintic a b c).roots.countP (fun t => t < x) + 1 := by
    unfold negativeCount
    rw [hshift,hr,Multiset.map_cons,Multiset.countP_cons_of_pos _ (by simpa using hx)]
    simp only [Multiset.countP_map,sub_neg,← Multiset.countP_eq_card_filter]
  have hz : zeroCount (symmetric a b c-Matrix.scalar (Fin 6) x) =
      (quintic a b c).roots.countP (fun t => t = x) := by
    unfold zeroCount
    rw [hshift,hr,Multiset.map_cons,Multiset.countP_cons_of_neg _ (by simpa using hx.ne')]
    simp only [Multiset.countP_map,sub_eq_zero,← Multiset.countP_eq_card_filter]
  have hb := six_support_shift a b c x ha hab hbc hxa
  rw [hp,hm]
  exact ⟨hn.symm.trans hb.1,hz.symm.trans hb.2⟩

#print axioms six_support_shift
#print axioms positive_root_counts
#print axioms nonsingular_diagonal
#print axioms singular_diagonal
#print axioms schur_nonsingular
#print axioms schur_singular
end D5.S3.Combinatorics.SpectralGraph.SixSupportInertia
