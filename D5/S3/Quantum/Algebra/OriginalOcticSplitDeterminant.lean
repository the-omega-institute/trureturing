/- GID: D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/OriginalOcticSplitDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible; premises=D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.coefficient_zero_count
   digest: The original labeled octic window has an absolutely irreducible split determinant. -/

module

public import D5.S3.Quantum.Algebra.SplitQuarticIrreducibility
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! The split determinant of the window with exponents zero, one, three and four. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant

open MvPolynomial Finset Matrix
open D5.S3.Quantum.Algebra.SplitQuarticIrreducibility
open scoped Classical

variable {k : Type*} [Field k] [CharZero k]

def coefficientMask : ℕ → ℤ
  | 15 => 1
  | 23 => -2
  | 71 => 2
  | 135 => -1
  | 43 => -2
  | 75 => -1
  | 139 => 2
  | 51 => 4
  | 83 => -2
  | 163 => -2
  | 195 => 1
  | 29 => 2
  | 45 => -1
  | 77 => -2
  | 53 => -2
  | 149 => 2
  | 101 => 2
  | 165 => 1
  | 197 => -2
  | 89 => 2
  | 153 => -4
  | 105 => 1
  | 169 => 2
  | 113 => -2
  | 209 => 2
  | 225 => -1
  | 30 => -1
  | 46 => 2
  | 142 => -2
  | 86 => 2
  | 150 => 1
  | 102 => -4
  | 166 => 2
  | 58 => -2
  | 90 => 1
  | 154 => 2
  | 106 => 2
  | 202 => -2
  | 178 => -2
  | 210 => -1
  | 226 => 2
  | 60 => 1
  | 92 => -2
  | 172 => -2
  | 204 => 4
  | 116 => 2
  | 180 => -1
  | 212 => -2
  | 120 => -1
  | 184 => 2
  | 232 => -2
  | 240 => 1
  | _ => 0

def integerCoefficient (I : Finset (Fin 8)) : ℤ :=
  coefficientMask (∑ i ∈ I, 2 ^ i.val)

def fourSets : Finset (Finset (Fin 8)) :=
  (univ : Finset (Fin 8)).powersetCard 4

private lemma fourSets_explicit : fourSets = {
    {0, 1, 2, 3},
    {0, 1, 2, 4},
    {0, 1, 2, 5},
    {0, 1, 2, 6},
    {0, 1, 2, 7},
    {0, 1, 3, 4},
    {0, 1, 3, 5},
    {0, 1, 3, 6},
    {0, 1, 3, 7},
    {0, 1, 4, 5},
    {0, 1, 4, 6},
    {0, 1, 4, 7},
    {0, 1, 5, 6},
    {0, 1, 5, 7},
    {0, 1, 6, 7},
    {0, 2, 3, 4},
    {0, 2, 3, 5},
    {0, 2, 3, 6},
    {0, 2, 3, 7},
    {0, 2, 4, 5},
    {0, 2, 4, 6},
    {0, 2, 4, 7},
    {0, 2, 5, 6},
    {0, 2, 5, 7},
    {0, 2, 6, 7},
    {0, 3, 4, 5},
    {0, 3, 4, 6},
    {0, 3, 4, 7},
    {0, 3, 5, 6},
    {0, 3, 5, 7},
    {0, 3, 6, 7},
    {0, 4, 5, 6},
    {0, 4, 5, 7},
    {0, 4, 6, 7},
    {0, 5, 6, 7},
    {1, 2, 3, 4},
    {1, 2, 3, 5},
    {1, 2, 3, 6},
    {1, 2, 3, 7},
    {1, 2, 4, 5},
    {1, 2, 4, 6},
    {1, 2, 4, 7},
    {1, 2, 5, 6},
    {1, 2, 5, 7},
    {1, 2, 6, 7},
    {1, 3, 4, 5},
    {1, 3, 4, 6},
    {1, 3, 4, 7},
    {1, 3, 5, 6},
    {1, 3, 5, 7},
    {1, 3, 6, 7},
    {1, 4, 5, 6},
    {1, 4, 5, 7},
    {1, 4, 6, 7},
    {1, 5, 6, 7},
    {2, 3, 4, 5},
    {2, 3, 4, 6},
    {2, 3, 4, 7},
    {2, 3, 5, 6},
    {2, 3, 5, 7},
    {2, 3, 6, 7},
    {2, 4, 5, 6},
    {2, 4, 5, 7},
    {2, 4, 6, 7},
    {2, 5, 6, 7},
    {3, 4, 5, 6},
    {3, 4, 5, 7},
    {3, 4, 6, 7},
    {3, 5, 6, 7},
    {4, 5, 6, 7}} := by
  decide +kernel

/-- The number of absent squarefree quartic coefficients in the exact normalized equation. -/
lemma coefficient_zero_count :
    (fourSets.filter (fun I => integerCoefficient I = 0)).card = 18 := by
  decide +kernel

private def quartic : MvPolynomial (Fin 8) k :=
  ∑ I ∈ fourSets, monomial (squareExponent I) (integerCoefficient I : k)

private lemma square_monomial (I : Finset (Fin 8)) (c : k) :
    monomial (squareExponent I) c = C c * ∏ i ∈ I, (X i : MvPolynomial (Fin 8) k) := by
  simp [squareExponent, monomial_sum_index, ← X_pow_eq_monomial]

private lemma square_exponent_injective : Function.Injective squareExponent := by
  intro I J h
  ext i
  have hi := DFunLike.congr_fun h i
  simp only [square_exponent_apply] at hi
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp_all

private lemma quartic_coefficient (I : Finset (Fin 8)) (hi : I ∈ fourSets) :
    (quartic : MvPolynomial (Fin 8) k).coeff (squareExponent I) = integerCoefficient I := by
  classical
  simp only [quartic, coeff_sum, coeff_monomial]
  rw [sum_eq_single_of_mem I hi]
  · simp
  · intro J _ hJI
    rw [if_neg (fun h => hJI (square_exponent_injective h))]

private lemma quartic_homogeneous : (quartic : MvPolynomial (Fin 8) k).IsHomogeneous 4 := by
  apply IsHomogeneous.sum
  intro I hi
  exact isHomogeneous_monomial _ ((square_exponent_degree I).trans
    (mem_powersetCard.mp hi).2)

private lemma quartic_multiaffine (i : Fin 8) :
    (quartic : MvPolynomial (Fin 8) k).degreeOf i ≤ 1 := by
  apply (degreeOf_sum_le i fourSets _).trans
  apply Finset.sup_le
  intro I _
  by_cases hc : (integerCoefficient I : k) = 0
  · simp [hc]
  · rw [degreeOf_monomial_eq _ _ hc, square_exponent_apply]
    split_ifs <;> omega

/-- The four powers, in the original order of the rational basis of X. -/
def windowExponent : Fin 4 → ℕ := ![0, 1, 3, 4]

/-- Rows retain the fixed original embedding labels, without a row permutation. -/
def originalWindowMatrix (a z : k) : Matrix (Fin 8) (Fin 4) k :=
  fun i j => (a * z ^ i.val) ^ windowExponent j

/-- The two four-column blocks, with the original eight row labels. -/
def splitMatrix (B : Matrix (Fin 8) (Fin 4) k) :
    Matrix (Fin 8) (Fin 8) (MvPolynomial (Fin 8) k) :=
  fun i j => if h : j.val < 4 then C (B i ⟨j.val, h⟩)
    else X i * C (B i ⟨j.val - 4, by omega⟩)

/-- The exact eight-variable determinant [B | diag(q) B]. -/
def splitDeterminant (B : Matrix (Fin 8) (Fin 4) k) : MvPolynomial (Fin 8) k :=
  det (splitMatrix B)

private def normalizedRows (s : k) : Matrix (Fin 4) (Fin 4) k :=
  !![-1, -s, 2, s; -s, 1, s, 0; 0, -s, 1, s; -s, 2, s, -1]

private def reducedMatrix (s : k) : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 8) k) :=
  fun i j => C (normalizedRows s i j) * (X (Fin.natAdd 4 i) - X (Fin.castAdd 4 j))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma reduced_determinant (s : k) (hs : s ^ 2 = -2) :
    det (reducedMatrix s) = (quartic : MvPolynomial (Fin 8) k) := by
  have hS : (C s : MvPolynomial (Fin 8) k) ^ 2 = -2 := by
    simpa only [map_pow, map_neg, map_ofNat] using
      congrArg (C : k →+* MvPolynomial (Fin 8) k) hs
  have hS4 : (C s : MvPolynomial (Fin 8) k) ^ 4 = 4 := by
    calc
      _ = ((C s : MvPolynomial (Fin 8) k) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hS]; norm_num
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.det_fin_zero, Matrix.submatrix_apply, reducedMatrix, normalizedRows]
  simp (disch := decide) only [quartic, fourSets_explicit, Finset.sum_insert,
    Finset.sum_singleton, Finset.sum_empty]
  simp only [square_monomial]
  norm_num [integerCoefficient, coefficientMask, map_ofNat,
    windowExponent,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val', Fin.succAbove]
  ring_nf
  all_goals simp only [hS, hS4]
  all_goals ring

private lemma primitive_fourth_power (z : k) (hz : IsPrimitiveRoot z 8) :
    z ^ 4 = -1 := by
  have hsq : (z ^ 4) ^ 2 = 1 := by simpa [← pow_mul] using hz.pow_eq_one
  rcases sq_eq_one_iff.mp hsq with h | h
  · have hd := hz.dvd_of_pow_eq_one 4 h
    norm_num at hd
  · exact h

private lemma fourth_power_reduction (z : k) (hz : z ^ 4 = -1) (n : ℕ) :
    z ^ n = z ^ (n % 4) * (-1) ^ (n / 4) := by
  conv_lhs => rw [← Nat.mod_add_div n 4]
  rw [pow_add, pow_mul, hz]

private def topRows (a z : k) : Matrix (Fin 4) (Fin 4) k :=
  fun i j => (a * z ^ i.val) ^ windowExponent j

private def bottomRows (a z : k) : Matrix (Fin 4) (Fin 4) k :=
  fun i j => (a * z ^ (4 + i.val)) ^ windowExponent j

set_option maxHeartbeats 1000000 in
private lemma bottom_rows_identity (a z : k) (hz : z ^ 4 = -1) :
    bottomRows a z = normalizedRows (z + z ^ 3) * topRows a z := by
  have h5 : z ^ 5 = -z := by
    convert fourth_power_reduction z hz 5 using 1 <;> norm_num
  have h6 : z ^ 6 = -(z ^ 2) := by
    convert fourth_power_reduction z hz 6 using 1 <;> norm_num
  have h7 : z ^ 7 = -(z ^ 3) := by
    convert fourth_power_reduction z hz 7 using 1 <;> norm_num
  have h8 : z ^ 8 = 1 := by
    convert fourth_power_reduction z hz 8 using 1 <;> norm_num
  have h9 : z ^ 9 = z := by
    convert fourth_power_reduction z hz 9 using 1 <;> norm_num
  have h12 : z ^ 12 = -1 := by
    convert fourth_power_reduction z hz 12 using 1 <;> norm_num
  have h15 : z ^ 15 = -(z ^ 3) := by
    convert fourth_power_reduction z hz 15 using 1 <;> norm_num
  have h16 : z ^ 16 = 1 := by
    convert fourth_power_reduction z hz 16 using 1 <;> norm_num
  have h18 : z ^ 18 = z ^ 2 := by
    convert fourth_power_reduction z hz 18 using 1 <;> norm_num
  have h20 : z ^ 20 = -1 := by
    convert fourth_power_reduction z hz 20 using 1 <;> norm_num
  have h21 : z ^ 21 = -z := by
    convert fourth_power_reduction z hz 21 using 1 <;> norm_num
  have h24 : z ^ 24 = 1 := by
    convert fourth_power_reduction z hz 24 using 1 <;> norm_num
  have h28 : z ^ 28 = -1 := by
    convert fourth_power_reduction z hz 28 using 1 <;> norm_num
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [bottomRows, topRows, normalizedRows, windowExponent, Matrix.mul_apply,
      Fin.sum_univ_succ, mul_pow, ← pow_mul, hz, h5, h6, h7, h8, h9, h12,
      h15, h16, h18, h20, h21, h24, h28] <;>
    ring_nf <;> simp only [hz, h5, h6, h7, h8, h9, h12, h15, h16, h18, h20,
      h21, h24, h28] <;> ring

set_option maxHeartbeats 1000000 in
private lemma top_rows_det_square (a z : k) (ha : a ^ 8 = 2) (hz : z ^ 4 = -1) :
    (det (topRows a z)) ^ 2 = 128 := by
  have h6 : z ^ 6 = -(z ^ 2) := by
    convert fourth_power_reduction z hz 6 using 1 <;> norm_num
  have h9 : z ^ 9 = z := by
    convert fourth_power_reduction z hz 9 using 1 <;> norm_num
  have h12 : z ^ 12 = -1 := by
    convert fourth_power_reduction z hz 12 using 1 <;> norm_num
  have h10 : z ^ 10 = z ^ 2 := by
    convert fourth_power_reduction z hz 10 using 1 <;> norm_num
  have h11 : z ^ 11 = z ^ 3 := by
    convert fourth_power_reduction z hz 11 using 1 <;> norm_num
  have h14 : z ^ 14 = -(z ^ 2) := by
    convert fourth_power_reduction z hz 14 using 1 <;> norm_num
  have hdet : det (topRows a z) = a ^ 8 * (4 * z - 4 * z ^ 3) := by
    simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_zero,
      Matrix.submatrix_apply]
    norm_num [topRows, windowExponent, mul_pow, ← pow_mul, hz, h6, h9, h12,
      Fin.succAbove]
    ring_nf
    simp only [hz, h6, h9, h10, h11, h12, h14]
    ring
  rw [hdet, ha]
  calc
    (2 * (4 * z - 4 * z ^ 3)) ^ 2 = 64 * (z ^ 2 - 2 * z ^ 4 + z ^ 6) := by ring
    _ = 128 := by rw [hz, h6]; ring

private lemma split_determinant_blocks (a z : k) :
    splitDeterminant (originalWindowMatrix a z) = det (Matrix.fromBlocks
      ((topRows a z).map C)
      (Matrix.diagonal (fun i : Fin 4 => (X (Fin.castAdd 4 i) : MvPolynomial (Fin 8) k)) *
        (topRows a z).map C)
      ((bottomRows a z).map C)
      (Matrix.diagonal (fun i : Fin 4 => (X (Fin.natAdd 4 i) : MvPolynomial (Fin 8) k)) *
        (bottomRows a z).map C)) := by
  change det (splitMatrix (originalWindowMatrix a z)) = _
  rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8)
    (splitMatrix (originalWindowMatrix a z))]
  congr 1
  ext i j : 2
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [splitMatrix, originalWindowMatrix, topRows, Matrix.submatrix_apply,
        finSumFinEquiv, Fin.castAdd, Fin.natAdd]
    | inr j => simp [splitMatrix, originalWindowMatrix, topRows, Matrix.submatrix_apply,
        finSumFinEquiv, Fin.castAdd, Fin.natAdd, Matrix.diagonal_mul]
  | inr i =>
    cases j with
    | inl j => simp [splitMatrix, originalWindowMatrix, bottomRows, Matrix.submatrix_apply,
        finSumFinEquiv, Fin.castAdd, Fin.natAdd, Nat.add_comm]
    | inr j => simp [splitMatrix, originalWindowMatrix, bottomRows, Matrix.submatrix_apply,
        finSumFinEquiv, Fin.castAdd, Fin.natAdd, Matrix.diagonal_mul, Nat.add_comm]

private lemma original_determinant_formula (a z : k)
    (ha : a ^ 8 = 2) (hz : IsPrimitiveRoot z 8) :
    splitDeterminant (originalWindowMatrix a z) = C 128 * quartic := by
  have hz4 := primitive_fourth_power z hz
  have hs : (z + z ^ 3) ^ 2 = -2 := by
    have h6 : z ^ 6 = -(z ^ 2) := by
      convert fourth_power_reduction z hz4 6 using 1 <;> norm_num
    calc
      _ = z ^ 2 + 2 * z ^ 4 + z ^ 6 := by ring
      _ = -2 := by rw [hz4, h6]; ring
  let U := (topRows a z).map (C : k →+* MvPolynomial (Fin 8) k)
  let R := (normalizedRows (z + z ^ 3)).map (C : k →+* MvPolynomial (Fin 8) k)
  let L := Matrix.diagonal (fun i : Fin 4 => (X (Fin.castAdd 4 i) : MvPolynomial (Fin 8) k))
  let V := Matrix.diagonal (fun i : Fin 4 => (X (Fin.natAdd 4 i) : MvPolynomial (Fin 8) k))
  have hb : (bottomRows a z).map C = R * U := by
    rw [bottom_rows_identity a z hz4]
    exact Matrix.map_mul
  rw [split_determinant_blocks, hb]
  change det (Matrix.fromBlocks U (L * U) (R * U) (V * (R * U))) = _
  have hfac : Matrix.fromBlocks U (L * U) (R * U) (V * (R * U)) =
      Matrix.fromBlocks 1 L R (V * R) * Matrix.fromBlocks U 0 0 U := by
    simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc]
  rw [hfac, Matrix.det_mul, Matrix.det_fromBlocks_one₁₁,
    Matrix.det_fromBlocks_zero₁₂]
  have hred : V * R - R * L = reducedMatrix (z + z ^ 3) := by
    ext i j : 2
    simp only [V, R, L, reducedMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.sub_apply, Matrix.map_apply]
    ring
  rw [hred, reduced_determinant _ hs]
  have hdet : det U * det U = C (128 : k) := by
    dsimp [U]
    have hmap : det ((topRows a z).map (C : k →+* MvPolynomial (Fin 8) k)) =
        C (det (topRows a z)) := (RingHom.map_det C (topRows a z)).symm
    rw [hmap, ← map_mul, ← pow_two,
      top_rows_det_square a z ha hz4]
  rw [hdet]
  ring

/-- Homogeneity, multiaffinity and exactly eighteen zero coefficients are
derived from the original alpha/zeta rows, without a coefficient hypothesis. -/
theorem original_split_determinant_structure (a z : k)
    (ha : a ^ 8 = 2) (hz : IsPrimitiveRoot z 8) :
    (splitDeterminant (originalWindowMatrix a z)).IsHomogeneous 4 ∧
    (∀ i, (splitDeterminant (originalWindowMatrix a z)).degreeOf i ≤ 1) ∧
    (fourSets.filter (fun I => (splitDeterminant (originalWindowMatrix a z)).coeff
      (squareExponent I) = 0)).card = 18 := by
  rw [original_determinant_formula a z ha hz]
  refine ⟨quartic_homogeneous.C_mul 128, ?_, ?_⟩
  · intro i
    exact (degreeOf_C_mul_le _ i 128).trans (quartic_multiaffine i)
  · have he : (fourSets.filter (fun I => (C 128 * (quartic : MvPolynomial (Fin 8) k)).coeff
        (squareExponent I) = 0)) = fourSets.filter (fun I => integerCoefficient I = 0) := by
      apply filter_congr
      intro I hi
      rw [coeff_C_mul, quartic_coefficient I hi]
      simp only [mul_eq_zero, show (128 : k) ≠ 0 by norm_num, false_or, Int.cast_eq_zero]
    rw [he, coefficient_zero_count]

/-- The embedding matrix of the original rational power basis. -/
def originalFieldWindowMatrix {D : Type*} [Field D] (alpha : D)
    (sigma : Fin 8 → D →+* k) : Matrix (Fin 8) (Fin 4) k :=
  fun i j => sigma i (alpha ^ windowExponent j)

/-- With the original field element and embedding labels preserved, the split
determinant is irreducible over every characteristic-zero coefficient field. -/
theorem original_split_determinant_irreducible {D : Type*} [Field D]
    (alpha : D) (sigma : Fin 8 → D →+* k) (z : k)
    (ha : alpha ^ 8 = 2) (hz : IsPrimitiveRoot z 8)
    (hlabels : ∀ i, sigma i alpha = sigma 0 alpha * z ^ i.val) :
    Irreducible (splitDeterminant (originalFieldWindowMatrix alpha sigma)) := by
  have hroot : (sigma 0 alpha) ^ 8 = 2 := by
    simpa only [map_pow, map_ofNat] using congrArg (sigma 0) ha
  have hB : originalFieldWindowMatrix alpha sigma = originalWindowMatrix (sigma 0 alpha) z := by
    ext i j : 2
    change sigma i (alpha ^ windowExponent j) =
      (sigma 0 alpha * z ^ i.val) ^ windowExponent j
    rw [map_pow, hlabels i]
  rw [hB]
  obtain ⟨hh, hm, hc⟩ := original_split_determinant_structure (sigma 0 alpha) z hroot hz
  apply irreducible_of_fewer_than_twenty_zeros _ hh hm
  change (fourSets.filter _).card < 20
  rw [hc]
  norm_num

end D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant
