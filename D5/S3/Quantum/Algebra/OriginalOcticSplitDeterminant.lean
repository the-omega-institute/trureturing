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

private def coefficientMask : ℕ → ℤ
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

private def integerCoefficient (I : Finset (Fin 8)) : ℤ :=
  coefficientMask (∑ i ∈ I, 2 ^ i.val)

private def fourSets : Finset (Finset (Fin 8)) :=
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

private lemma square_exponent_injective : Function.Injective squareExponent := by
  intro I J h
  ext i
  have hi := DFunLike.congr_fun h i
  simpa only [square_exponent_apply, ite_eq_ite_iff, one_ne_zero, zero_ne_one,
    and_false, or_false, and_true, true_and] using hi

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
  apply sup_le
  intro I _
  by_cases hc : (integerCoefficient I : k) = 0
  · simp [hc]
  · rw [degreeOf_monomial_eq _ _ hc, square_exponent_apply]
    split_ifs <;> omega

private lemma quartic_irreducible : Irreducible (quartic : MvPolynomial (Fin 8) k) := by
  apply irreducible_of_fewer_than_twenty_zeros _ quartic_homogeneous quartic_multiaffine
  have he : (fourSets.filter (fun I => (quartic : MvPolynomial (Fin 8) k).coeff
      (squareExponent I) = 0)) = fourSets.filter (fun I => integerCoefficient I = 0) := by
    apply filter_congr
    intro I hi
    rw [quartic_coefficient I hi]
    exact Int.cast_eq_zero
  change (fourSets.filter _).card < 20
  rw [he, coefficient_zero_count]
  norm_num

/-- The four powers, in the original order of the rational basis of X. -/
def windowExponent : Fin 4 → ℕ := ![0, 1, 3, 4]

/-- Rows retain the fixed original embedding labels, without a row permutation. -/
def originalWindowMatrix (a z : k) : Matrix (Fin 8) (Fin 4) k :=
  fun i j => (a * z ^ i.val) ^ windowExponent j

/-- The exact eight-variable determinant [B | diag(q) B]. -/
def splitDeterminant (B : Matrix (Fin 8) (Fin 4) k) : MvPolynomial (Fin 8) k :=
  det (fun i j : Fin 8 => if h : j.val < 4 then C (B i ⟨j.val, h⟩)
    else X i * C (B i ⟨j.val - 4, by omega⟩))

private def normalizedRows (s : k) : Matrix (Fin 4) (Fin 4) k :=
  !![-1, -s, 2, s; -s, 1, s, 0; 0, -s, 1, s; -s, 2, s, -1]

private def reducedMatrix (s : k) : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 8) k) :=
  fun i j => C (normalizedRows s i j) * (X (Fin.natAdd 4 i) - X (Fin.castAdd 4 j))

private lemma reduced_determinant (s : k) (hs : s ^ 2 = -2) :
    det (reducedMatrix s) = (quartic : MvPolynomial (Fin 8) k) := by
  have hS : (C s : MvPolynomial (Fin 8) k) ^ 2 = -2 := by
    simpa using congrArg (C : k →+* MvPolynomial (Fin 8) k) hs
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix_apply, reducedMatrix, normalizedRows]
  norm_num [quartic, fourSets_explicit, integerCoefficient, coefficientMask,
    squareExponent, monomial_sum_index, monomial_single, windowExponent,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val', Fin.succAbove]
  ring_nf
  all_goals simp only [hS]
  all_goals ring

end D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant
