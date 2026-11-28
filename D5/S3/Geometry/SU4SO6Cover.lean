/- GID: D5/S3/Geometry/SU4SO6Cover
   generality: G
   mirror-B: none(waiver:covered-by-pati-salam-unification4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The second compound of a determinant-one unitary matrix on four complex coordinates restricts to a real orthogonal action on the Hodge real form. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Omega original.

The second compound of a determinant-one unitary matrix on four complex
coordinates restricts to a real orthogonal action on the Hodge real form. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexConjugate Matrix

namespace OmegaMath.SU4SO6Cover

abbrev C4 := Matrix (Fin 4) (Fin 4) ℂ
abbrev C6 := Matrix (Fin 6) (Fin 6) ℂ
abbrev R6 := Matrix (Fin 6) (Fin 6) ℝ
abbrev SU4 := Matrix.specialUnitaryGroup (Fin 4) ℂ

private def first : Fin 6 → Fin 4 := ![0, 0, 0, 2, 1, 1]
private def second : Fin 6 → Fin 4 := ![1, 2, 3, 3, 3, 2]

/-- Second compound in the ordered basis 01, 02, 03, 23, 13, 12. -/
def exteriorSquare (A : C4) : C6 := fun i j =>
  A (first i) (first j) * A (second i) (second j) -
    A (first i) (second j) * A (second i) (first j)

private theorem compound_mul (A B : C4) :
    exteriorSquare (A * B) = exteriorSquare A * exteriorSquare B := by
  ext i j
  simp [exteriorSquare, Matrix.mul_apply, Fin.sum_univ_succ, first, second]
  ring

private theorem compound_diagonal (d : Fin 4 → ℂ) :
    exteriorSquare (diagonal d) = diagonal (fun i => d (first i) * d (second i)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [exteriorSquare, first, second, diagonal_apply]

private theorem compound_one : exteriorSquare (1 : C4) = 1 := by
  simpa only [diagonal_one, mul_one] using compound_diagonal (fun _ => 1)

private theorem compound_conjTranspose (A : C4) :
    exteriorSquare Aᴴ = (exteriorSquare A)ᴴ := by
  ext i j
  simp only [exteriorSquare, conjTranspose_apply, star_sub, star_mul]
  ring

private theorem compound_transvection_det {i j : Fin 4} (hij : i ≠ j) (c : ℂ) :
    (exteriorSquare (transvection i j c)).det = 1 := by
  let d : Fin 4 → ℂ := fun k => if k = i then -1 else 1
  have hsq : diagonal d * diagonal d = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [d, hk]
  have hflip (z : ℂ) :
      diagonal d * transvection i j z * diagonal d = transvection i j (-z) := by
    rw [transvection, transvection, Matrix.mul_add, Matrix.add_mul, mul_one, hsq]
    congr 1
    ext k l
    simp only [mul_diagonal, diagonal_mul, d]
    by_cases hk : i = k <;> by_cases hl : j = l <;> simp [hk, hl, eq_comm]
    subst k
    subst l
    simp [hij]
  let f : ℂ → ℂ := fun z => (exteriorSquare (transvection i j z)).det
  have hadd (z w : ℂ) : f (z + w) = f z * f w := by
    dsimp [f]
    rw [← transvection_mul_transvection_same _ _ hij, compound_mul, det_mul]
  have hzero : f 0 = 1 := by simp [f, compound_one]
  have hneg (z : ℂ) : f (-z) = f z := by
    dsimp [f]
    rw [← hflip, compound_mul, compound_mul, det_mul, det_mul]
    have hdet : (exteriorSquare (diagonal d)).det * (exteriorSquare (diagonal d)).det = 1 := by
      rw [← det_mul, ← compound_mul, hsq, compound_one, det_one]
    rw [mul_right_comm, hdet, one_mul]
  change f c = 1
  rw [show c = c / 2 + c / 2 by ring, hadd]
  nth_rw 1 [← hneg (c / 2)]
  rw [← hadd, neg_add_cancel, hzero]

private theorem compound_det (A : C4) : (exteriorSquare A).det = A.det ^ 3 := by
  apply diagonal_transvection_induction (fun B : C4 => (exteriorSquare B).det = B.det ^ 3) A
  · intro d _
    simp [compound_diagonal, det_diagonal, Fin.prod_univ_succ, first, second]
    ring
  · intro t
    rcases t with ⟨i, j, hij, c⟩
    simp [compound_transvection_det hij, det_transvection_of_ne _ _ hij]
  · intro A B hA hB
    simp [compound_mul, det_mul, mul_pow, hA, hB]

/-- The symmetric wedge pairing on two-forms, with orientation 0123. -/
def hodgeMatrix : C6 :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0]

private theorem hodge_transpose : hodgeMatrixᵀ = hodgeMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem hodge_sq : hodgeMatrix * hodgeMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hodgeMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private def pairColumns (i j : Fin 6) : Fin 4 → Fin 4 :=
  ![first i, second i, first j, second j]

private def pairedColumns (A : C4) (i j : Fin 6) : C4 := fun a b => A a (pairColumns i j b)

private theorem det_pairedColumns (A : C4) (i j : Fin 6) :
    (pairedColumns A i j).det =
      ((exteriorSquare A)ᵀ * hodgeMatrix * exteriorSquare A) i j := by
  rw [det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, det_fin_three, pairedColumns,
    submatrix_apply, Fin.zero_succAbove, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
    show (1 : Fin 4).succAbove (2 : Fin 3) = 3 from rfl,
    show (2 : Fin 4).succAbove (1 : Fin 3) = 1 from rfl,
    show (2 : Fin 4).succAbove (2 : Fin 3) = 3 from rfl,
    show (3 : Fin 4).succAbove (1 : Fin 3) = 1 from rfl,
    show (3 : Fin 4).succAbove (2 : Fin 3) = 2 from rfl]
  simp [pairColumns, Matrix.mul_apply, Fin.sum_univ_succ, hodgeMatrix, exteriorSquare,
    first, second]
  ring

private theorem compound_pairing (A : C4) :
    (exteriorSquare A)ᵀ * hodgeMatrix * exteriorSquare A = A.det • hodgeMatrix := by
  ext i j
  have hcol : pairedColumns A i j = A * pairedColumns 1 i j := by
    ext a b
    simp [pairedColumns, Matrix.mul_apply, Matrix.one_apply]
  have hOne : (pairedColumns 1 i j).det = hodgeMatrix i j := by
    simpa only [compound_one, transpose_one, Matrix.one_mul, Matrix.mul_one] using
      det_pairedColumns 1 i j
  rw [← det_pairedColumns, hcol, det_mul, hOne, Matrix.smul_apply, smul_eq_mul]

private theorem compound_unitary (U : SU4) :
    (exteriorSquare (U : C4))ᴴ * exteriorSquare (U : C4) = 1 := by
  rw [← compound_conjTranspose, ← compound_mul]
  have h := Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.prop).1
  rw [← star_eq_conjTranspose, h, compound_one]

private theorem unitary_transpose_conj (U : SU4) :
    (U : C4)ᵀ * (U : C4).map conj = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.prop).1
  simpa [star_eq_conjTranspose, transpose_mul, Matrix.conjTranspose_transpose] using
    congrArg Matrix.transpose h

private theorem compound_hodge_intertwine (U : SU4) :
    hodgeMatrix * exteriorSquare (U : C4) =
      (exteriorSquare (U : C4)).map conj * hodgeMatrix := by
  let C := exteriorSquare (U : C4)
  have hC : C.map conj * Cᵀ = 1 := by
    simpa [C, transpose_mul, Matrix.conjTranspose_transpose] using
      congrArg Matrix.transpose (mul_eq_one_comm.mp (compound_unitary U))
  have hpair : Cᵀ * hodgeMatrix * C = hodgeMatrix := by
    have hd : (U : C4).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp U.prop).2
    simpa [C, hd] using compound_pairing (U : C4)
  change hodgeMatrix * C = C.map conj * hodgeMatrix
  calc
    hodgeMatrix * C = (C.map conj * Cᵀ) * hodgeMatrix * C := by rw [hC, Matrix.one_mul]
    _ = C.map conj * hodgeMatrix := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Cᵀ, hpair]

/-- The change of coordinates whose columns are the real Hodge basis times sqrt two. -/
private def basisChange : C6 :=
  !![1, 0, 0, Complex.I, 0, 0;
     0, 1, 0, 0, Complex.I, 0;
     0, 0, 1, 0, 0, Complex.I;
     1, 0, 0, -Complex.I, 0, 0;
     0, -1, 0, 0, Complex.I, 0;
     0, 0, 1, 0, 0, -Complex.I]

private def basisInv : C6 := (1 / 2 : ℂ) • basisChangeᴴ

private theorem basis_gram : basisChangeᴴ * basisChange = (2 : ℂ) • (1 : C6) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisChange, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      Complex.star_def, Complex.I_mul_I]

private theorem basisInv_mul : basisInv * basisChange = 1 := by
  rw [basisInv, smul_mul_assoc, basis_gram, smul_smul]
  norm_num

private theorem mul_basisInv : basisChange * basisInv = 1 :=
  mul_eq_one_comm.mp basisInv_mul

private theorem hodge_basis : hodgeMatrix * basisChange = basisChange.map conj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisChange, hodgeMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem basisInv_hodge : basisInv.map conj * hodgeMatrix = basisInv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisInv, basisChange, hodgeMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.star_def, map_ofNat]

private def actionComplex (U : SU4) : C6 := basisInv * exteriorSquare (U : C4) * basisChange

private theorem action_real (U : SU4) : (actionComplex U).map conj = actionComplex U := by
  have mapMul (A B : C6) : (A * B).map conj = A.map conj * B.map conj :=
    (conj : ℂ →+* ℂ).mapMatrix.map_mul A B
  unfold actionComplex
  simp only [mapMul]
  rw [← hodge_basis, Matrix.mul_assoc, ← Matrix.mul_assoc ((exteriorSquare (U : C4)).map conj),
    ← compound_hodge_intertwine, ← Matrix.mul_assoc, ← Matrix.mul_assoc, basisInv_hodge]

/-- The real matrix of the exterior-square action in the ordered Hodge basis. -/
def so6OfSU4 (U : SU4) : R6 := (actionComplex U).map Complex.re

private theorem complexification (U : SU4) : (so6OfSU4 U).map Complex.ofReal = actionComplex U := by
  ext i j
  have h := congrArg (fun A : C6 => A i j) (action_real U)
  exact Complex.conj_eq_iff_re.1 h

private theorem complexification_injective :
    Function.Injective (fun A : R6 => A.map Complex.ofReal) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun M : C6 => M i j) h)

theorem so6OfSU4_one : so6OfSU4 1 = 1 := by
  apply complexification_injective
  change (so6OfSU4 1).map Complex.ofReal = (1 : R6).map Complex.ofReal
  rw [complexification, Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one, actionComplex]
  change basisInv * exteriorSquare (1 : C4) * basisChange = 1
  rw [compound_one, Matrix.mul_one, basisInv_mul]

theorem so6OfSU4_mul (U V : SU4) : so6OfSU4 (U * V) = so6OfSU4 U * so6OfSU4 V := by
  apply complexification_injective
  change (so6OfSU4 (U * V)).map Complex.ofReal =
    Complex.ofRealHom.mapMatrix (so6OfSU4 U * so6OfSU4 V)
  rw [map_mul]
  change _ = (so6OfSU4 U).map Complex.ofReal * (so6OfSU4 V).map Complex.ofReal
  simp only [complexification, actionComplex, Submonoid.coe_mul, compound_mul]
  simp [Matrix.mul_assoc, ← Matrix.mul_assoc basisChange, mul_basisInv]

private theorem action_unitary (U : SU4) : (actionComplex U)ᴴ * actionComplex U = 1 := by
  have hAdj : basisInvᴴ = (1 / 2 : ℂ) • basisChange := by
    rw [basisInv, conjTranspose_smul, conjTranspose_conjTranspose]
    norm_num [Complex.star_def, map_ofNat]
  have hInv : basisInvᴴ * basisInv = (1 / 2 : ℂ) • (1 : C6) := by
    rw [hAdj, smul_mul_assoc, mul_basisInv]
  let C := exteriorSquare (U : C4)
  have hC : Cᴴ * C = 1 := compound_unitary U
  change (basisInv * C * basisChange)ᴴ * (basisInv * C * basisChange) = 1
  calc
    _ = basisChangeᴴ * (Cᴴ * (basisInvᴴ * basisInv) * C) * basisChange := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [hInv, mul_smul_comm, Matrix.mul_one, smul_mul_assoc, hC,
        mul_smul_comm, Matrix.mul_one, smul_mul_assoc, basis_gram, smul_smul]
      norm_num

theorem so6OfSU4_orthogonal (U : SU4) : (so6OfSU4 U)ᵀ * so6OfSU4 U = 1 := by
  apply complexification_injective
  have hC : ((so6OfSU4 U)ᵀ).map Complex.ofReal = (actionComplex U)ᴴ := by
    rw [← complexification U]
    ext i j
    simp
  change Complex.ofRealHom.mapMatrix ((so6OfSU4 U)ᵀ * so6OfSU4 U) = _
  rw [map_mul]
  change ((so6OfSU4 U)ᵀ).map Complex.ofReal * (so6OfSU4 U).map Complex.ofReal =
    (1 : R6).map Complex.ofReal
  rw [hC, complexification, action_unitary, Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one]

theorem so6OfSU4_det_one (U : SU4) : (so6OfSU4 U).det = 1 := by
  have hD : (basisInv.det : ℂ) * basisChange.det = 1 := by rw [← det_mul, basisInv_mul, det_one]
  apply Complex.ofReal_injective
  change Complex.ofRealHom (so6OfSU4 U).det = Complex.ofReal 1
  rw [RingHom.map_det]
  change ((so6OfSU4 U).map Complex.ofReal).det = _
  rw [complexification, actionComplex, det_mul, det_mul, mul_right_comm, hD, one_mul,
    compound_det, (Matrix.mem_specialUnitaryGroup_iff.mp U.prop).2]
  norm_num

/-- The exterior-square action as a group homomorphism. -/
def so6Cover : SU4 →* Matrix.specialOrthogonalGroup (Fin 6) ℝ where
  toFun U := ⟨so6OfSU4 U, Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 6) ℝ).mpr (so6OfSU4_orthogonal U),
      so6OfSU4_det_one U⟩⟩
  map_one' := Subtype.ext so6OfSU4_one
  map_mul' U V := Subtype.ext (so6OfSU4_mul U V)

/-- Assemble the six ordered bivector coefficients into a skew matrix. -/
def skewMatrix (z : Fin 6 → ℂ) : C4 :=
  !![0, z 0, z 1, z 2;
     -z 0, 0, z 5, z 4;
     -z 1, -z 5, 0, z 3;
     -z 2, -z 4, -z 3, 0]

private def skewCoords (A : C4) : Fin 6 → ℂ := fun i => A (first i) (second i)

private theorem skew_transpose (z : Fin 6 → ℂ) : (skewMatrix z)ᵀ = -skewMatrix z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMatrix]

private theorem skewCoords_skew (z : Fin 6 → ℂ) : skewCoords (skewMatrix z) = z := by
  funext i
  fin_cases i <;> rfl

private theorem skew_coords {A : C4} (hA : Aᵀ = -A) : skewMatrix (skewCoords A) = A := by
  have h (i j : Fin 4) : A j i = -A i j := congrArg (fun B : C4 => B i j) hA
  have hdiag (i : Fin 4) : A i i = 0 := neg_eq_self.mp (h i i).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | simp [skewMatrix, skewCoords, first, second, hdiag]; done
          | simpa [skewMatrix, skewCoords, first, second] using (h _ _).symm

/-- Congruence on skew matrices acts by the second compound on their coefficients. -/
theorem exteriorSquare_action (A : C4) (z : Fin 6 → ℂ) :
    A * skewMatrix z * Aᵀ = skewMatrix (exteriorSquare A *ᵥ z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMatrix, exteriorSquare, first, second, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

private theorem action_trivial_iff (U : SU4) :
    so6OfSU4 U = 1 ↔ exteriorSquare (U : C4) = 1 := by
  have h : basisChange * actionComplex U * basisInv = exteriorSquare (U : C4) := by
    unfold actionComplex
    rw [← Matrix.mul_assoc basisChange, ← Matrix.mul_assoc basisChange, mul_basisInv,
      Matrix.one_mul, Matrix.mul_assoc, mul_basisInv, Matrix.mul_one]
  constructor
  · intro hR
    have hC : actionComplex U = 1 := by
      rw [← complexification U, hR, Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one]
    rw [hC, Matrix.mul_one, mul_basisInv] at h
    exact h.symm
  · intro hC
    apply complexification_injective
    change (so6OfSU4 U).map Complex.ofReal = (1 : R6).map Complex.ofReal
    rw [complexification, Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one,
      actionComplex, hC, Matrix.mul_one, basisInv_mul]

private def elementarySkew (i j : Fin 4) : C4 := single i j 1 - single j i 1

private theorem not_pair_exhaustive (i j : Fin 4) : ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem compound_kernel (U : SU4) (hU : exteriorSquare (U : C4) = 1) :
    (U : C4) = 1 ∨ (U : C4) = -1 := by
  have hskew (i j : Fin 4) : (elementarySkew i j)ᵀ = -elementarySkew i j := by
    simp [elementarySkew, transpose_sub, transpose_single, neg_sub]
  have heq (i j : Fin 4) :
      (U : C4) * elementarySkew i j = elementarySkew i j * (U : C4).map conj := by
    have hfix : (U : C4) * elementarySkew i j * (U : C4)ᵀ = elementarySkew i j := by
      rw [← skew_coords (hskew i j), exteriorSquare_action, hU, one_mulVec]
    calc
      _ = ((U : C4) * elementarySkew i j * (U : C4)ᵀ) * (U : C4).map conj := by
        rw [Matrix.mul_assoc (_ * _), unitary_transpose_conj, Matrix.mul_one]
      _ = _ := by rw [hfix]
  have hoff (i j : Fin 4) (hij : i ≠ j) : (U : C4) i j = 0 := by
    obtain ⟨k, hki, hkj⟩ := not_pair_exhaustive i j
    have h := congrArg (fun M : C4 => M i k) (heq j k)
    simpa [elementarySkew, Matrix.mul_sub, Matrix.sub_mul, mul_single_apply_same,
      mul_single_apply_of_ne, single_mul_apply_of_ne, hki, hki.symm, hkj, hkj.symm,
      hij, hij.symm] using h
  have hpair (i j : Fin 4) (hij : i ≠ j) :
      (U : C4) i i = conj ((U : C4) j j) := by
    have h := congrArg (fun M : C4 => M i j) (heq i j)
    simpa [elementarySkew, Matrix.mul_sub, Matrix.sub_mul, mul_single_apply_same,
      mul_single_apply_of_ne, single_mul_apply_same, single_mul_apply_of_ne,
      hij, hij.symm] using h
  let z : ℂ := (U : C4) 0 0
  have hD : (U : C4) = diagonal (fun _ => z) := by
    ext i j
    by_cases hij : i = j
    · subst j
      obtain ⟨k, hki, hk0⟩ := not_pair_exhaustive i 0
      simpa [z] using (hpair i k hki.symm).trans (hpair 0 k hk0.symm).symm
    · simp [hij, hoff i j hij]
  have hz : z * z = 1 := by
    simpa [hD, compound_diagonal, first, second] using
      congrArg (fun M : C6 => M 0 0) hU
  have hroots : z = 1 ∨ z = -1 := by
    have hprod : (z - 1) * (z + 1) = 0 := by
      calc
        _ = z * z - 1 := by ring
        _ = _ := by rw [hz, sub_self]
    simpa [sub_eq_zero, eq_neg_iff_add_eq_zero] using mul_eq_zero.mp hprod
  rcases hroots with h | h
  · left
    simp [hD, h]
  · right
    rw [hD, ← diagonal_one, diagonal_neg, h]

theorem so6OfSU4_kernel (U : SU4) :
    so6OfSU4 U = 1 ↔ (U : C4) = 1 ∨ (U : C4) = -1 := by
  rw [action_trivial_iff]
  refine ⟨compound_kernel U, ?_⟩
  rintro (h | h)
  · rw [h, compound_one]
  · rw [h, ← diagonal_one, diagonal_neg, compound_diagonal]
    simp

/-- Hodge dual of a skew matrix in the orientation 0123. -/
def hodgeStar (A : C4) : C4 := skewMatrix (hodgeMatrix *ᵥ skewCoords A)

/-- The real form cut out by skew symmetry and Hodge duality with conjugation. -/
def SelfDual (A : C4) : Prop := Aᵀ = -A ∧ hodgeStar A = A.map conj

private theorem skew_map_conj (z : Fin 6 → ℂ) :
    (skewMatrix z).map conj = skewMatrix (conj ∘ z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMatrix]

private theorem selfDual_skew_iff (z : Fin 6 → ℂ) :
    SelfDual (skewMatrix z) ↔ hodgeMatrix *ᵥ z = conj ∘ z := by
  simp only [SelfDual, hodgeStar, skew_transpose, true_and, skewCoords_skew, skew_map_conj]
  constructor
  · intro h
    simpa only [skewCoords_skew] using congrArg skewCoords h
  · exact congrArg skewMatrix

private theorem conj_mulVec (A : C6) (z : Fin 6 → ℂ) :
    conj ∘ (A *ᵥ z) = A.map conj *ᵥ (conj ∘ z) := by
  funext i
  exact RingHom.map_mulVec (starRingEnd ℂ) A z i

theorem so6OfSU4_preserves_selfDual (U : SU4) (A : C4) (hA : SelfDual A) :
    SelfDual ((U : C4) * A * (U : C4)ᵀ) := by
  obtain ⟨z, rfl⟩ : ∃ z, A = skewMatrix z := ⟨skewCoords A, (skew_coords hA.1).symm⟩
  rw [selfDual_skew_iff] at hA
  rw [exteriorSquare_action, selfDual_skew_iff, conj_mulVec, mulVec_mulVec,
    compound_hodge_intertwine, ← mulVec_mulVec, hA]

private def normFactor : ℂ := (↑(Real.sqrt 2) : ℂ)⁻¹

private theorem normFactor_ne_zero : normFactor ≠ 0 := by
  have h : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  simp [normFactor, h]

private theorem normFactor_sq : normFactor * normFactor = 1 / 2 := by
  have hs : (↑(Real.sqrt 2) : ℂ) * ↑(Real.sqrt 2) = 2 := by
    rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold normFactor
  rw [← mul_inv, hs, one_div]

private theorem conj_normFactor : conj normFactor = normFactor := by simp [normFactor]

private def realCoordinates (x : Fin 6 → ℝ) : Fin 6 → ℂ :=
  normFactor • (Complex.ofReal ∘ x)

private theorem conj_realCoordinates (x : Fin 6 → ℝ) :
    conj ∘ realCoordinates x = realCoordinates x := by
  funext i
  simp [realCoordinates, Pi.smul_apply, smul_eq_mul, map_mul, conj_normFactor]

/-- The self-dual form with the given real coordinates in the orthonormal basis. -/
def selfDualChart (x : Fin 6 → ℝ) : C4 := skewMatrix (basisChange *ᵥ realCoordinates x)

/-- The ordered Hodge basis, normalized for one half of the trace pairing. -/
def selfDualBasis (i : Fin 6) : C4 :=
  skewMatrix (fun j => normFactor * basisChange j i)

private theorem skew_trace (z w : Fin 6 → ℂ) :
    ((skewMatrix z)ᴴ * skewMatrix w).trace / 2 = ∑ j, conj (z j) * w j := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, skewMatrix]
  ring

theorem selfDualBasis_orthonormal (i j : Fin 6) :
    ((selfDualBasis i)ᴴ * selfDualBasis j).trace / 2 = if i = j then 1 else 0 := by
  have h := congrArg (fun A : C6 => A i j) basis_gram
  change (basisChangeᴴ * basisChange) i j = ((2 : ℂ) • (1 : C6)) i j at h
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply] at h
  change (∑ k, conj (basisChange k i) * basisChange k j) =
    2 * (if i = j then 1 else 0) at h
  rw [selfDualBasis, selfDualBasis, skew_trace]
  simp only [map_mul, conj_normFactor]
  simp_rw [show ∀ (z w : ℂ), normFactor * z * (normFactor * w) =
      (normFactor * normFactor) * (z * w) by intros; ring]
  rw [← Finset.mul_sum, h, normFactor_sq]
  split <;> norm_num

private theorem realCoordinates_injective : Function.Injective realCoordinates := by
  intro x y h
  funext i
  apply Complex.ofReal_injective
  exact mul_left_cancel₀ normFactor_ne_zero
    (congrFun h i : normFactor * (x i : ℂ) = normFactor * (y i : ℂ))

theorem selfDualChart_injective : Function.Injective selfDualChart := by
  intro x y h
  have h' := congrArg (fun A => basisInv *ᵥ skewCoords A) h
  simp only [selfDualChart, skewCoords_skew, mulVec_mulVec, basisInv_mul, one_mulVec] at h'
  exact realCoordinates_injective h'

theorem selfDual_iff_chart (A : C4) : SelfDual A ↔ ∃! x, selfDualChart x = A := by
  constructor
  · intro hA
    obtain ⟨z, rfl⟩ : ∃ z, A = skewMatrix z := ⟨skewCoords A, (skew_coords hA.1).symm⟩
    rw [selfDual_skew_iff] at hA
    let u := basisInv *ᵥ z
    have hu : conj ∘ u = u := by
      rw [show u = basisInv *ᵥ z from rfl, conj_mulVec, ← hA,
        mulVec_mulVec, basisInv_hodge]
    let x := fun i => (normFactor⁻¹ * u i).re
    have hx : realCoordinates x = u := by
      funext i
      have hu' : conj (u i) = u i := congrFun hu i
      have hh : conj (normFactor⁻¹ * u i) = normFactor⁻¹ * u i := by
        simp [map_mul, conj_normFactor, hu']
      change normFactor * ↑(normFactor⁻¹ * u i).re = u i
      rw [Complex.conj_eq_iff_re.mp hh, ← mul_assoc, mul_inv_cancel₀ normFactor_ne_zero, one_mul]
    have hchart : selfDualChart x = skewMatrix z := by
      rw [selfDualChart, hx, show u = basisInv *ᵥ z from rfl,
        mulVec_mulVec, mul_basisInv, one_mulVec]
    exact ⟨x, hchart, fun y hy => selfDualChart_injective (hy.trans hchart.symm)⟩
  · rintro ⟨x, rfl, _⟩
    rw [selfDualChart, selfDual_skew_iff, conj_mulVec, mulVec_mulVec,
      hodge_basis, conj_realCoordinates]

theorem so6OfSU4_action (U : SU4) (x : Fin 6 → ℝ) :
    (U : C4) * selfDualChart x * (U : C4)ᵀ =
      selfDualChart (so6OfSU4 U *ᵥ x) := by
  have hU : exteriorSquare (U : C4) * basisChange = basisChange * actionComplex U := by
    rw [actionComplex, ← Matrix.mul_assoc basisChange, ← Matrix.mul_assoc basisChange,
      mul_basisInv, Matrix.one_mul]
  have hcoords : realCoordinates (so6OfSU4 U *ᵥ x) = actionComplex U *ᵥ realCoordinates x := by
    unfold realCoordinates
    rw [mulVec_smul, ← complexification U]
    congr 1
    funext i
    exact RingHom.map_mulVec Complex.ofRealHom (so6OfSU4 U) x i
  rw [selfDualChart, exteriorSquare_action, mulVec_mulVec, hU, ← mulVec_mulVec, ← hcoords,
    selfDualChart]

/-- The explicit Hodge form scaled by sqrt two. Unit coordinate vectors give
unitary skew matrices in this normalization. -/
def unnormalizedSelfDualMatrix (x : Fin 6 → ℝ) : C4 :=
  skewMatrix
    ![↑(x 0) + Complex.I * ↑(x 3), ↑(x 1) + Complex.I * ↑(x 4),
      ↑(x 2) + Complex.I * ↑(x 5), ↑(x 0) - Complex.I * ↑(x 3),
      -↑(x 1) + Complex.I * ↑(x 4), ↑(x 2) - Complex.I * ↑(x 5)]

theorem unnormalizedSelfDualMatrix_eq (x : Fin 6 → ℝ) :
    unnormalizedSelfDualMatrix x = (↑(Real.sqrt 2) : ℂ) • selfDualChart x := by
  have h : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have hskew (z : Fin 6 → ℂ) : skewMatrix (normFactor • z) = normFactor • skewMatrix z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrix, smul_eq_mul]
  rw [selfDualChart, realCoordinates, mulVec_smul, hskew, smul_smul, normFactor,
    mul_inv_cancel₀ h, one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unnormalizedSelfDualMatrix, skewMatrix, basisChange, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, mul_comm, sub_eq_add_neg]

end OmegaMath.SU4SO6Cover
