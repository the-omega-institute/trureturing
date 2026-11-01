/- GID: D5/S3/Quantum/Matrix/MalkounJordanElementary
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/MalkounJordanElementary
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Elementary symmetric eigenvalue inequality for a Hermitian Jordan product. -/

import D5.S3.Quantum.Schatten.CompoundMatrices
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! ## The elementary symmetric inequality for a Hermitian Jordan product
The only public theorem is the exact first question of MO512579.
All auxiliary theorems are consumed on its proof path.
-/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution; exact external source assertion.
jordan_hermitian: bind-only; consumers: claim, result.
gram_det_le: bind-only; consumer: principal_det_le.
principal_det_le: bind-only; consumer: result.
spectral_minors: bind-only; consumer: result.
Direct frozen dependency: cauchyBinet, GID D5/S3/Quantum/Schatten/CompoundMatrices.
Declaration statement_id: sha256:6fb332c198d4506b8775454dff648409222d03ae0a60e7dbf5fca62ea37506df.
Frozen module statement_id: sha256:8398f8b23ac0815231125a1304c91754b658ebb26e9e24af0ace9c2147f696ce.
No source code is transplanted. The remaining dependencies are pinned Mathlib.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.Matrix.MalkounJordanElementary

open _root_.Matrix Finset Complex Polynomial
open scoped ComplexOrder
open scoped BigOperators AllOrdered

noncomputable section

/-- The original elementary symmetric polynomial: sum over k-element subsets. -/
def elementarySymmetric {n : ℕ} (t : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ S, t i

private theorem jordan_hermitian {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) : (X * Y + Y * X).IsHermitian := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hX.eq, hY.eq, add_comm]

/-- The exact first question of MO512579, with all positive orders and all k. -/
def claim : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (X Y : Matrix (Fin n) (Fin n) ℂ),
    ∀ (hX : X.PosSemidef) (hY : Y.PosSemidef), ∀ (k : ℕ), 1 ≤ k → k ≤ n →
    elementarySymmetric (jordan_hermitian hX.isHermitian hY.isHermitian).eigenvalues k ≤
      elementarySymmetric ((hX.isHermitian.pow 2).add (hY.isHermitian.pow 2)).eigenvalues k

private theorem gram_det_le {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    [LinearOrder d] (U V : Matrix d (Fin m) ℂ) (hgram : Uᴴ * U = Vᴴ * V) :
    (Uᴴ * V).det.re ≤ (Uᴴ * U).det.re := by
  classical
  let u (S : {S : Finset d // S.card = m}) : ℂ :=
    (U.submatrix (S.1.orderEmbOfFin S.2) id).det
  let v (S : {S : Finset d // S.card = m}) : ℂ :=
    (V.submatrix (S.1.orderEmbOfFin S.2) id).det
  have cb (A B : Matrix d (Fin m) ℂ) :
      (Aᴴ * B).det = ∑ S : {S : Finset d // S.card = m},
        star ((A.submatrix (S.1.orderEmbOfFin S.2) id).det) *
          (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
    simpa only [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose] using
      (cauchyBinet Aᴴ B)
  have huu := congrArg Complex.re (cb U U)
  have hvv := congrArg Complex.re (cb V V)
  have huv := congrArg Complex.re (cb U V)
  have pointwise (S : {S : Finset d // S.card = m}) :
      (star (u S) * v S).re ≤
        ((star (u S) * u S).re + (star (v S) * v S).re) / 2 := by
    have ha := sq_nonneg ((u S).re - (v S).re)
    have hb := sq_nonneg ((u S).im - (v S).im)
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith
  have hs := Finset.sum_le_sum (fun S (_ : S ∈ Finset.univ) => pointwise S)
  simp only [Complex.re_sum] at huu hvv huv
  change (Uᴴ * U).det.re = ∑ S, (star (u S) * u S).re at huu
  change (Vᴴ * V).det.re = ∑ S, (star (v S) * v S).re at hvv
  change (Uᴴ * V).det.re = ∑ S, (star (u S) * v S).re at huv
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← huu, ← hvv, ← huv, ← hgram] at hs
  linarith

private theorem principal_det_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (S : Finset (Fin n)) :
    ((X * Y + Y * X).submatrix (Subtype.val : S → Fin n) Subtype.val).det.re ≤
      ((X ^ 2 + Y ^ 2).submatrix (Subtype.val : S → Fin n) Subtype.val).det.re := by
  classical
  let e : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i : Fin n)
  let A := X.submatrix id e
  let B := Y.submatrix id e
  let U := Matrix.fromRows A B
  let V := Matrix.fromRows B A
  have mul_selected (P Q : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) :
      (P.submatrix id e)ᴴ * Q.submatrix id e = (P * Q).submatrix e e := by
    rw [Matrix.conjTranspose_submatrix, hP.eq]
    exact (Matrix.submatrix_mul P Q e id e Function.bijective_id).symm
  have hu : Uᴴ * U = (X ^ 2 + Y ^ 2).submatrix e e := by
    dsimp [U, A, B]
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, mul_selected X X hX, mul_selected Y Y hY]
    simp only [pow_two]
    rfl
  have hv : Vᴴ * V = (X ^ 2 + Y ^ 2).submatrix e e := by
    dsimp [V, A, B]
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, mul_selected Y Y hY, mul_selected X X hX]
    simp only [pow_two]
    ext i j
    simp only [Matrix.add_apply, Matrix.submatrix_apply]
    ring
  have huv : Uᴴ * V = (X * Y + Y * X).submatrix e e := by
    dsimp [U, V, A, B]
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, mul_selected X Y hX, mul_selected Y X hY]
    rfl
  have h := gram_det_le U V (hu.trans hv.symm)
  rw [hu, huv] at h
  have reindex (M : Matrix (Fin n) (Fin n) ℂ) :
      (M.submatrix e e).det =
        (M.submatrix (Subtype.val : S → Fin n) Subtype.val).det := by
    change ((M.submatrix (Subtype.val : S → Fin n) Subtype.val).submatrix
      (S.orderIsoOfFin rfl).toEquiv (S.orderIsoOfFin rfl).toEquiv).det = _
    exact Matrix.det_submatrix_equiv_self (S.orderIsoOfFin rfl).toEquiv
      (M.submatrix (Subtype.val : S → Fin n) Subtype.val)
  simpa only [reindex] using h

private theorem spectral_minors {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.IsHermitian) (k : ℕ) (hk : k ≤ n) :
    elementarySymmetric hM.eigenvalues k =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (M.submatrix (Subtype.val : S → Fin n) Subtype.val).det.re := by
  classical
  have hc := M.charpoly_coeff_eq_sum_minors k (by simpa using hk)
  have he := Polynomial.coeff_eq_esymm_roots_of_splits hM.splits_charpoly
    (k := n - k) (by simpa using (Nat.sub_le n k))
  rw [hM.roots_charpoly_eq_eigenvalues, Finset.esymm_map_val] at he
  have he' : M.charpoly.coeff (n - k) =
      (-1 : ℂ) ^ k * (elementarySymmetric hM.eigenvalues k : ℂ) := by
    simpa [Matrix.charpoly_natDegree_eq_dim, M.charpoly_monic.leadingCoeff,
      hM.roots_charpoly_eq_eigenvalues, Finset.esymm_map_val,
      Nat.sub_sub_self hk, elementarySymmetric] using he
  have hz : (-1 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have eqc : (elementarySymmetric hM.eigenvalues k : ℂ) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (M.submatrix (Subtype.val : S → Fin n) Subtype.val).det := by
    apply mul_left_cancel₀ hz
    exact he'.symm.trans (by simpa using hc)
  simpa using congrArg Complex.re eqc

/-- The original positive-semidefinite assertion, with no positivity hypothesis on XY+YX. -/
theorem result : claim := by
  intro n _hn X Y hX hY k _hk hkn
  rw [spectral_minors _ _ k hkn, spectral_minors _ _ k hkn]
  exact Finset.sum_le_sum (fun S _ => principal_det_le X Y hX.isHermitian hY.isHermitian S)

#print axioms result

end

end D5.S3.Quantum.Matrix.MalkounJordanElementary
