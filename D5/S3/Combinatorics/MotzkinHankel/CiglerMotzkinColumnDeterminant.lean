/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant
   mirror-E: none(waiver:monic-multiplier-remainder-determinant)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Div]
   utility: none
   digest: Monic division converts modified moment determinants into remainder determinants. -/

import Mathlib.Algebra.Polynomial.Div
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnTransfer
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelConfluence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDeterminant

open Polynomial Finset

/-- Two integral changes of basis prove the monic-multiplier determinant formula. -/
theorem multiplier_remainders {R : Type*} [CommRing R] [Nontrivial R]
    (p : ℕ → R[X]) (hp : ∀ i : ℕ, (p i).IsMonicOfDegree i)
    (ℓ : R[X] →ₗ[R] R)
    (ho : ∀ i j : ℕ, ℓ (p i * p j) = if i = j then 1 else 0)
    (g : R[X]) (h n : ℕ) (hg : g.IsMonicOfDegree h) :
    (Matrix.of fun i j : Fin n => ℓ (g * X ^ (i.val + j.val))).det =
      (-1 : R) ^ (n * h) *
        (Matrix.of fun i j : Fin h => ((p (n + i.val)) %ₘ g).coeff j.val).det := by
  classical
  have expand (f : R[X]) (b : ℕ) (hb : f.degree < b) :
      f = ∑ a : Fin b, C (f.coeff a.val) * X ^ a.val := by
    rw [Polynomial.sum_fin (fun a c => C c * X ^ a) (by simp) hb]
    exact f.sum_C_mul_X_pow_eq.symm
  have scalar (c : R) (f : R[X]) : ℓ (C c * f) = c * ℓ f := by
    simpa only [smul_eq_C_mul, smul_eq_mul] using ℓ.map_smul c f
  let total := h + n
  let P : Matrix (Fin total) (Fin total) R :=
    Matrix.of fun i j => (p i.val).coeff j.val
  let W : Matrix (Fin total) (Fin total) R :=
    Matrix.of fun i j => ℓ (X ^ i.val * p j.val)
  have p_degree (i : ℕ) : (p i).degree = i := by
    rw [degree_eq_natDegree (hp i).monic.ne_zero, (hp i).natDegree_eq]
  have inverse : P * W = 1 := by
    ext i j
    simp only [Matrix.mul_apply, P, W, Matrix.of_apply]
    have expansion := expand (p i.val) total (by rw [p_degree]; exact_mod_cast i.isLt)
    have pairing := congrArg (fun f : R[X] => ℓ (f * p j.val)) expansion
    simp only [sum_mul, map_sum, mul_assoc, scalar] at pairing
    rw [← pairing, ho]
    simp [Matrix.one_apply, Fin.ext_iff]
  have reverse_inverse : W * P = 1 := mul_eq_one_comm.mp inverse
  have P_det : P.det = 1 := by
    have triangular : P.IsLowerTriangular := by
      intro i j larger
      apply coeff_eq_zero_of_natDegree_lt
      rw [(hp i.val).natDegree_eq]
      exact larger
    rw [Matrix.det_of_isLowerTriangular P triangular]
    apply prod_eq_one
    intro i _
    change (p i.val).coeff i.val = 1
    simpa [(hp i.val).natDegree_eq] using (hp i.val).monic.coeff_natDegree
  let f : Fin total → R[X] := fun i =>
    if i.val < n then g * X ^ i.val else p (n + (i.val - n))
  have f_degree (i : Fin total) : (f i).degree < total := by
    dsimp only [f]
    split_ifs with top
    · rw [degree_mul_X_pow, degree_eq_natDegree hg.monic.ne_zero, hg.natDegree_eq]
      norm_cast
      dsimp only [total] at i ⊢
      omega
    · rw [p_degree]
      norm_cast
      dsimp only [total] at i ⊢
      omega
  let T : Matrix (Fin total) (Fin total) R := Matrix.of fun i j => (f i).coeff j.val
  let U := T * W
  have U_entry (i j : Fin total) : U i j = ℓ (f i * p j.val) := by
    dsimp only [U]
    simp only [Matrix.mul_apply, T, W, Matrix.of_apply]
    have pairing := congrArg (fun q : R[X] => ℓ (q * p j.val))
      (expand (f i) total (f_degree i))
    simp only [sum_mul, map_sum, mul_assoc, scalar] at pairing
    exact pairing.symm
  have U_det : U.det = T.det := by
    have product : U * P = T := by
      dsimp only [U]
      rw [Matrix.mul_assoc, reverse_inverse, Matrix.mul_one]
    have determinant := congrArg Matrix.det product
    simpa [Matrix.det_mul, P_det] using determinant
  let H : Matrix (Fin n) (Fin n) R :=
    Matrix.of fun i j => ℓ (g * X ^ (i.val + j.val))
  let Q : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (p i.val).coeff j.val
  have Q_det : Q.det = 1 := by
    have triangular : Q.IsLowerTriangular := by
      intro i j larger
      apply coeff_eq_zero_of_natDegree_lt
      rw [(hp i.val).natDegree_eq]
      exact larger
    rw [Matrix.det_of_isLowerTriangular Q triangular]
    apply prod_eq_one
    intro i _
    change (p i.val).coeff i.val = 1
    simpa [(hp i.val).natDegree_eq] using (hp i.val).monic.coeff_natDegree
  let index : Fin n ⊕ Fin h ≃ Fin total :=
    (finSumFinEquiv : Fin n ⊕ Fin h ≃ Fin (n + h)).trans (finCongr (Nat.add_comm n h))
  let side : Matrix (Fin n) (Fin h) R :=
    Matrix.of fun i j => ℓ (g * X ^ i.val * p (n + j.val))
  have U_block : U.submatrix index index = Matrix.fromBlocks (H * Q.transpose) side 0 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [Matrix.submatrix_apply, U_entry]
        have left_index : (index (Sum.inl i)).val = i.val := by simp [index]
        have right_index : (index (Sum.inl j)).val = j.val := by simp [index]
        simp only [f, left_index, i.isLt, if_true, right_index,
          Matrix.fromBlocks_apply₁₁, Matrix.mul_apply, H, Q,
          Matrix.transpose_apply, Matrix.of_apply]
        have pairing := congrArg (fun q : R[X] => ℓ (g * X ^ i.val * q))
          (expand (p j.val) n (by rw [p_degree]; exact_mod_cast j.isLt))
        simp only [mul_sum, map_sum] at pairing
        rw [pairing]
        apply sum_congr rfl
        intro a _
        rw [show g * X ^ i.val * (C ((p j.val).coeff a.val) * X ^ a.val) =
          C ((p j.val).coeff a.val) * (g * X ^ (i.val + a.val)) by rw [pow_add]; ring,
          scalar]
        ring
      | inr j =>
        simp [Matrix.submatrix_apply, U_entry, f, index, side, Matrix.fromBlocks,
          i.isLt, Nat.add_comm]
    | inr i =>
      cases j with
      | inl j =>
        have unequal : n + i.val ≠ j.val := by omega
        simp [Matrix.submatrix_apply, U_entry, f, index, Matrix.fromBlocks,
          ho, unequal]
      | inr j =>
        simp [Matrix.submatrix_apply, U_entry, f, index, Matrix.fromBlocks,
          ho, Matrix.one_apply, Fin.ext_iff, Nat.add_comm]
  have T_det : T.det = H.det := by
    rw [← U_det, ← Matrix.det_submatrix_equiv_self index U, U_block,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_mul,
      Matrix.det_transpose, Q_det, mul_one]
  let basis : Fin total → R[X] := fun i =>
    if i.val < h then X ^ i.val else g * X ^ (i.val - h)
  let B : Matrix (Fin total) (Fin total) R :=
    Matrix.of fun i j => (basis i).coeff j.val
  have basis_monic (i : Fin total) : (basis i).IsMonicOfDegree i.val := by
    dsimp only [basis]
    split_ifs with first
    · simpa using (isMonicOfDegree_X (R := R)).pow i.val
    · have product := hg.mul ((isMonicOfDegree_X (R := R)).pow (i.val - h))
      simpa [Nat.add_sub_of_le (le_of_not_gt first)] using product
  have B_det : B.det = 1 := by
    have triangular : B.IsLowerTriangular := by
      intro i j larger
      change (basis i).coeff j.val = 0
      apply coeff_eq_zero_of_natDegree_lt
      rw [(basis_monic i).natDegree_eq]
      exact larger
    rw [Matrix.det_of_isLowerTriangular B triangular]
    apply prod_eq_one
    intro i _
    change (basis i).coeff i.val = 1
    simpa [(basis_monic i).natDegree_eq] using (basis_monic i).monic.coeff_natDegree
  let Cmat : Matrix (Fin total) (Fin total) R := Matrix.of fun i j =>
    if i.val < n then (if j.val = h + i.val then 1 else 0)
    else if j.val < h then ((p (n + (i.val - n))) %ₘ g).coeff j.val
    else ((p (n + (i.val - n))) /ₘ g).coeff (j.val - h)
  have reconstruction (i : Fin total) :
      f i = ∑ a : Fin total, C (Cmat i a) * basis a := by
    by_cases top : i.val < n
    · let pivot : Fin total := ⟨h + i.val, by dsimp [total]; omega⟩
      rw [sum_eq_single pivot]
      · simp [Cmat, top, pivot, basis, f]
      · intro a _ different
        have unequal : a.val ≠ h + i.val := by
          intro equal
          exact different (Fin.ext equal)
        simp [Cmat, top, unequal]
      · simp
    · let q := p (n + (i.val - n))
      have remainder_degree : (q %ₘ g).degree < h := by
        simpa [degree_eq_natDegree hg.monic.ne_zero, hg.natDegree_eq] using
          degree_modByMonic_lt q hg.monic
      have quotient_degree : (q /ₘ g).degree < n := by
        by_cases qzero : q /ₘ g = 0
        · simp [qzero]
        · have enough : h ≤ n + (i.val - n) := by
            have lower := not_lt.mp ((divByMonic_eq_zero_iff hg.monic).not.mp qzero)
            rw [degree_eq_natDegree hg.monic.ne_zero, hg.natDegree_eq,
              show q.degree = (n + (i.val - n) : ℕ) by exact p_degree _] at lower
            exact_mod_cast lower
          rw [degree_eq_natDegree qzero, natDegree_divByMonic q hg.monic,
            hg.natDegree_eq, (hp (n + (i.val - n))).natDegree_eq]
          norm_cast
          dsimp only [total] at i
          omega
      rw [Fin.sum_univ_add]
      have first_part :
          (∑ a : Fin h, C (Cmat i (Fin.castAdd n a)) * basis (Fin.castAdd n a)) =
          q %ₘ g := by
        simpa [Cmat, top, basis, q] using (expand _ h remainder_degree).symm
      have second_part :
          (∑ a : Fin n, C (Cmat i (Fin.natAdd h a)) * basis (Fin.natAdd h a)) =
          g * (q /ₘ g) := by
        simp only [Cmat, Matrix.of_apply, top, if_false, Fin.val_natAdd,
          show ∀ a : Fin n, ¬h + a.val < h by intro a; omega,
          if_false, Nat.add_sub_cancel_left, basis]
        change (∑ a : Fin n, C ((q /ₘ g).coeff a.val) * (g * X ^ a.val)) = _
        calc
          _ = ∑ a : Fin n, g * (C ((q /ₘ g).coeff a.val) * X ^ a.val) := by
            apply sum_congr rfl
            intro a _
            ring
          _ = g * (∑ a : Fin n, C ((q /ₘ g).coeff a.val) * X ^ a.val) :=
            (mul_sum _ _ _).symm
          _ = g * (q /ₘ g) := congrArg (g * ·) (expand _ n quotient_degree).symm
      rw [first_part, second_part, modByMonic_add_div]
      simp [f, top, q]
  have product : Cmat * B = T := by
    ext i j
    have coefficient := congrArg (fun q : R[X] => q.coeff j.val) (reconstruction i)
    simp only [finsetSum_coeff, coeff_C_mul] at coefficient
    simpa only [Matrix.mul_apply, T, B, Matrix.of_apply] using coefficient.symm
  have Cmat_det : Cmat.det = T.det := by
    have determinant := congrArg Matrix.det product
    simpa [Matrix.det_mul, B_det] using determinant
  have delete : ∀ count width : ℕ, ∀ bottom : ℕ → ℕ → R,
      (Matrix.of fun i j : Fin (width + count) =>
        if i.val < count then (if j.val = width + i.val then 1 else 0)
        else bottom (i.val - count) j.val).det =
        (-1 : R) ^ (count * width) *
          (Matrix.of fun i j : Fin width => bottom i.val j.val).det := by
    intro count
    induction count with
    | zero => intro width bottom; simp
    | succ count ih =>
      intro width bottom
      let A : Matrix (Fin (width + count + 1)) (Fin (width + count + 1)) R :=
        Matrix.of fun i j =>
          if i.val < count + 1 then (if j.val = width + i.val then 1 else 0)
          else bottom (i.val - (count + 1)) j.val
      let pivot : Fin (width + count + 1) := ⟨width, by omega⟩
      have expansion : A.det = (-1 : R) ^ width *
          (A.submatrix Fin.succ pivot.succAbove).det := by
        rw [Matrix.det_succ_row_zero, sum_eq_single pivot]
        · simp [A, pivot]
        · intro j _ different
          have unequal : j.val ≠ width := by
            intro equal
            exact different (Fin.ext equal)
          simp [A, unequal]
        · simp
      have minor : A.submatrix Fin.succ pivot.succAbove =
          Matrix.of (fun i j : Fin (width + count) =>
            if i.val < count then (if j.val = width + i.val then 1 else 0)
            else bottom (i.val - count) (if j.val < width then j.val else j.val + 1)) := by
        ext i j
        have hole : (pivot.succAbove j).val =
            if j.val < width then j.val else j.val + 1 := by
          by_cases before : j.val < width
          · rw [Fin.succAbove_of_castSucc_lt pivot j (by exact before)]
            simp [before]
          · rw [Fin.succAbove_of_le_castSucc pivot j (by exact le_of_not_gt before)]
            simp [before]
        simp only [Matrix.submatrix_apply, A, Matrix.of_apply, Fin.val_succ, hole]
        have test : i.val + 1 < count + 1 ↔ i.val < count := by omega
        rw [if_congr test rfl rfl]
        by_cases top : i.val < count
        · simp only [top, if_true]
          have column_test :
              (if j.val < width then j.val else j.val + 1) = width + (i.val + 1) ↔
                j.val = width + i.val := by split_ifs <;> omega
          rw [if_congr column_test rfl rfl]
        · simp only [top, if_false]
          congr 1
          omega
      have bottom_fixed :
          (Matrix.of fun i j : Fin width =>
            bottom i.val (if j.val < width then j.val else j.val + 1)) =
          Matrix.of (fun i j : Fin width => bottom i.val j.val) := by
        ext i j
        simp
      change A.det = _
      rw [expansion, minor, ih width
        (fun i j => bottom i (if j < width then j else j + 1)), bottom_fixed,
        ← mul_assoc, ← pow_add]
      congr 1
      ring
  rw [← T_det, ← Cmat_det]
  have reduction := delete n h (fun i j =>
    if j < h then ((p (n + i)) %ₘ g).coeff j
    else ((p (n + i)) /ₘ g).coeff (j - h))
  simpa only [Cmat, total, Fin.isLt, if_true] using reduction

/-- Fixed evaluation columns do not increase the confluence order of the remaining columns. -/
theorem mixed_confluence {R : Type*} [CommRing R] (m k : ℕ)
    (f : Fin (m + k) → PowerSeries R) (g : Fin (m + k) → Fin k → R)
    (c : Fin m → R) :
    let A := Matrix.of fun i j : Fin (m + k) =>
      if hj : j.val < m then PowerSeries.rescale (c ⟨j.val, hj⟩) (f i)
      else PowerSeries.C (g i ⟨j.val - m, by omega⟩)
    let J := Matrix.of fun i j : Fin (m + k) =>
      if hj : j.val < m then PowerSeries.coeff j.val (f i)
      else g i ⟨j.val - m, by omega⟩
    (∀ d : ℕ, d < m.choose 2 → PowerSeries.coeff d A.det = 0) ∧
      PowerSeries.coeff (m.choose 2) A.det = (Matrix.vandermonde c).det * J.det := by
  classical
  induction k with
  | zero =>
    have full :
        (Matrix.of fun i j : Fin (m + 0) =>
          if hj : j.val < m then PowerSeries.rescale (c ⟨j.val, hj⟩) (f i)
          else PowerSeries.C (g i ⟨j.val - m, by omega⟩)) =
        Matrix.of (fun i j : Fin m => PowerSeries.rescale (c j) (f i)) := by
      ext i j
      simp
    have jets :
        (Matrix.of fun i j : Fin (m + 0) =>
          if hj : j.val < m then PowerSeries.coeff j.val (f i)
          else g i ⟨j.val - m, by omega⟩) =
        Matrix.of (fun i j : Fin m => PowerSeries.coeff j.val (f i)) := by
      ext i j
      simp
    dsimp only
    rw [full, jets]
    exact CiglerMotzkinHankelConfluence.alternant_coefficients m f c
  | succ k ih =>
    let A : Matrix (Fin (m + k + 1)) (Fin (m + k + 1)) (PowerSeries R) :=
      Matrix.of fun i j =>
        if hj : j.val < m then PowerSeries.rescale (c ⟨j.val, hj⟩) (f i)
        else PowerSeries.C (g i ⟨j.val - m, by omega⟩)
    let J : Matrix (Fin (m + k + 1)) (Fin (m + k + 1)) R :=
      Matrix.of fun i j =>
        if hj : j.val < m then PowerSeries.coeff j.val (f i)
        else g i ⟨j.val - m, by omega⟩
    have last_A (i : Fin (m + k + 1)) :
        A i (Fin.last (m + k)) = PowerSeries.C (g i (Fin.last k)) := by
      simp [A, Fin.last]
    have last_J (i : Fin (m + k + 1)) :
        J i (Fin.last (m + k)) = g i (Fin.last k) := by
      simp [J, Fin.last]
    have minor_A (i : Fin (m + k + 1)) :
        A.submatrix i.succAbove (Fin.last (m + k)).succAbove =
        Matrix.of (fun a b : Fin (m + k) =>
          if hb : b.val < m then PowerSeries.rescale (c ⟨b.val, hb⟩) (f (i.succAbove a))
          else PowerSeries.C (g (i.succAbove a)
            (Fin.castSucc ⟨b.val - m, by omega⟩))) := by
      ext a b
      simp [A, Matrix.submatrix_apply, Fin.succAbove_last]
    have minor_J (i : Fin (m + k + 1)) :
        J.submatrix i.succAbove (Fin.last (m + k)).succAbove =
        Matrix.of (fun a b : Fin (m + k) =>
          if hb : b.val < m then PowerSeries.coeff b.val (f (i.succAbove a))
          else g (i.succAbove a) (Fin.castSucc ⟨b.val - m, by omega⟩)) := by
      ext a b
      simp [J, Matrix.submatrix_apply, Fin.succAbove_last]
    have minor_bound (i : Fin (m + k + 1)) :=
      ih (fun a => f (i.succAbove a)) (fun a b => g (i.succAbove a) b.castSucc)
    have extract (d : ℕ) : PowerSeries.coeff d A.det =
        ∑ i : Fin (m + k + 1), (-1 : R) ^ (i.val + (m + k)) * g i (Fin.last k) *
          PowerSeries.coeff d (A.submatrix i.succAbove (Fin.last (m + k)).succAbove).det := by
      rw [Matrix.det_succ_column A (Fin.last (m + k)), map_sum]
      apply sum_congr rfl
      intro i _
      rw [last_A]
      have sign_constant : (-1 : PowerSeries R) ^ (i.val + (m + k)) =
          PowerSeries.C ((-1 : R) ^ (i.val + (m + k))) := by simp
      rw [Fin.val_last, sign_constant, ← map_mul, PowerSeries.coeff_C_mul]
    change (∀ d : ℕ, d < m.choose 2 → PowerSeries.coeff d A.det = 0) ∧
      PowerSeries.coeff (m.choose 2) A.det = (Matrix.vandermonde c).det * J.det
    constructor
    · intro d below
      rw [extract]
      apply sum_eq_zero
      intro i _
      rw [minor_A, (minor_bound i).1 d below, mul_zero]
    · rw [extract, Matrix.det_succ_column J (Fin.last (m + k)), mul_sum]
      apply sum_congr rfl
      intro i _
      rw [minor_A, (minor_bound i).2, last_J, minor_J]
      simp only [Fin.val_last]
      ring

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDeterminant
