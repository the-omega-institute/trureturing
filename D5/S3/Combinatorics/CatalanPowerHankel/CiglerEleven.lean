/- GID: D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CatalanPowerHankel/CiglerEleven
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Residue row reduction evaluates the shifted Hankel determinants of odd Catalan powers. -/

import D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenPolynomials
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDeterminant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option quotPrecheck false

noncomputable section

namespace D5.S3.Combinatorics.CatalanPowerHankel.CiglerEleven

open Polynomial Matrix CiglerElevenMoments CiglerElevenPolynomials CiglerElevenReduction

open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelOrthogonal
open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs

local notation "P" => (fun n : ℕ => Polynomial.map
  (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun i : Fin 2 => if i = 0 then 2 else 1))
  (orthogonal n))

local notation "H" => (fun n : ℕ => Polynomial.map
  (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun i : Fin 2 => if i = 0 then 2 else 3))
  (orthogonal n))


/-- Truncated multiplication on a monic family gives the coefficient determinant, including
an arbitrary retained initial row and a multiplier with zero constant coefficient. -/
theorem coefficient_determinant (a : ℕ) (F g : ℚ[X]) (family : ℕ → ℚ[X])
    (hfamily : ∀ t < a, (family t).Monic ∧ (family t).natDegree = t) :
    det (Matrix.of fun i j : Fin (a + 1) =>
      (if i.val = 0 then g else X * (F * family (i.val - 1))).coeff j.val) =
      g.coeff 0 * F.coeff 0 ^ a := by
  classical
  let C : Matrix (Fin a) (Fin a) ℚ := Matrix.of fun i j => (family i.val).coeff j.val
  let U : Matrix (Fin a) (Fin a) ℚ :=
    Matrix.of fun i j => if i.val ≤ j.val then F.coeff (j.val - i.val) else 0
  let K : Matrix (Fin a) (Fin a) ℚ := Matrix.of fun i j => (F * family i.val).coeff j.val
  have hCd : C.det = 1 := by
    rw [← det_transpose]
    exact det_matrixOfPolynomials (fun i : Fin a => family i.val)
      (fun i => (hfamily i.val i.isLt).2) (fun i => (hfamily i.val i.isLt).1)
  have hU : U.IsUpperTriangular := by
    intro i j hij
    simp only [U, Matrix.of_apply,
      if_neg (show ¬ i.val ≤ j.val by exact not_le_of_gt hij)]
  have hUd : U.det = F.coeff 0 ^ a := by
    rw [det_of_isUpperTriangular hU]
    simp [U]
  have factor : K = C * U := by
    ext i j
    have hexp : family i.val = ∑ t : Fin a, (family i.val).coeff t.val • X ^ t.val := by
      rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (family i.val).coeff t • (X : ℚ[X]) ^ t)]
      simpa only [smul_eq_C_mul] using
        (family i.val).as_sum_range_C_mul_X_pow' (by rw [(hfamily i.val i.isLt).2]; exact i.isLt)
    simp only [K, C, U, Matrix.of_apply, Matrix.mul_apply]
    conv_lhs => rw [hexp, Finset.mul_sum, finsetSum_coeff]
    simp only [mul_smul_comm, coeff_smul, smul_eq_mul, coeff_mul_X_pow', mul_ite, mul_zero]
  have hKd : K.det = F.coeff 0 ^ a := by rw [factor, det_mul, hCd, hUd, one_mul]
  let e : Fin 1 ⊕ Fin a ≃ Fin (a + 1) :=
    (@finSumFinEquiv 1 a).trans (finCongr (Nat.add_comm 1 a))
  let M : Matrix (Fin (a + 1)) (Fin (a + 1)) ℚ := Matrix.of fun i j =>
    (if i.val = 0 then g else X * (F * family (i.val - 1))).coeff j.val
  have hcast : Fin.castAdd a (0 : Fin 1) = 0 := Fin.ext rfl
  have hnat (i : Fin a) : Fin.natAdd 1 i ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd, Fin.val_zero] at hv
    omega
  have block : M.submatrix e e =
      fromBlocks (Matrix.of fun _ _ : Fin 1 => g.coeff 0)
        (Matrix.of fun _ : Fin 1 => fun j : Fin a => g.coeff (j.val + 1)) 0 K := by
    ext i j
    cases i with
    | inl i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      cases j with
      | inl j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, M, e, hcast]
      | inr j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, M, e, Nat.add_comm, hcast]
    | inr i =>
      cases j with
      | inl j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, M, e, hcast, hnat]
      | inr j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, M, e, K,
          Nat.add_comm, coeff_X_mul, hnat]
  change M.det = _
  rw [← det_submatrix_equiv_self e, block, det_fromBlocks_zero₂₁, det_unique, hKd]
  rfl

/-- Row reversal and one determinant-one row-addition matrix evaluate the residue determinant.
The source row for the last possible addition is the retained boundary row. -/
theorem residue_determinant (k m n : ℕ) (hk : 1 ≤ k) (hm : m ≤ k + 1) :
    det (Matrix.of fun i j : Fin (k + (m + 1)) =>
      if j.val < k then
        (P ((2 * k + 1) * n + k + i.val) %ₘ P k).coeff j.val
      else (P ((2 * k + 1) * n + k + i.val)).coeff (j.val - k)) =
    (-1) ^ ((k + 1).choose 2 + k) *
      (P ((2 * k + 1) * n + k)).coeff 0 *
        ((Chebyshev.S ℚ (((2 * k + 1) * (n + 1) - 1 : ℕ) : ℤ)).comp
          (X - 2)).coeff 0 ^ m := by
  classical
  let R := 2 * k + 1
  let N := R * n + k
  let B := R * (n + 1)
  let D := k + (m + 1)
  let F := (Chebyshev.S ℚ ((B - 1 : ℕ) : ℤ)).comp (X - 2)
  have NB : N + k + 1 = B := by dsimp [N, B, R]; ring
  have Nk : k ≤ N := by dsimp [N]; omega
  have hp (j : ℕ) : (P j).Monic ∧ (P j).natDegree = j := by
    have hj := (orthogonal_basis j).1
    exact ⟨hj.monic.map _, (hj.monic.natDegree_map _).trans hj.natDegree_eq⟩
  have hperiod := polynomial_structure.1
  have hreflect := polynomial_structure.2.1
  have hpair := polynomial_structure.2.2
  have hh (t : ℕ) : (H t).Monic ∧ (H t).natDegree = t := by
    have ht := (orthogonal_basis t).1
    exact ⟨ht.monic.map _, (ht.monic.natDegree_map _).trans ht.natDegree_eq⟩
  have periodic (q r : ℕ) : P (R * q + r) %ₘ P k = P r %ₘ P k := by
    induction q with
    | zero => simp
    | succ q ih =>
      have hdvd : P k ∣ P (R * (q + 1) + r) - P (R * q + r) := by
        rw [show R * (q + 1) + r = 2 * k + 1 + (R * q + r) by dsimp [R]; ring,
          hperiod]
        exact dvd_mul_right _ _
      exact (modByMonic_eq_of_dvd_sub (hp k).1 hdvd).trans ih
  have source (t : ℕ) (ht : t ≤ k) :
      P (N + k - t) %ₘ P k = -(P t %ₘ P k) := by
    have hsum := congrArg (fun f : ℚ[X] => f %ₘ P k) (hreflect k (k - t) (by omega))
    rw [add_modByMonic, self_mul_modByMonic (hp k).1] at hsum
    have hi : k - (k - t) = t := by omega
    rw [hi] at hsum
    rw [show N + k - t = R * n + (k + (k - t)) by dsimp [N]; omega, periodic]
    exact eq_neg_of_add_eq_zero_left hsum
  have rem_small (i : Fin k) : P i.val %ₘ P k = P i.val := by
    apply (modByMonic_eq_self_iff (hp k).1).mpr
    exact degree_lt_degree (by rw [(hp i.val).2, (hp k).2]; exact i.isLt)
  have rem_N : P N %ₘ P k = 0 := by
    change P (R * n + k) %ₘ P k = 0
    rw [periodic, modByMonic_self (hp k).1]
  have pair_identity (t : ℕ) (ht : t < m) :
      P (N + (k + 1 + t)) + P (N + k - t) = X * F * H t := by
    have htB : t < B := by omega
    rw [show N + (k + 1 + t) = B + t by omega,
      show N + k - t = B - 1 - t by omega]
    exact hpair B t (by omega) htB
  have pair_rem (t : ℕ) (ht : t < m) : (X * F * H t) %ₘ P k = 0 := by
    rw [← pair_identity t ht, add_modByMonic, source t (by omega)]
    rw [show N + (k + 1 + t) = R * (n + 1) + t by dsimp [N]; omega,
      periodic, add_neg_cancel]
  have reverse_det (a : ℕ) :
      det (Matrix.of fun i j : Fin a => if i.val + j.val + 1 = a then (1 : ℚ) else 0) =
        (-1) ^ a.choose 2 := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [det_succ_column_zero]
      rw [Finset.sum_eq_single (Fin.last a)]
      · have minor :
            (Matrix.of fun i j : Fin (a + 1) =>
              if i.val + j.val + 1 = a + 1 then (1 : ℚ) else 0).submatrix
                (Fin.last a).succAbove Fin.succ =
            Matrix.of (fun i j : Fin a => if i.val + j.val + 1 = a then 1 else 0) := by
          ext i j
          simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last,
            Fin.val_castSucc, Fin.val_succ]
          have he : i.val + (j.val + 1) + 1 = a + 1 ↔
              i.val + j.val + 1 = a := by omega
          simp only [he]
        simp only [Matrix.of_apply, Fin.val_last, Fin.val_zero, Nat.add_zero,
          mul_one, minor, ih, ite_true]
        rw [Nat.choose_succ_succ', Nat.choose_one_right, pow_add]
      · intro i _ hi
        have hv : i.val ≠ a := by intro hv; apply hi; exact Fin.ext hv
        simp [Matrix.of_apply, hv]
      · simp
  have reverse_sign (a : ℕ) : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin a)) : ℚ) =
      (-1) ^ a.choose 2 := by
    have hrev : (1 : Matrix (Fin a) (Fin a) ℚ).submatrix Fin.revPerm id =
        Matrix.of (fun i j : Fin a => if i.val + j.val + 1 = a then 1 else 0) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.revPerm_apply, id_eq,
        Matrix.of_apply]
      have he : i.rev = j ↔ i.val + j.val + 1 = a := by
        rw [Fin.ext_iff, Fin.val_rev]
        have := i.isLt
        have := j.isLt
        omega
      simp only [he]
    have he := det_permute (Fin.revPerm : Equiv.Perm (Fin a)) (1 : Matrix (Fin a) (Fin a) ℚ)
    rw [hrev, reverse_det, det_one, mul_one] at he
    exact he.symm
  let ef : Fin (k + 1) ⊕ Fin m ≃ Fin D :=
    (@finSumFinEquiv (k + 1) m).trans (finCongr (by dsimp [D]; omega))
  let π : Equiv.Perm (Fin D) := ef.permCongr
    (Equiv.sumCongr (Fin.revPerm : Equiv.Perm (Fin (k + 1))) (Equiv.refl (Fin m)))
  have signπ : (Equiv.Perm.sign π : ℚ) = (-1) ^ (k + 1).choose 2 := by
    simp [π, Equiv.Perm.sign_sumCongr, reverse_sign]
  have πval (i : Fin D) : (π i).val = if i.val ≤ k then k - i.val else i.val := by
    obtain ⟨j, rfl⟩ := ef.surjective i
    cases j with
    | inl j =>
      have hj := j.isLt
      simp [π, ef, D, Fin.val_rev, show j.val ≤ k by omega]
    | inr j => simp [π, ef, D, show ¬ k + 1 + j.val ≤ k by omega]
  let C : Fin D → ℚ[X] →ₗ[ℚ] ℚ := fun j =>
    if j.val < k then (lcoeff ℚ j.val).comp (modByMonicHom (P k))
    else lcoeff ℚ (j.val - k)
  let Z : Matrix (Fin D) (Fin D) ℚ := Matrix.of fun i j => C j (P (N + i.val))
  let K := Z.submatrix π id
  let src (i : Fin D) : Fin D := ⟨i.val - (k + 1), by have := i.isLt; dsimp [D] at *; omega⟩
  let E : Matrix (Fin D) (Fin D) ℚ :=
    Matrix.of fun i j => if k + 1 ≤ i.val then (1 : Matrix (Fin D) (Fin D) ℚ) (src i) j else 0
  let A : Matrix (Fin D) (Fin D) ℚ := 1 + E
  have hA : A.IsLowerTriangular := by
    intro i j hij
    have hji : i.val < j.val := hij
    have hne : i ≠ j := by intro heq; subst j; omega
    have hsne : src i ≠ j := by
      intro heq
      have he := congrArg Fin.val heq
      dsimp [src] at he
      omega
    simp [A, E, hne, hsne, Matrix.one_apply]
  have hAdet : A.det = 1 := by
    rw [det_of_isLowerTriangular A hA]
    have diag (i : Fin D) : A i i = 1 := by
      dsimp [A, E]
      simp only [Matrix.one_apply]
      by_cases hi : k + 1 ≤ i.val
      · have hsne : src i ≠ i := by
          intro heq
          have he := congrArg Fin.val heq
          dsimp [src] at he
          omega
        simp [hi, hsne]
      · simp [hi]
    simp [diag]
  have addition (i j : Fin D) : (A * K) i j =
      K i j + if k + 1 ≤ i.val then K (src i) j else 0 := by
    rw [show A * K = K + E * K by dsimp [A]; rw [add_mul, one_mul]]
    simp [E, Matrix.mul_apply, Matrix.one_apply, ite_mul, Finset.sum_ite_irrel]
  let W : Fin D → ℚ[X] := fun i =>
    if i.val ≤ k then P (N + k - i.val) else X * F * H (i.val - (k + 1))
  have transformed : A * K = Matrix.of (fun i j => C j (W i)) := by
    ext i j
    rw [addition]
    simp only [Matrix.of_apply, K, Matrix.submatrix_apply, Z, id_eq, πval, Matrix.of_apply]
    by_cases hi : k + 1 ≤ i.val
    · have ht : i.val - (k + 1) < m := by have := i.isLt; dsimp [D] at *; omega
      have hsrc : (src i).val ≤ k := by dsimp [src]; omega
      simp only [if_pos hi, if_neg (show ¬ i.val ≤ k by omega), if_pos hsrc, src]
      rw [← map_add, show N + (k - (i.val - (k + 1))) = N + k - (i.val - (k + 1))
        by omega]
      have hhpair := pair_identity (i.val - (k + 1)) ht
      have hidx : N + (k + 1 + (i.val - (k + 1))) = N + i.val := by omega
      rw [hidx] at hhpair
      rw [hhpair]
      simp [W, show ¬ i.val ≤ k by omega]
    · have hi' : i.val ≤ k := by omega
      simp [hi, hi', W, show N + (k - i.val) = N + k - i.val by omega]
  let e : Fin k ⊕ Fin (m + 1) ≃ Fin D := @finSumFinEquiv k (m + 1)
  let T : Matrix (Fin k) (Fin k) ℚ := Matrix.of fun i j => (-P i.val).coeff j.val
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ := Matrix.of fun i j =>
    (if i.val = 0 then P N else X * (F * H (i.val - 1))).coeff j.val
  have hT : T.IsLowerTriangular := by
    intro i j hij
    simp only [T, Matrix.of_apply, coeff_neg]
    rw [coeff_eq_zero_of_natDegree_lt (by rw [(hp i.val).2]; exact hij), neg_zero]
  have hTdet : T.det = (-1) ^ k := by
    rw [det_of_isLowerTriangular T hT]
    have diag (i : Fin k) : T i i = -1 := by
      simp only [T, Matrix.of_apply, coeff_neg]
      nth_rw 2 [← (hp i.val).2]
      rw [(hp i.val).1.coeff_natDegree]
    simp [diag]
  have block : (A * K).submatrix e e =
      fromBlocks T ((A * K).submatrix (fun i : Fin k => e (Sum.inl i))
        (fun j : Fin (m + 1) => e (Sum.inr j))) 0 M := by
    rw [transformed]
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, D,
          j.isLt, show i.val ≤ k by omega, T, source, rem_small, coeff_neg]
      | inr j => rfl
    | inr i =>
      by_cases hi : i.val = 0
      · have hiFin : i = 0 := Fin.ext hi
        cases j with
        | inl j =>
          simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, D,
            hi, j.isLt, rem_N]
        | inr j =>
          simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, D,
            hiFin, M, Nat.add_comm]
      · have hiFin : i ≠ 0 := by
          intro he
          apply hi
          exact congrArg Fin.val he
        have hi' : 1 ≤ i.val := by omega
        have ht : i.val - 1 < m := by have := i.isLt; omega
        cases j with
        | inl j =>
          simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, D,
            j.isLt, show ¬ k + i.val ≤ k by omega,
            show k + i.val - (k + 1) = i.val - 1 by omega, pair_rem _ ht]
        | inr j =>
          simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, D,
            hiFin, show ¬ k + i.val ≤ k by omega,
            show k + i.val - (k + 1) = i.val - 1 by omega, M, mul_assoc]
  have hMdet : M.det = (P N).coeff 0 * F.coeff 0 ^ m :=
    coefficient_determinant m F (P N) H (fun t _ => hh t)
  have detAK : (A * K).det = (-1) ^ k * ((P N).coeff 0 * F.coeff 0 ^ m) := by
    rw [← det_submatrix_equiv_self e, block, det_fromBlocks_zero₂₁, hTdet, hMdet]
  have equation : (-1 : ℚ) ^ (k + 1).choose 2 * Z.det =
      (-1) ^ k * ((P N).coeff 0 * F.coeff 0 ^ m) := by
    rw [det_mul, hAdet, one_mul] at detAK
    change (Z.submatrix π id).det = _ at detAK
    rw [det_permute, signπ] at detAK
    exact detAK
  have hsquare : (-1 : ℚ) ^ (k + 1).choose 2 * (-1) ^ (k + 1).choose 2 = 1 := by
    rw [← mul_pow]
    norm_num
  have solved : Z.det = (-1) ^ ((k + 1).choose 2 + k) * (P N).coeff 0 * F.coeff 0 ^ m := by
    have he := congrArg (fun x : ℚ => (-1) ^ (k + 1).choose 2 * x) equation
    rw [← mul_assoc, hsquare, one_mul] at he
    rw [pow_add]
    simpa [mul_assoc] using he
  have form : (Matrix.of fun i j : Fin (k + (m + 1)) =>
      if j.val < k then (P (R * n + k + i.val) %ₘ P k).coeff j.val
      else (P (R * n + k + i.val)).coeff (j.val - k)) = Z := by
    ext i j
    simp only [Matrix.of_apply, Z, C, N]
    split_ifs <;> rfl
  simpa only [R, N, B, F, form] using solved

/-- Cigler's Conjecture 11, with the two upper boundary shifts included. -/
theorem result : CiglerElevenDefs.claim := by
  classical
  intro k m n hk hm
  let R := 2 * k + 1
  let N := R * n + k
  let d := m + 1
  let B := R * (n + 1)
  let u : ℚ[X] := X ^ d * P k
  have hp (j : ℕ) : (P j).Monic ∧ (P j).natDegree = j := by
    have hj := (orthogonal_basis j).1
    exact ⟨hj.monic.map _, (hj.monic.natDegree_map _).trans hj.natDegree_eq⟩
  have endpoint (j : ℕ) : (P j).coeff 0 = (-1 : ℚ) ^ j := by
    have endpoint : (P j).eval 0 = (-1 : ℚ) ^ j := by
      induction j using Nat.twoStepInduction with
      | zero => simp [orthogonal]
      | one => simp [orthogonal, sVar]
      | more j ih₀ ih₁ =>
        have step : P (j + 2) = (X - 2) * P (j + 1) - P j := by
          simp [orthogonal, tVar, Polynomial.map_sub, Polynomial.map_mul, Polynomial.C_ofNat]
        rw [step, eval_sub, eval_mul, eval_sub, eval_X, eval_ofNat, ih₀, ih₁,
          pow_succ, pow_succ]
        ring
    rw [coeff_zero_eq_eval_zero, endpoint]
  have hu : u.Monic := (monic_X.pow d).mul (hp k).1
  have hdeg : u.natDegree = k + d := by
    rw [Monic.natDegree_mul (monic_X.pow d) (hp k).1, natDegree_X_pow, (hp k).2]
    omega
  obtain ⟨moment, horth, hmoments⟩ := moment_dictionary
  have dictionary : CiglerElevenDefs.shiftedHankel R ((m : ℤ) - k + 1) N =
      det (Matrix.of fun i j : Fin N => moment (X ^ (i.val + j.val) * u)) := by
    unfold CiglerElevenDefs.shiftedHankel
    congr 1
    ext i j
    simp only [Matrix.of_apply, u, ← mul_assoc, ← pow_add, hmoments]
    congr 1
    dsimp [d]
    ring
  let Q : Fin (k + d) → ℚ[X] := fun i => P (N + i.val)
  let T : Matrix (Fin (k + d)) (Fin (k + d)) ℚ :=
    Matrix.of fun i j => (Q i %ₘ u).coeff j.val
  let Z : Matrix (Fin (k + d)) (Fin (k + d)) ℚ := Matrix.of fun i j =>
    if j.val < k then (Q i %ₘ P k).coeff j.val else (Q i).coeff (j.val - k)
  have reduction : CiglerElevenDefs.shiftedHankel R ((m : ℤ) - k + 1) N =
      (-1) ^ (N * (k + d)) * T.det := by
    rw [dictionary]
    simpa only [mul_comm] using
      D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDeterminant.multiplier_remainders
        P (fun j => ⟨(hp j).2, (hp j).1⟩) moment horth u (k + d) N ⟨hdeg, hu⟩
  have coordinates : Z.det = (-1 : ℚ) ^ (k * d) * T.det := by
    have hc := coordinate_change k d (by dsimp [d]; omega) (P k)
      (hp k).1 (hp k).2 Q
    rw [endpoint, ← pow_mul] at hc
    exact hc
  have inverse_coordinates : T.det = (-1 : ℚ) ^ (k * d) * Z.det := by
    rw [coordinates, ← mul_assoc, ← mul_pow]
    norm_num
  have residue : Z.det = (-1 : ℚ) ^ ((k + 1).choose 2 + k) * (-1) ^ N *
      ((Chebyshev.S ℚ ((B - 1 : ℕ) : ℤ)).comp (X - 2)).coeff 0 ^ m := by
    have hz := residue_determinant k m n hk hm
    rw [endpoint] at hz
    exact hz
  have Bpos : 0 < B := by dsimp [B, R]; positivity
  have multiplier : ((Chebyshev.S ℚ ((B - 1 : ℕ) : ℤ)).comp (X - 2)).coeff 0 =
      (-1 : ℚ) ^ (B - 1) * (B : ℚ) := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp only [eval_sub, eval_X, eval_ofNat, zero_sub, Chebyshev.S_eval_neg_two,
      Int.cast_negOnePow_natCast, Int.cast_natCast]
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.sub_add_cancel Bpos]
  let E := N * (k + d) + k * d + ((k + 1).choose 2 + k) + N + (B - 1) * m
  have evaluation : CiglerElevenDefs.shiftedHankel R ((m : ℤ) - k + 1) N =
      (-1 : ℚ) ^ E * (B : ℚ) ^ m := by
    rw [reduction, inverse_coordinates, residue, multiplier, mul_pow, ← pow_mul]
    dsimp [E]
    simp only [pow_add]
    ring
  have parity : E % 2 = (k * n + k.choose 2) % 2 := by
    have choose : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
      change k + k.choose 2 = k.choose 2 + k
      omega
    have bminus : B - 1 = 2 * k * (n + 1) + n := by
      have beq : B = 2 * k * (n + 1) + n + 1 := by dsimp [B, R]; ring
      omega
    have he : E = k * n + k.choose 2 +
        2 * (k * k * n + 2 * k * n * m + 2 * k * n + n * m + 2 * k * m + n +
          2 * k) + k * (k + 1) := by
      dsimp [E, N, R, d]
      rw [choose, bminus]
      ring
    obtain ⟨t, ht⟩ := Nat.two_dvd_mul_add_one k
    rw [he, ht]
    omega
  rw [evaluation, neg_one_pow_eq_pow_mod_two E, parity,
    ← neg_one_pow_eq_pow_mod_two (k * n + k.choose 2)]
  dsimp [B, R]
  rw [Nat.cast_mul, mul_pow]
  ring

end D5.S3.Combinatorics.CatalanPowerHankel.CiglerEleven
