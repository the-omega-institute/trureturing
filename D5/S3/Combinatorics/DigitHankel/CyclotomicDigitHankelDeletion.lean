/- GID: D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDeletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDeletion
   mirror-E: none(waiver:weighted-scalar-deletion)
   anchors: []
   utility: none
   digest: Independent highest-weight deletion by binary carry shears. -/

import D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelReflection
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Matrix
namespace D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelDeletion
open CyclotomicDigitHankelReflection
/-- Deletion with an independently variable highest weight; the child weight is `x / 2`.
The carry shear uses only division by two, so the formula includes `x = 2 * w`. -/
theorem weighted_deletion {R : Type*} [Field R] [CharZero R] (f : ℕ → R)
    (k n : ℕ) (w x : R) (hk : 2 ≤ k) (hn : 5 ≤ n)
    (hlo : 3 * 2 ^ k < 2 * n) (hhi : n ≤ 2 * 2 ^ k) (hz : f 0 = 0)
    (hlow : ∀ s < 2 ^ k, f (2 ^ k + s) = f s + w)
    (hhigh : ∀ s < 2 * 2 ^ k, f (2 * 2 ^ k + s) = x + f s) :
    let H := fun n => (Matrix.of fun i j : Fin n => f (i.val + j.val)).det
    let E := fun n => (Matrix.of fun i j : Fin n =>
      if j.val + 1 < n then f (i.val + j.val + 1) - f (i.val + j.val) else 1).det
    let g := fun s => f s + (x / 2 - w) * (if 2 ^ k ≤ s then 1 else 0)
    let H' := fun n => (Matrix.of fun i j : Fin n => g (i.val + j.val)).det
    let E' := fun n => (Matrix.of fun i j : Fin n =>
      if j.val + 1 < n then g (i.val + j.val + 1) - g (i.val + j.val) else 1).det
    let m := n - 2 ^ k
    let b := 2 * n - 3 * 2 ^ k - 1
    let u := x - 2 * w
    H n = 2 ^ b * u ^ (2 ^ k) * H' m +
      (-1) ^ n * 2 ^ b * w ^ 2 * u ^ (2 ^ k - 1) * E' m ∧
      E n = 2 ^ b * u ^ (2 ^ k) * E' m := by
  classical
  intro H E g H' E'
  let p := 2 ^ k
  let m := n - p
  let q := 2 * p - n
  let b := 2 * n - 3 * p - 1
  let u := x - 2 * w
  have hp : 0 < p := by dsimp [p]; positivity
  have hp4 : p = 4 * 2 ^ (k - 2) := by
    calc
      p = 2 ^ (k - 2 + 2) := by dsimp [p]; congr 1; omega
      _ = 4 * 2 ^ (k - 2) := by rw [pow_add]; ring
  have hsize : m + 1 + b + q + q = n := by dsimp [m,b,q,p] at *; omega
  have hmp : m + q = p := by dsimp [m,q,p] at *; omega
  have hmb : m = q + 1 + b := by dsimp [m,b,q,p] at *; omega
  have hm : 0 < m := by dsimp [m,p] at *; omega
  have hb : 0 < b := by dsimp [b,p] at *; omega
  have hup : 2 ^ k < n := by dsimp [p] at *; omega
  obtain ⟨L,hL,hones,hentries⟩ :=
    block_conjugation f k n w x hup hhi hz hlow hhigh
  let e : ((Fin (m + 1) ⊕ Fin b) ⊕ (Fin q ⊕ Fin q)) ≃ Fin n :=
    { toFun := fun a => match a with
        | Sum.inl (Sum.inl i) => if i.val < m then ⟨i.val, by omega⟩
            else ⟨p, by omega⟩
        | Sum.inl (Sum.inr i) => ⟨p + q + 1 + i.val, by omega⟩
        | Sum.inr (Sum.inl i) => ⟨m + i.val, by omega⟩
        | Sum.inr (Sum.inr i) => ⟨p + 1 + i.val, by omega⟩
      invFun := fun j =>
        if h₁ : j.val < m then Sum.inl (Sum.inl ⟨j.val, by omega⟩)
        else if h₂ : j.val < p then Sum.inr (Sum.inl ⟨j.val - m, by omega⟩)
        else if h₃ : j.val = p then Sum.inl (Sum.inl (Fin.last m))
        else if h₄ : j.val ≤ p + q then Sum.inr (Sum.inr ⟨j.val - p - 1, by omega⟩)
        else Sum.inl (Sum.inr ⟨j.val - (p + q + 1), by omega⟩)
      left_inv := by
        rintro ((i | i) | (i | i))
        · by_cases hi : i.val < m
          · simp [hi, show i.val < p by omega]
          · have he : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
            subst i
            simp [show ¬p < m by omega]
        · have h₁ : ¬p + q + 1 + i.val < m := by omega
          have h₂ : ¬p + q + 1 + i.val < p := by omega
          have h₃ : ¬p + q + 1 + i.val = p := by omega
          have h₄ : ¬p + q + 1 + i.val ≤ p + q := by omega
          simp [h₁,h₂,h₃,h₄]
        · have h₁ : ¬m + i.val < m := by omega
          have h₂ : m + i.val < p := by omega
          simp [h₁,h₂]
        · have h₁ : ¬p + 1 + i.val < m := by omega
          have h₂ : ¬p + 1 + i.val < p := by omega
          have h₃ : ¬p + 1 + i.val = p := by omega
          have h₄ : p + 1 + i.val ≤ p + q := by omega
          simp [h₁,h₂,h₃,h₄]
          apply Fin.ext
          dsimp
          omega
      right_inv := by
        intro j
        dsimp only
        split_ifs with h₁ h₂ h₃ h₄
        · simp [h₁]
        · apply Fin.ext; dsimp; omega
        · simp only [Fin.val_last, lt_self_iff_false, if_false]
          exact Fin.ext h₃.symm
        · apply Fin.ext; dsimp; omega
        · apply Fin.ext; dsimp; omega }
  let a (i : Fin (m + 1)) (j : Fin b) : R :=
    if i.val < m ∧ i.val = q + 1 + j.val then 1 / 2 else 0
  let S : Matrix (Fin (m + 1) ⊕ Fin b) (Fin (m + 1) ⊕ Fin b) R :=
    fromBlocks 1 a 0 1
  have hS : S.det = 1 := by simp [S,det_fromBlocks_zero₂₁]
  let U : Matrix ((Fin (m + 1) ⊕ Fin b) ⊕ (Fin q ⊕ Fin q))
      ((Fin (m + 1) ⊕ Fin b) ⊕ (Fin q ⊕ Fin q)) R := fromBlocks S 0 0 1
  have hU : U.det = 1 := by simp [U,det_fromBlocks_zero₂₁,hS]
  have hshear (T : Matrix ((Fin (m + 1) ⊕ Fin b) ⊕ (Fin q ⊕ Fin q))
      ((Fin (m + 1) ⊕ Fin b) ⊕ (Fin q ⊕ Fin q)) R) :
      ∀ i j, (U * T) i j = match i with
        | Sum.inl (Sum.inl i) => T (Sum.inl (Sum.inl i)) j +
            if h : q + 1 ≤ i.val ∧ i.val < m then
              (1 / 2) * T (Sum.inl (Sum.inr ⟨i.val - q - 1, by omega⟩)) j else 0
        | _ => T i j := by
    intro i j
    rcases i with ((i | i) | (i | i))
    · simp only [Matrix.mul_apply,Fintype.sum_sum_type,U,S,fromBlocks_apply₁₁,
        fromBlocks_apply₁₂,fromBlocks_apply₂₁,fromBlocks_apply₂₂,Matrix.one_apply]
      simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.sum_const_zero,
        add_zero,zero_add]
      by_cases hi : q + 1 ≤ i.val ∧ i.val < m
      · rw [dif_pos hi]
        let j₀ : Fin b := ⟨i.val - q - 1, by omega⟩
        have hj₀ : i.val = q + 1 + j₀.val := by dsimp [j₀]; omega
        have ha : ∀ j : Fin b, a i j = if j = j₀ then 1 / 2 else 0 := by
          intro j
          dsimp [a]
          apply if_congr
          · constructor
            · intro h; apply Fin.ext; dsimp [j₀]; omega
            · rintro rfl; exact ⟨hi.2,hj₀⟩
          · rfl
          · rfl
        simp [ha,j₀]
      · rw [dif_neg hi]
        have ha : ∀ j : Fin b, a i j = 0 := by
          intro j
          dsimp [a]
          rw [if_neg (by omega)]
        simp [ha]
    · simp [U,S,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]
    · simp [U,S,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]
    · simp [U,S,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]
  have forced (q : Type) [Fintype q] [DecidableEq q] (r : ℕ) (B : Matrix q q R)
      (C : Matrix q (Fin r) R) (C' : Matrix (Fin r) q R)
      (D M : Matrix (Fin r) (Fin r) R) (u : R) :
      (fromBlocks B ((fun i => Sum.elim (C i) (fun _ => 0)))
        ((Matrix.of (Sum.elim (fun i j => C' i j) (fun _ _ => 0))))
        (fromBlocks D (u • M) (u • M.transpose) 0)).det =
        (-1) ^ r * u ^ (2 * r) * M.det ^ 2 * B.det := by
    let Q : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) R := fromBlocks 0 1 1 0
    have hQ : Q.det = (-1) ^ r := by
      let P : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) R := fromBlocks 1 1 0 1
      have hP : P.det = 1 := by simp [P, det_fromBlocks_zero₂₁]
      have hprod : P * Q = fromBlocks 1 1 1 0 := by simp [P, Q, fromBlocks_multiply]
      have hd := congrArg Matrix.det hprod
      rw [det_mul, hP, one_mul, det_fromBlocks_one₁₁] at hd
      simpa [Matrix.det_neg] using hd
    let A := fromBlocks B ((fun i => Sum.elim (C i) (fun _ => 0)))
      ((Matrix.of (Sum.elim (fun i j => C' i j) (fun _ _ => 0))))
      (fromBlocks D (u • M) (u • M.transpose) 0)
    let Q' : Matrix (q ⊕ (Fin r ⊕ Fin r)) (q ⊕ (Fin r ⊕ Fin r)) R :=
      fromBlocks 1 0 0 Q
    have hQ' : Q'.det = (-1) ^ r := by simp [Q', det_fromBlocks_zero₂₁, hQ]
    have hprod : (A * Q').submatrix (Equiv.sumAssoc _ _ _)
        (Equiv.sumAssoc _ _ _) =
        fromBlocks (fromBlocks B 0 C' (u • M))
          ((Matrix.of (Sum.elim (fun i j => C i j) (fun i j => D i j))))
          0 (u • M.transpose) := by
      ext i j
      rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
        simp [A, Q', Q, Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr, Matrix.mul_apply,
          Matrix.one_apply]
    have hd := congrArg Matrix.det hprod
    rw [det_submatrix_equiv_self, det_mul, hQ', det_fromBlocks_zero₂₁,
      det_fromBlocks_zero₁₂, det_smul, det_smul, det_transpose] at hd
    simp only [Fintype.card_fin] at hd
    have hs : (-1 : R) ^ r * (-1) ^ r = 1 := by
      rw [← mul_pow]
      simp
    calc
      A.det = (-1)^r * (A.det * (-1)^r) := by rw [mul_left_comm, hs, mul_one]
      _ = (-1)^r * ((B.det * (u^r*M.det)) * (u^r*M.det)) := by rw [hd]
      _ = (-1)^r * u^(2*r) * M.det^2 * B.det := by rw [show 2*r = r+r by omega, pow_add]; ring
  have border (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (w u : R) :
      let B : Matrix (Fin (n + 2)) (Fin (n + 2)) R := fun i j =>
        Fin.lastCases (Fin.lastCases u (fun _ => w) j)
          (fun i => Fin.lastCases w (fun j => A i j) j) i
      let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j =>
        Fin.lastCases 1 (fun j => A i j.succ - A i j.castSucc) j
      B.det = u * A.det + (-1) ^ (n + 1) * w ^ 2 * Q.det := by
    intro B Q
    let C : Matrix (Fin (n + 2)) (Fin (n + 2)) R := fun i j =>
      Fin.cases (B i 0) (fun j =>
        if j = Fin.last n then B i j.succ else B i j.succ - B i j.castSucc) j
    have hBC : B.det = C.det := by
      apply Matrix.det_eq_of_forall_col_eq_smul_add_pred
        (fun j => if j = Fin.last n then 0 else 1)
      · intro i
        simp [C]
      · intro i j
        simp only [C, Fin.cases_succ]
        split_ifs <;> ring
    have lc0 : Fin.lastCases u (fun _ : Fin (n + 1) => w) (0 : Fin (n + 2)) = w := by
      change Fin.lastCases u (fun _ : Fin (n + 1) => w) (0 : Fin (n + 1)).castSucc = w
      exact Fin.lastCases_castSucc 0
    have row0 : C (Fin.last (n + 1)) 0 = w := by simp [C, B, lc0]
    have rows (j : Fin (n + 1)) :
        C (Fin.last (n + 1)) j.succ = if j = Fin.last n then u else 0 := by
      simp only [C, Fin.cases_succ]
      split_ifs with h
      · subst j
        simp [B]
      · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr h
        simp [B, ← Fin.castSucc_succ]
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j =>
      Fin.cases (A i 0) (fun j => A i j.succ - A i j.castSucc) j
    have hKA : A.det = K.det := by
      apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (fun _ => 1)
      · intro i
        simp [K]
      · intro i j
        simp only [K, Fin.cases_succ]; ring
    have minorLast : (C.submatrix (Fin.last (n + 1)).succAbove
        (Fin.last (n + 1)).succAbove).det = A.det := by
      rw [hKA]
      congr 1
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last]
      change C i.castSucc j.castSucc = K i j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.castSucc_zero, C, Fin.cases_zero, B, Fin.lastCases_castSucc, K]
        change Fin.lastCases w (fun j => A i j) (0 : Fin (n + 1)).castSucc = A i 0
        exact Fin.lastCases_castSucc 0
      · simp only [Fin.castSucc_succ, C, Fin.cases_succ, K]
        simp [B, ← Fin.castSucc_succ]
    have minorZero : (C.submatrix (Fin.last (n + 1)).succAbove
        (0 : Fin (n + 2)).succAbove).det = w * Q.det := by
      have heq : C.submatrix (Fin.last (n + 1)).succAbove
          (0 : Fin (n + 2)).succAbove = Matrix.updateCol Q (Fin.last n) (fun _ => w) := by
        ext i j
        simp only [Matrix.submatrix_apply, Fin.succAbove_last, Fin.succAbove_zero]
        change C i.castSucc j.succ = (Matrix.updateCol Q (Fin.last n) (fun _ => w)) i j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simp only [C, Fin.cases_succ]
          simp [B, Matrix.updateCol]
        · simp only [C, Fin.cases_succ]
          simp [B, Q, Matrix.updateCol, ← Fin.castSucc_succ]
      rw [heq]
      have hw : (fun _ : Fin (n + 1) => w) = w • (fun _ => (1 : R)) := by
        ext
        simp
      rw [hw, Matrix.det_updateCol_smul]
      congr 1
      have hQ : Matrix.updateCol Q (Fin.last n) (fun _ => (1 : R)) = Q := by
        ext i j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [Q, Matrix.updateCol]
      rw [hQ]
    rw [hBC, Matrix.det_succ_row C (Fin.last (n + 1)), Fin.sum_univ_succ]
    simp only [Fin.val_last, Fin.val_zero, Nat.add_zero, row0, minorZero]
    have hs : (∑ j : Fin (n + 1),
        (-1 : R) ^ (n + 1 + j.succ.val) *
          C (Fin.last (n + 1)) j.succ *
          (C.submatrix (Fin.last (n + 1)).succAbove j.succ.succAbove).det) =
        u * A.det := by
      rw [Finset.sum_eq_single (Fin.last n)]
      · simp only [rows, if_true, Fin.val_last, Fin.val_succ]
        have hs : (-1 : R) ^ (n + 1 + (n + 1)) = 1 := by
          rw [show n + 1 + (n + 1) = 2 * (n + 1) by omega, pow_mul]; norm_num
        rw [hs, one_mul]
        simpa only [Fin.succ_last] using congrArg (u * ·) minorLast
      · intro j hj hjlast
        rw [rows, if_neg hjlast, mul_zero, zero_mul]
      · simp
    rw [hs]; ring
  let K (r : ℕ) : Matrix (Fin r) (Fin r) R :=
    Matrix.of fun i j => if r ≤ i.val + j.val + 1 then 1 else 0
  have Kstep (r : ℕ) : (K (r + 1)).det = (-1) ^ r * (K r).det := by
    rw [Matrix.det_succ_row (K (r + 1)) 0]
    rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [Fin.val_zero,Fin.val_last,Nat.zero_add]
      have hentry : K (r + 1) 0 (Fin.last r) = 1 := by simp [K]
      rw [hentry,mul_one]
      congr 1
      congr 1
      ext i j
      simp only [K,Matrix.of_apply,Matrix.submatrix_apply,
        Fin.succAbove_zero,Fin.succAbove_last,Fin.val_succ,Fin.val_castSucc]
      apply if_congr
      · omega
      · rfl
      · rfl
    · intro j hj hjlast
      have hj' : j.val < r := by
        have := j.isLt
        have hne : j.val ≠ r := fun h => hjlast (Fin.ext h)
        omega
      have hentry : K (r + 1) 0 j = 0 := by
        change (if r + 1 ≤ 0 + j.val + 1 then (1 : R) else 0) = 0
        rw [if_neg (by omega)]
      simp only [hentry,mul_zero,zero_mul]
    · simp
  have Ksquare (r : ℕ) : (K r).det ^ 2 = 1 := by
    induction r with
    | zero => simp [K]
    | succ r ih =>
        rw [Kstep,mul_pow,ih,mul_one]
        rw [← pow_mul]
        have he : r * 2 = 2 * r := by omega
        rw [he,pow_mul]
        simp
  have Kodd (r : ℕ) : (K (2 * r + 1)).det = (-1) ^ r := by
    induction r with
    | zero => simp [K,Matrix.det_fin_one]
    | succ r ih =>
        rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 1 + 1 by omega,Kstep,Kstep,ih]
        rw [← mul_assoc,← pow_add]
        have hs : (-1 : R) ^ (2 * r + 1 + 1 + (2 * r + 1)) = -1 := by
          rw [show 2 * r + 1 + 1 + (2 * r + 1) = 2 * (2 * r + 1) + 1 by omega,
            pow_succ,pow_mul]
          simp
        rw [hs,pow_succ]
        ring
  let ell := m - p / 2 - 1
  have hbodd : b = 2 * ell + 1 := by dsimp [b,ell,m] at *; omega
  have hsign : (-1 : R) ^ q * (-1) ^ b * (K b).det = 1 := by
    rw [hbodd,Kodd,← pow_add,← pow_add]
    have hp2 : q + 1 + ell = p / 2 := by dsimp [ell]; omega
    have hpar : ∃ s, q + (2 * ell + 1) + ell = 2 * s := by
      have hpEven : ∃ s, p / 2 = 2 * s := ⟨2 ^ (k - 2), by omega⟩
      obtain ⟨s,hs⟩ := hpEven
      refine ⟨s + ell, ?_⟩
      omega
    obtain ⟨s,hs⟩ := hpar
    rw [hs,pow_mul]
    simp
  have reduction (c : R) :
      (Matrix.of fun i j : Fin n => f (i.val + j.val) + c).det =
        2 ^ b * u ^ (p - 1) *
          (Matrix.of fun i j : Fin (m + 1) =>
            Fin.lastCases (Fin.lastCases u (fun _ => w) j)
              (fun i => Fin.lastCases w
                (fun j => g (i.val + j.val) + c) j) i).det := by
    let A : Matrix (Fin n) (Fin n) R :=
      Matrix.of fun i j => f (i.val + j.val) + c
    let J : Matrix (Fin n) (Fin n) R := fun _ _ => 1
    let F : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => f (i.val + j.val)
    have hA : A = F + c • J := by ext i j; simp [A,F,J]
    have hJ (i j : Fin n) : (L * J * L.transpose) i j =
        (if i.val < p then 1 else 0) * (if j.val < p then 1 else 0) := by
      simp only [Matrix.mul_apply,Matrix.transpose_apply,J,mul_one]
      change (∑ a : Fin n, (∑ b : Fin n, L i b) * L j a) = _
      rw [← Finset.mul_sum,hones i,hones j]
    let W := L * A * L.transpose
    have hW (i j : Fin n) : W i j =
        (if i.val < p then
          if j.val < p then f (i.val + j.val) else
            if j.val = p then w else u * (if p ≤ i.val + j.val - p then 1 else 0)
        else if i.val = p then
          if j.val < p then w else if j.val = p then u else 0
        else if j.val < p then u * (if p ≤ i.val - p + j.val then 1 else 0)
        else -2 * u * (if p ≤ (i.val - p) + (j.val - p) then 1 else 0)) +
          c * (if i.val < p then 1 else 0) * (if j.val < p then 1 else 0) := by
      simp only [W,hA,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
        Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hJ,F,hentries]
      dsimp [F,p,u]
      ring
    let T := W.submatrix e e
    have hsym : T.transpose = T := by
      have hAsym : A.transpose = A := by ext i j; simp [A,Nat.add_comm]
      simp [T,W,Matrix.transpose_mul,hAsym,Matrix.transpose_submatrix,
        Matrix.mul_assoc]
    have hright (i j) : (T * U.transpose) i j = (U * T) j i := by
      have h := congrArg (fun M => M j i) (Matrix.transpose_mul T U.transpose)
      simpa [hsym] using h
    have lowhigh (i j : Fin n) (hi : i.val < p) (hj : p < j.val) :
        W i j = u * (if p ≤ i.val + j.val - p then 1 else 0) := by
      simp [hW,hi,show ¬j.val < p by omega,show j.val ≠ p by omega]
    have highhigh (i j : Fin n) (hi : p < i.val) (hj : p < j.val) :
        W i j = -2 * u * (if p ≤ (i.val - p) + (j.val - p) then 1 else 0) := by
      simp [hW,show ¬i.val < p by omega,show i.val ≠ p by omega,
        show ¬j.val < p by omega]
    have centerhigh (j : Fin n) (hj : p < j.val) : W ⟨p,hup⟩ j = 0 := by
      simp [hW,show ¬j.val < p by omega,show j.val ≠ p by omega]
    have T00 (i j : Fin (m + 1)) : T (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl j)) =
        Fin.lastCases (Fin.lastCases u (fun _ => w) j)
          (fun i => Fin.lastCases w (fun j => f (i.val + j.val) + c) j) i := by
      refine Fin.lastCases ?_ (fun i => ?_) i
      all_goals refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [T,Matrix.submatrix_apply,e,hW]
      · simp [T,Matrix.submatrix_apply,e,hW,
          show j.val < p by omega]
      · simp [T,Matrix.submatrix_apply,e,hW,
          show i.val < p by omega]
      · simp [T,Matrix.submatrix_apply,e,hW,
          show i.val < p by omega,show j.val < p by omega]
    have T01 (i : Fin (m + 1)) (j : Fin b) :
        T (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inr j)) =
          Fin.lastCases 0 (fun i => u * (if p ≤ i.val + q + 1 + j.val then 1 else 0)) i := by
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [T,Matrix.submatrix_apply,e,Equiv.coe_fn_mk,Fin.val_last,
          if_neg (Nat.lt_irrefl m),Fin.lastCases_last]
        change W ⟨p,hup⟩ ⟨p + q + 1 + j.val, by omega⟩ = 0
        exact centerhigh _ (by dsimp only; omega)
      · simp only [T,Matrix.submatrix_apply,e,Equiv.coe_fn_mk,Fin.val_castSucc,
          if_pos i.isLt,Fin.lastCases_castSucc]
        change W ⟨i.val, by omega⟩ ⟨p + q + 1 + j.val, by omega⟩ =
          u * (if p ≤ i.val + q + 1 + j.val then 1 else 0)
        rw [lowhigh _ _ (by dsimp only; omega) (by dsimp only; omega)]
        simp only [Fin.val_mk]
        congr 1
        apply if_congr
        · omega
        · rfl
        · rfl
    have T11 (i j : Fin b) :
        T (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inr j)) = -2 * u * K b i j := by
      change W ⟨p + q + 1 + i.val, by omega⟩ ⟨p + q + 1 + j.val, by omega⟩ =
        -2 * u * K b i j
      rw [highhigh _ _ (by dsimp only; omega) (by dsimp only; omega)]
      simp only [Fin.val_mk,K,Matrix.of_apply]
      congr 1
      apply if_congr
      · omega
      · rfl
      · rfl
    have T03 (i : Fin (m + 1) ⊕ Fin b) (j : Fin q) :
        T (Sum.inl i) (Sum.inr (Sum.inr j)) = 0 := by
      rcases i with i | i
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · simp only [T,Matrix.submatrix_apply,e,Equiv.coe_fn_mk,Fin.val_last,
            if_neg (Nat.lt_irrefl m)]
          change W ⟨p,hup⟩ ⟨p + 1 + j.val, by omega⟩ = 0
          exact centerhigh _ (by dsimp only; omega)
        · simp only [T,Matrix.submatrix_apply,e,Equiv.coe_fn_mk,Fin.val_castSucc,
            if_pos i.isLt]
          change W ⟨i.val, by omega⟩ ⟨p + 1 + j.val, by omega⟩ = 0
          rw [lowhigh _ _ (by dsimp only; omega) (by dsimp only; omega)]
          simp only [Fin.val_mk,if_neg (show ¬p ≤ i.val + (p + 1 + j.val) - p by omega),
            mul_zero]
      · change W ⟨p + q + 1 + i.val, by omega⟩ ⟨p + 1 + j.val, by omega⟩ = 0
        rw [highhigh _ _ (by dsimp only; omega) (by dsimp only; omega)]
        simp only [Fin.val_mk,if_neg (show
          ¬p ≤ (p + q + 1 + i.val - p) + (p + 1 + j.val - p) by omega),mul_zero]
    have T23 (i j : Fin q) :
        T (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) = u * K q i j := by
      change W ⟨m + i.val, by omega⟩ ⟨p + 1 + j.val, by omega⟩ = u * K q i j
      rw [lowhigh _ _ (by dsimp only; omega) (by dsimp only; omega)]
      simp only [Fin.val_mk,K,Matrix.of_apply]
      congr 1
      apply if_congr
      · omega
      · rfl
      · rfl
    have T33 (i j : Fin q) :
        T (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = 0 := by
      change W ⟨p + 1 + i.val, by omega⟩ ⟨p + 1 + j.val, by omega⟩ = 0
      rw [highhigh _ _ (by dsimp only; omega) (by dsimp only; omega)]
      simp only [Fin.val_mk,if_neg (show
        ¬p ≤ (p + 1 + i.val - p) + (p + 1 + j.val - p) by omega),mul_zero]
    let V := U * T * U.transpose
    let coef (i : (Fin (m + 1) ⊕ Fin b) ⊕ (Fin q ⊕ Fin q)) : R :=
      match i with
      | Sum.inl (Sum.inl i) => if q + 1 ≤ i.val ∧ i.val < m then 1 / 2 else 0
      | _ => 0
    let dst (i : (Fin (m + 1) ⊕ Fin b) ⊕ (Fin q ⊕ Fin q)) :=
      match i with
      | Sum.inl (Sum.inl j) => if h : q + 1 ≤ j.val ∧ j.val < m then
          Sum.inl (Sum.inr (⟨j.val - q - 1, by omega⟩ : Fin b)) else i
      | _ => i
    have mult (A : Matrix ((Fin (m + 1) ⊕ Fin b) ⊕ (Fin q ⊕ Fin q))
        ((Fin (m + 1) ⊕ Fin b) ⊕ (Fin q ⊕ Fin q)) R) (i j) :
        (U * A) i j = A i j + coef i * A (dst i) j := by
      rw [hshear]
      rcases i with ((i | i) | (i | i))
      · by_cases hi : q + 1 ≤ i.val ∧ i.val < m
        · simp only [coef,dst,if_pos hi,dif_pos hi]
        · simp only [coef,dst,if_neg hi,dif_neg hi,mul_zero,zero_mul,add_zero]
      · simp [coef,dst]
      · simp [coef,dst]
      · simp [coef,dst]
    have htsym (i j) : T i j = T j i := by
      have h := congrArg (fun M => M j i) hsym
      exact h
    have Ventry (i j) : V i j = T i j + coef i * T (dst i) j +
        coef j * T i (dst j) + coef i * coef j * T (dst i) (dst j) := by
      calc
        V i j = T j i + coef j * T (dst j) i +
            coef i * (T j (dst i) + coef j * T (dst j) (dst i)) := by
          dsimp only [V]
          rw [Matrix.mul_assoc,mult,hright,hright,mult,mult]
        _ = _ := by
          rw [htsym j i,htsym (dst j) i,htsym j (dst i),htsym (dst j) (dst i)]
          ring
    let B := V.submatrix Sum.inl Sum.inl
    let C := V.submatrix Sum.inl (Sum.inr ∘ Sum.inl)
    let C' := V.submatrix (Sum.inr ∘ Sum.inl) Sum.inl
    let D := V.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl)
    have hblock : V = fromBlocks B (fun i => Sum.elim (C i) (fun _ => 0))
        (Matrix.of (Sum.elim (fun i j => C' i j) (fun _ _ => 0)))
        (fromBlocks D (u • K q) (u • (K q).transpose) 0) := by
      have V03 (i : Fin (m + 1) ⊕ Fin b) (j : Fin q) :
          V (Sum.inl i) (Sum.inr (Sum.inr j)) = 0 := by
        rcases i with i | i
        · by_cases hi : q + 1 ≤ i.val ∧ i.val < m
          · simp only [Ventry,coef,dst,if_pos hi,dif_pos hi,T03,zero_mul,mul_zero,
              add_zero,zero_add]
          · simp only [Ventry,coef,dst,if_neg hi,dif_neg hi,T03,zero_mul,mul_zero,
              add_zero,zero_add]
        · simp only [Ventry,coef,dst,T03,zero_mul,mul_zero,add_zero,zero_add]
      have vsym (i j) : V i j = V j i := by
        rw [Ventry,Ventry,htsym j i,htsym j (dst i),htsym (dst j) i,
          htsym (dst j) (dst i)]
        ring
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · rcases j with j | j
        · rfl
        · simp only [V03,Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr,Matrix.of_apply,Sum.elim_inr]
      · rcases i with i | i
        · rfl
        · rw [vsym,V03]
          rfl
      · rcases i with i | i <;> rcases j with j | j
        · rfl
        · simp only [Ventry,coef,dst,T23,zero_mul,mul_zero,add_zero,
            Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr,Matrix.smul_apply,smul_eq_mul,
              Sum.elim_inl,Sum.elim_inr,Matrix.of_apply]
        · rw [vsym]
          simp only [Ventry,coef,dst,T23,zero_mul,mul_zero,add_zero,
            Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr,Matrix.smul_apply,smul_eq_mul,
              Matrix.transpose_apply,Sum.elim_inl,Sum.elim_inr,Matrix.of_apply]
        · simp only [Ventry,coef,dst,T33,zero_mul,mul_zero,add_zero,
            Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr,Matrix.zero_apply,Sum.elim_inl,
              Sum.elim_inr,Matrix.of_apply]
    let Q : Matrix (Fin (m + 1)) (Fin (m + 1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases u (fun _ => w) j)
        (fun i => Fin.lastCases w (fun j => g (i.val + j.val) + c) j) i
    have hB : B = fromBlocks Q 0 0 ((-2 * u) • K b) := by
      have T10 (i : Fin b) (j : Fin (m + 1)) :
          T (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inl j)) =
            Fin.lastCases 0 (fun j => u * (if p ≤ j.val + q + 1 + i.val then 1 else 0)) j := by
        rw [htsym,T01]
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · refine Fin.lastCases ?_ (fun i => ?_) i
        all_goals refine Fin.lastCases ?_ (fun j => ?_) j
        · simp [B,Ventry,coef,dst,T00,T01,T10,T11,Q,Matrix.fromBlocks]
        · simp only [B,Matrix.submatrix_apply,Ventry,coef,dst,T00,T01,T10,T11,
            Fin.val_last,Fin.val_castSucc,Fin.lastCases_castSucc,Fin.lastCases_last,
            if_neg (show ¬(q + 1 ≤ m ∧ m < m) by omega),
            dif_neg (show ¬(q + 1 ≤ m ∧ m < m) by omega),
            zero_mul,mul_zero,add_zero,zero_add,Q,Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr,
              Matrix.of_apply]
          by_cases hj : q + 1 ≤ j.val ∧ j.val < m
          · simp only [if_pos hj,dif_pos hj,T00,T01,T10,T11,
              Fin.lastCases_castSucc,Fin.lastCases_last]
            ring
          · simp only [if_neg hj,dif_neg hj,zero_mul,mul_zero,add_zero]
        · simp only [B,Matrix.submatrix_apply,Ventry,coef,dst,T00,T01,T10,T11,
            Fin.val_last,Fin.val_castSucc,Fin.lastCases_castSucc,Fin.lastCases_last,
            if_neg (show ¬(q + 1 ≤ m ∧ m < m) by omega),
            dif_neg (show ¬(q + 1 ≤ m ∧ m < m) by omega),
            zero_mul,mul_zero,add_zero,zero_add,Q,Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr,
              Matrix.of_apply]
          by_cases hi : q + 1 ≤ i.val ∧ i.val < m
          · simp only [if_pos hi,dif_pos hi,T00,T01,T10,T11,
              Fin.lastCases_castSucc,Fin.lastCases_last]
            ring
          · simp only [if_neg hi,dif_neg hi,zero_mul,mul_zero,add_zero]
        · have hi := i.isLt
          have hj := j.isLt
          by_cases hs : p ≤ i.val + j.val <;>
            by_cases hi' : q + 1 ≤ i.val ∧ i.val < m <;>
            by_cases hj' : q + 1 ≤ j.val ∧ j.val < m
          all_goals try omega
          all_goals simp only [B,Matrix.submatrix_apply,Ventry,coef,dst,T00,T01,T10,T11,
            Fin.val_castSucc,Fin.lastCases_castSucc,hi',hj',ite_true,ite_false,dite_true,dite_false,
            Fin.val_mk,Q,Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr,Matrix.of_apply,g]
          all_goals try simp only [and_true,true_and,and_false,false_and,
            ite_true,ite_false,dite_true,dite_false,T00,T01,T10,T11,
            Fin.lastCases_castSucc,Fin.lastCases_last,Fin.val_mk,K,Matrix.of_apply]
          all_goals try simp only [and_true,true_and,and_false,false_and,
            ite_true,ite_false,dite_true,dite_false,T00,T01,T10,T11,
            Fin.lastCases_castSucc,Fin.lastCases_last,Fin.val_mk,K,Matrix.of_apply]
          all_goals first | (split_ifs <;> try omega) | skip
          all_goals try dsimp only [p,u]
          all_goals field_simp
          all_goals ring
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [B,Ventry,coef,dst,T01,T11,Matrix.fromBlocks]
        · have hi := i.isLt
          have hj := j.isLt
          by_cases hi' : q + 1 ≤ i.val ∧ i.val < m
          all_goals simp only [B,Matrix.submatrix_apply,Ventry,coef,dst,T01,T11,
            Fin.val_castSucc,Fin.lastCases_castSucc,hi',ite_true,ite_false,dite_true,dite_false,
              Fin.val_mk,zero_mul,mul_zero,add_zero,
            Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr,Matrix.zero_apply,K,Matrix.of_apply]
          all_goals try simp only [and_true,true_and,and_false,false_and,
            ite_true,ite_false,dite_true,dite_false,T00,T01,T10,T11,
            Fin.lastCases_castSucc,Fin.lastCases_last,Fin.val_mk,K,Matrix.of_apply]
          all_goals first | (split_ifs <;> try omega) | skip
          all_goals field_simp
          all_goals ring
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simp [B,Ventry,coef,dst,T10,T11,Matrix.fromBlocks]
        · have hi := i.isLt
          have hj := j.isLt
          by_cases hj' : q + 1 ≤ j.val ∧ j.val < m
          all_goals simp only [B,Matrix.submatrix_apply,Ventry,coef,dst,T10,T11,
            Fin.val_castSucc,Fin.lastCases_castSucc,hj',ite_true,ite_false,dite_true,dite_false,
              Fin.val_mk,zero_mul,mul_zero,add_zero,
            Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr,Matrix.zero_apply,K,Matrix.of_apply]
          all_goals try simp only [and_true,true_and,and_false,false_and,
            ite_true,ite_false,dite_true,dite_false,T00,T01,T10,T11,
            Fin.lastCases_castSucc,Fin.lastCases_last,Fin.val_mk,K,Matrix.of_apply]
          all_goals first | (split_ifs <;> try omega) | skip
          all_goals field_simp
          all_goals ring
      · simp only [B,Matrix.submatrix_apply,Ventry,coef,dst,T11,
          zero_mul,mul_zero,add_zero,Matrix.fromBlocks,Sum.elim_inl,Sum.elim_inr,
            Matrix.smul_apply,smul_eq_mul,Sum.elim_inl,Sum.elim_inr,Matrix.of_apply]
    have hVdet : V.det = A.det := by
      simp [V,Matrix.det_mul,Matrix.det_transpose,hU,T,
        Matrix.det_submatrix_equiv_self,W,hL]
    change A.det = _
    rw [← hVdet,hblock,forced,Ksquare,mul_one,hB,det_fromBlocks_zero₂₁,
      Matrix.det_smul]
    simp only [Fintype.card_fin]
    have hexp : 2 * q + b = p - 1 := by omega
    have htwo : (-2 : R) ^ b = (-1) ^ b * 2 ^ b := by
      rw [show (-2 : R) = (-1) * 2 by ring,mul_pow]
    have hcoef : (-1 : R) ^ q * u ^ (2 * q) * ((-2 * u) ^ b * (K b).det) =
        2 ^ b * u ^ (p - 1) := by
      rw [mul_pow,htwo]
      calc
        (-1) ^ q * u ^ (2 * q) * (((-1) ^ b * 2 ^ b) * u ^ b * (K b).det) =
            ((-1) ^ q * (-1) ^ b * (K b).det) * (2 ^ b * u ^ (2 * q + b)) := by
          rw [pow_add]
          ring
        _ = _ := by rw [hsign,one_mul,hexp]
    change (-1) ^ q * u ^ (2 * q) * (Q.det * ((-2 * u) ^ b * (K b).det)) = _
    calc
      (-1) ^ q * u ^ (2 * q) * (Q.det * ((-2 * u) ^ b * (K b).det)) =
          ((-1) ^ q * u ^ (2 * q) * ((-2 * u) ^ b * (K b).det)) * Q.det := by ring
      _ = _ := by rw [hcoef]
  have borderFormula (g : ℕ → R) (m : ℕ) (hm : 0 < m) (w u : R) :
      let B : Matrix (Fin (m + 1)) (Fin (m + 1)) R := fun i j =>
        Fin.lastCases (Fin.lastCases u (fun _ => w) j)
          (fun i => Fin.lastCases w (fun j => g (i.val + j.val)) j) i
      B.det = u * (Matrix.of fun i j : Fin m => g (i.val + j.val)).det +
        (-1) ^ m * w ^ 2 * (Matrix.of fun i j : Fin m => if j.val + 1 < m then
          g (i.val + j.val + 1) - g (i.val + j.val) else 1).det := by
    intro B
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have h := border n (Matrix.of fun i j : Fin (n + 1) => g (i.val + j.val)) w u
    dsimp only at h
    have hQ : (fun i j : Fin (n + 1) => Fin.lastCases 1
        (fun j => g (i.val + j.succ.val) - g (i.val + j.castSucc.val)) j) =
        Matrix.of (fun i j : Fin (n + 1) => if j.val + 1 < n + 1 then
          g (i.val + j.val + 1) - g (i.val + j.val) else 1) := by
      ext i j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp only [Fin.lastCases_castSucc,Matrix.of_apply,Fin.val_castSucc,Fin.val_succ]
        rw [if_pos (by omega)]
        congr 2
    simp only [Matrix.of_apply] at h
    rw [hQ] at h
    exact h
  let eps (m : ℕ) : Fin m ⊕ Unit ≃ Fin (m + 1) :=
    { toFun := Sum.elim Fin.castSucc (fun _ => Fin.last m)
      invFun := Fin.lastCases (Sum.inr ()) Sum.inl
      left_inv := by rintro (i | ⟨⟩) <;> simp
      right_inv := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp }
  have shift (g : ℕ → R) (m : ℕ) (hm : 0 < m) (c : R) :
      (Matrix.of fun i j : Fin m => g (i.val + j.val) + c).det =
        (Matrix.of fun i j : Fin m => g (i.val + j.val)).det -
          c * (-1) ^ m * (Matrix.of fun i j : Fin m => if j.val + 1 < m then
            g (i.val + j.val + 1) - g (i.val + j.val) else 1).det := by
    let A : Matrix (Fin m) (Fin m) R := Matrix.of fun i j => g (i.val + j.val)
    let o : Matrix (Fin m) Unit R := fun _ _ => 1
    let B : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) R := fromBlocks A o o.transpose 0
    let C : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) R :=
      fromBlocks A ((-c) • o) o.transpose 1
    have hC : C.det = (Matrix.of fun i j : Fin m => g (i.val + j.val) + c).det := by
      change (fromBlocks A ((-c) • o) o.transpose 1).det = _
      rw [det_fromBlocks_one₂₂]
      congr 1
      ext i j
      simp [A,o,Matrix.mul_apply,Matrix.transpose_apply,Sum.elim_inl,Sum.elim_inr,Matrix.of_apply]
    have hB : B.det = (-1) ^ m *
        (Matrix.of fun i j : Fin m => if j.val + 1 < m then
          g (i.val + j.val + 1) - g (i.val + j.val) else 1).det := by
      let B' : Matrix (Fin (m + 1)) (Fin (m + 1)) R := fun i j =>
        Fin.lastCases (Fin.lastCases 0 (fun _ => 1) j)
          (fun i => Fin.lastCases 1 (fun j => g (i.val + j.val)) j) i
      have heq : B'.submatrix (eps m) (eps m) = B := by
        ext i j
        rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
          simp [B',B,A,o,eps,Matrix.submatrix,Matrix.fromBlocks]
      rw [← heq,Matrix.det_submatrix_equiv_self]
      simpa only [B',zero_mul,zero_add,one_pow,mul_one] using borderFormula g m hm 1 0
    let C₀ : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) R :=
      fromBlocks A ((-c) • o) o.transpose 0
    let C₁ : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) R :=
      fromBlocks A ((-c) • o) 0 1
    have hsplit : C.det = C₀.det + C₁.det := by
      have h := Matrix.det_updateRow_add C (Sum.inr ())
        (C₀ (Sum.inr ())) (C₁ (Sum.inr ()))
      have heq : C.updateRow (Sum.inr ())
          (C₀ (Sum.inr ()) + C₁ (Sum.inr ())) = C := by
        ext i j
        rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
          simp [C,C₀,C₁,Matrix.updateRow,Function.update,Matrix.fromBlocks]
      have h₀ : C.updateRow (Sum.inr ()) (C₀ (Sum.inr ())) = C₀ := by
        ext i j
        rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
          simp [C,C₀,Matrix.updateRow,Function.update,Matrix.fromBlocks]
      have h₁ : C.updateRow (Sum.inr ()) (C₁ (Sum.inr ())) = C₁ := by
        ext i j
        rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
          simp [C,C₁,Matrix.updateRow,Function.update,Matrix.fromBlocks]
      rw [heq,h₀,h₁] at h
      exact h
    have h₀ : C₀.det = -c * B.det := by
      have heq : C₀ = B.updateCol (Sum.inr ()) ((-c) • fun i => B i (Sum.inr ())) := by
        ext i j
        rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
          simp [C₀,B,o,Matrix.updateCol,Function.update,Matrix.fromBlocks]
      rw [heq,Matrix.det_updateCol_smul]
      congr 1
      congr 1
      ext i j
      rcases j with j | ⟨⟩ <;> simp [Matrix.updateCol,Function.update]
    have h₁ : C₁.det = A.det := by simp [C₁,Matrix.det_fromBlocks_zero₂₁]
    rw [← hC,hsplit,h₀,h₁,hB]
    dsimp [A]
    ring
  have auxShift (g : ℕ → R) (m : ℕ) (c : R) :
      (Matrix.of fun i j : Fin m => if j.val + 1 < m then
        (g (i.val + j.val + 1) + c) - (g (i.val + j.val) + c) else 1).det =
        (Matrix.of fun i j : Fin m => if j.val + 1 < m then
          g (i.val + j.val + 1) - g (i.val + j.val) else 1).det := by
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    split_ifs <;> ring
  have hmain (c : R) :
      H n - c * (-1) ^ n * E n =
        2 ^ b * u ^ p * (H' m - c * (-1) ^ m * E' m) +
          (-1) ^ m * 2 ^ b * w ^ 2 * u ^ (p - 1) * E' m := by
    have h := reduction c
    have hs := shift f n (by omega) c
    have hs' := shift g m hm c
    have hb' := borderFormula (fun s => g s + c) m hm w u
    dsimp only at hb'
    rw [auxShift g m c] at hb'
    erw [hs,hb',hs'] at h
    change H n - c * (-1) ^ n * E n = _ at h
    change H n - c * (-1) ^ n * E n =
      2 ^ b * u ^ (p - 1) * (u * (H' m - c * (-1) ^ m * E' m) +
        (-1) ^ m * w ^ 2 * E' m) at h
    have hpPow : u ^ p = u ^ (p - 1) * u := by
      calc
        u ^ p = u ^ (p - 1 + 1) := by congr 1; omega
        _ = _ := by rw [pow_succ]
    rw [hpPow]
    convert h using 1 <;> ring
  have hsignMN : (-1 : R) ^ m = (-1) ^ n := by
    have hn : n = m + p := by omega
    rw [hn,pow_add,hp4,pow_mul]
    norm_num
  have hH := hmain 0
  have hHE := hmain 1
  simp only [zero_mul,sub_zero,one_mul] at hH hHE
  rw [hsignMN] at hH hHE
  have hE : E n = 2 ^ b * u ^ p * E' m := by
    have hc : (-1 : R) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    apply (mul_left_cancel₀ hc)
    linear_combination hH - hHE
  dsimp only
  change (H n = 2 ^ b * u ^ p * H' m +
    (-1) ^ n * 2 ^ b * w ^ 2 * u ^ (p - 1) * E' m) ∧
    (E n = 2 ^ b * u ^ p * E' m)
  exact ⟨hH,hE⟩
end D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelDeletion
