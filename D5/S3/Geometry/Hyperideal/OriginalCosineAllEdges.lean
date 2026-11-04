/- GID: D5/S3/Geometry/Hyperideal/OriginalCosineAllEdges
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/OriginalCosineAllEdges
   mirror-E: none(waiver:original-cosine-all-edges)
   anchors: []
   utility: none
   digest: Six target-edge original cosine bounds share one determinant sign. -/

import D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface

/-! The common determinant criterion for all six target-edge original cosines. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.OriginalCosineAllEdges

open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface

/-- The strict interval condition for one target edge in the local edge order. -/
def strictCosine (r a b o c d : Real) : Prop :=
  -1 < N r a b o c d / (Real.sqrt (D1 r a d) * Real.sqrt (D2 r b c)) ∧
    N r a b o c d / (Real.sqrt (D1 r a d) * Real.sqrt (D2 r b c)) < 1

private theorem ratio_strict_iff {p q n : Real} (hp : 0 < p) (hq : 0 < q) :
    ((-1 < n / (Real.sqrt p * Real.sqrt q)) ∧
      (n / (Real.sqrt p * Real.sqrt q) < 1)) ↔ 0 < p * q - n ^ 2 := by
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hden : 0 < Real.sqrt p * Real.sqrt q := mul_pos hsp hsq
  have hps : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt (le_of_lt hp)
  have hqs : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (le_of_lt hq)
  constructor
  · rintro ⟨hl, hu⟩
    have hl' : -(Real.sqrt p * Real.sqrt q) < n := by
      simpa using (lt_div_iff₀ hden).mp hl
    have hu' : n < Real.sqrt p * Real.sqrt q := by
      simpa using (div_lt_iff₀ hden).mp hu
    nlinarith [sq_nonneg (n + Real.sqrt p * Real.sqrt q),
      sq_nonneg (n - Real.sqrt p * Real.sqrt q)]
  · intro h
    have hlow : -(Real.sqrt p * Real.sqrt q) < n := by
      nlinarith [sq_nonneg (n + Real.sqrt p * Real.sqrt q),
        sq_nonneg (n - Real.sqrt p * Real.sqrt q)]
    have hupp : n < Real.sqrt p * Real.sqrt q := by
      nlinarith [sq_nonneg (n + Real.sqrt p * Real.sqrt q),
        sq_nonneg (n - Real.sqrt p * Real.sqrt q)]
    exact ⟨by
        apply (lt_div_iff₀ hden).mpr
        nlinarith [hlow], by
        apply (div_lt_iff₀ hden).mpr
        nlinarith [hupp]⟩

private theorem strict_cosine_iff_det_neg (r a b o c d : Real)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hc : 1 < c) (hd : 1 < d) :
    strictCosine r a b o c d ↔ (gram r a b o c d).det < 0 := by
  have h := original_cosine_interface r a b o c d hr ha hb ho hc hd
  rw [strictCosine, ratio_strict_iff h.1.1 h.1.2]
  exact h.2.2.symm

private theorem det_perm_a (r a b o c d : Real) :
    (gram a r b c o d).det = (gram r a b o c d).det := by
  norm_num [gram,
    Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.det_fin_two, Matrix.det_fin_one, Matrix.det_fin_zero,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Matrix.of_apply,
    Matrix.cons_val_zero', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ,
    Matrix.vecHead, Matrix.vecTail, Fin.succAbove, Fin.reduceEq, Fin.reduceFinMk,
    Fin.castSucc, Fin.castAdd, Fin.succ, Fin.val_zero, Fin.val_succ,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castLE, Fin.cast]
  ring

private theorem det_perm_b (r a b o c d : Real) :
    (gram b r a d o c).det = (gram r a b o c d).det := by
  norm_num [gram,
    Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.det_fin_two, Matrix.det_fin_one, Matrix.det_fin_zero,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Matrix.of_apply,
    Matrix.cons_val_zero', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ,
    Matrix.vecHead, Matrix.vecTail, Fin.succAbove, Fin.reduceEq, Fin.reduceFinMk,
    Fin.castSucc, Fin.castAdd, Fin.succ, Fin.val_zero, Fin.val_succ,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castLE, Fin.cast]
  ring

private theorem det_perm_o (r a b o c d : Real) :
    (gram o a d r c b).det = (gram r a b o c d).det := by
  norm_num [gram,
    Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.det_fin_two, Matrix.det_fin_one, Matrix.det_fin_zero,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Matrix.of_apply,
    Matrix.cons_val_zero', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ,
    Matrix.vecHead, Matrix.vecTail, Fin.succAbove, Fin.reduceEq, Fin.reduceFinMk,
    Fin.castSucc, Fin.castAdd, Fin.succ, Fin.val_zero, Fin.val_succ,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castLE, Fin.cast]
  ring

private theorem det_perm_c (r a b o c d : Real) :
    (gram c r d a o b).det = (gram r a b o c d).det := by
  norm_num [gram,
    Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.det_fin_two, Matrix.det_fin_one, Matrix.det_fin_zero,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Matrix.of_apply,
    Matrix.cons_val_zero', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ,
    Matrix.vecHead, Matrix.vecTail, Fin.succAbove, Fin.reduceEq, Fin.reduceFinMk,
    Fin.castSucc, Fin.castAdd, Fin.succ, Fin.val_zero, Fin.val_succ,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castLE, Fin.cast]
  ring

private theorem det_perm_d (r a b o c d : Real) :
    (gram d r c b o a).det = (gram r a b o c d).det := by
  norm_num [gram,
    Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.det_fin_two, Matrix.det_fin_one, Matrix.det_fin_zero,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Matrix.of_apply,
    Matrix.cons_val_zero', Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ,
    Matrix.vecHead, Matrix.vecTail, Fin.succAbove, Fin.reduceEq, Fin.reduceFinMk,
    Fin.castSucc, Fin.castAdd, Fin.succ, Fin.val_zero, Fin.val_succ,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castLE, Fin.cast]
  ring

set_option maxHeartbeats 20000000 in
/- All six local original cosines lie strictly in the open interval exactly when
    the common signed Gram determinant is negative.  This is a local algebraic
criterion; it does not assert a geometric realization or a face gluing. -/
theorem all_edges_strict_iff_det_neg (r a b o c d : Real)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hc : 1 < c) (hd : 1 < d) :
    (gram r a b o c d).det < 0 ↔
      strictCosine r a b o c d ∧
      strictCosine a r b c o d ∧
      strictCosine b r a d o c ∧
      strictCosine o a d r c b ∧
      strictCosine c r d a o b ∧
      strictCosine d r c b o a := by
  have h0 := strict_cosine_iff_det_neg r a b o c d hr ha hb ho hc hd
  have h1 := strict_cosine_iff_det_neg a r b c o d ha hr hb hc ho hd
  have h2 := strict_cosine_iff_det_neg b r a d o c hb hr ha hd ho hc
  have h3 := strict_cosine_iff_det_neg o a d r c b ho ha hd hr hc hb
  have h4 := strict_cosine_iff_det_neg c r d a o b hc hr hd ha ho hb
  have h5 := strict_cosine_iff_det_neg d r c b o a hd hr hc hb ho ha
  rw [h0, h1, h2, h3, h4, h5]
  rw [det_perm_a r a b o c d, det_perm_b r a b o c d,
    det_perm_o r a b o c d, det_perm_c r a b o c d,
    det_perm_d r a b o c d]
  tauto

#print axioms all_edges_strict_iff_det_neg

end D5.S3.Geometry.Hyperideal.OriginalCosineAllEdges
