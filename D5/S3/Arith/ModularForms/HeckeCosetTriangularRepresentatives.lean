/- GID: D5/S3/Arith/ModularForms/HeckeCosetTriangularRepresentatives
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/HeckeCosetTriangularRepresentatives
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Triangular representatives and right reindexing for level-one Hecke sums. -/

import Mathlib.Algebra.Group.Int.Units
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-! For positive determinant, the left `SL(2, ℤ)` orbits of integral matrices have unique
triangular representatives. Right multiplication therefore permutes the indices of the
unnormalized level-one Hecke sum. -/

set_option autoImplicit false

open scoped BigOperators Matrix MatrixGroups

namespace D5.S3.Arith.ModularForms.HeckeCosetTriangularRepresentatives

local notation "Mat₂" => Matrix (Fin 2) (Fin 2) ℤ

/-- A term of the level-one Hecke sum at determinant `N`. -/
@[ext]
structure Index (N : ℤ) where
  a : ℤ
  b : ℤ
  d : ℤ
  a_pos : 0 < a
  d_pos : 0 < d
  b_nonneg : 0 ≤ b
  b_lt_d : b < d
  ad : a * d = N

/-- The matrix for the affine transformation `τ ↦ (a * τ + b) / d`. -/
def Index.matrix {N : ℤ} (r : Index N) : Mat₂ :=
  !![r.a, r.b; 0, r.d]

@[simp]
theorem Index.det_matrix {N : ℤ} (r : Index N) : r.matrix.det = N := by
  rw [Index.matrix, Matrix.det_fin_two_of, mul_zero, sub_zero, r.ad]

private def ofReps {N : ℤ} (hN : 0 < N) (A : FixedDetMatrix (Fin 2) ℤ N)
    (hA : A ∈ FixedDetMatrices.reps N) : Index N := by
  have h10 : A.1 1 0 = 0 := hA.1
  have ha : 0 < A.1 0 0 := hA.2.1
  have hb : 0 ≤ A.1 0 1 := hA.2.2.1
  have hbd : |A.1 0 1| < |A.1 1 1| := hA.2.2.2
  have had : A.1 0 0 * A.1 1 1 = N := by
    simpa only [Matrix.det_fin_two, h10, mul_zero, sub_zero] using A.2
  have hprod : 0 < A.1 0 0 * A.1 1 1 := by rwa [had]
  have hd : 0 < A.1 1 1 := lt_of_not_ge fun h =>
    (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha.le h)) hprod
  exact ⟨A.1 0 0, A.1 0 1, A.1 1 1, ha, hd, hb,
    by simpa only [abs_of_nonneg hb, abs_of_pos hd] using hbd, had⟩

private theorem ofReps_matrix {N : ℤ} (hN : 0 < N) (A : FixedDetMatrix (Fin 2) ℤ N)
    (hA : A ∈ FixedDetMatrices.reps N) : (ofReps hN A hA).matrix = A.1 := by
  have h10 : A.1 1 0 = 0 := hA.1
  change !![A.1 0 0, A.1 0 1; 0, A.1 1 1] = A.1
  simpa only [h10] using (Matrix.eta_fin_two A.1).symm

private theorem exists_smul_reduce {N : ℤ} (A : FixedDetMatrix (Fin 2) ℤ N) :
    ∃ L : SL(2, ℤ), L • A = FixedDetMatrices.reduce A := by
  induction A using FixedDetMatrices.reduce_rec with
  | base A hc =>
    by_cases ha : 0 < A.1 0 0
    · exact ⟨ModularGroup.T ^ (-(A.1 0 1 / A.1 1 1)),
        (FixedDetMatrices.reduce_of_pos hc ha).symm⟩
    · refine ⟨ModularGroup.T ^ (-(-A.1 0 1 / -A.1 1 1)) *
        (ModularGroup.S * ModularGroup.S), ?_⟩
      rw [FixedDetMatrices.reduce_of_not_pos hc ha, mul_smul, mul_smul]
  | step A hc ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨L * (ModularGroup.S * ModularGroup.T ^ (-(A.1 0 0 / A.1 1 0))), ?_⟩
    rw [mul_smul, mul_smul]
    change L • FixedDetMatrices.reduceStep A = FixedDetMatrices.reduce A
    rw [hL, FixedDetMatrices.reduce_reduceStep hc]

/-- Reduce the first column by Euclidean row operations, then reduce `b` modulo `d`. -/
def representative {N : ℤ} (hN : 0 < N) (A : Mat₂) (hA : A.det = N) : Index N :=
  let B : FixedDetMatrix (Fin 2) ℤ N := ⟨A, hA⟩
  ofReps hN (FixedDetMatrices.reduce B) (FixedDetMatrices.reduce_mem_reps (ne_of_gt hN) B)

/-- The Euclidean reduction is realized by left multiplication by an integral determinant-one
matrix. -/
theorem representative_spec {N : ℤ} (hN : 0 < N) (A : Mat₂) (hA : A.det = N) :
    ∃ L : SL(2, ℤ), (L : Mat₂) * A = (representative hN A hA).matrix := by
  let B : FixedDetMatrix (Fin 2) ℤ N := ⟨A, hA⟩
  obtain ⟨L, hL⟩ := exists_smul_reduce B
  refine ⟨L, ?_⟩
  calc
    (L : Mat₂) * A = (L • B).1 := (FixedDetMatrices.smul_coe (Fin 2) ℤ N L B).symm
    _ = (FixedDetMatrices.reduce B).1 := congrArg (fun C : FixedDetMatrix (Fin 2) ℤ N => C.1) hL
    _ = (representative hN A hA).matrix :=
      (ofReps_matrix hN (FixedDetMatrices.reduce B)
        (FixedDetMatrices.reduce_mem_reps (ne_of_gt hN) B)).symm

/-- Two reduced representatives related by a left row operation have identical indices. -/
theorem index_eq_of_left_mul {N : ℤ} {r s : Index N} (L : SL(2, ℤ))
    (h : (L : Mat₂) * r.matrix = s.matrix) : r = s := by
  let A : Mat₂ := L
  have hA : A * r.matrix = s.matrix := h
  have h10 : A 1 0 * r.a = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Index.matrix] using congrFun₂ hA 1 0
  have hc : A 1 0 = 0 := (mul_eq_zero.mp h10).resolve_right (ne_of_gt r.a_pos)
  have ha : A 0 0 * r.a = s.a := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Index.matrix] using congrFun₂ hA 0 0
  have hd : A 1 1 * r.d = s.d := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Index.matrix, hc] using congrFun₂ hA 1 1
  have hb : A 0 0 * r.b + A 0 1 * r.d = s.b := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Index.matrix] using congrFun₂ hA 0 1
  have hdet : A.det = 1 := L.det_coe
  have hdiag : A 0 0 * A 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using hdet
  obtain ⟨h00, h11⟩ | ⟨h00, h11⟩ := Int.eq_one_or_neg_one_of_mul_eq_one' hdiag
  · have ha' : r.a = s.a := by simpa only [h00, one_mul] using ha
    have hd' : r.d = s.d := by simpa only [h11, one_mul] using hd
    have hb' : r.b + r.d * A 0 1 = s.b := by
      simpa only [h00, one_mul, mul_comm (A 0 1) r.d] using hb
    have hmod := congrArg (fun x : ℤ => x % r.d) hb'
    change (r.b + r.d * A 0 1) % r.d = s.b % r.d at hmod
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt r.b_nonneg r.b_lt_d, hd',
      Int.emod_eq_of_lt s.b_nonneg s.b_lt_d] at hmod
    exact Index.ext ha' hmod hd'
  · have hneg : -r.a = s.a := by simpa only [h00, neg_one_mul] using ha
    have hs : 0 < -r.a := by
      rw [hneg]
      exact s.a_pos
    exact ((not_lt_of_ge (neg_nonpos.mpr r.a_pos.le)) hs).elim

private theorem left_representative_unique {N : ℤ} {A : Mat₂} {r s : Index N}
    {L M : SL(2, ℤ)} (hL : (L : Mat₂) * A = r.matrix) (hM : (M : Mat₂) * A = s.matrix) :
    r = s := by
  have hLinv : (↑(L⁻¹) : Mat₂) * r.matrix = A := by
    rw [← hL, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mul]
  apply index_eq_of_left_mul (M * L⁻¹)
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_assoc, hLinv, hM]

/-- Every positive-determinant integral matrix has a unique triangular left representative. -/
theorem existsUnique_left_representative {N : ℤ} (hN : 0 < N) (A : Mat₂) (hA : A.det = N) :
    ∃! r : Index N, ∃ L : SL(2, ℤ), (L : Mat₂) * A = r.matrix := by
  obtain ⟨L, hL⟩ := representative_spec hN A hA
  refine ⟨representative hN A hA, ⟨L, hL⟩, ?_⟩
  rintro r ⟨M, hM⟩
  exact left_representative_unique hM hL

private def toReps {N : ℤ} (r : Index N) : FixedDetMatrices.reps N := by
  refine ⟨⟨r.matrix, r.det_matrix⟩, ?_⟩
  change (0 : ℤ) = 0 ∧ 0 < r.a ∧ 0 ≤ r.b ∧ |r.b| < |r.d|
  exact ⟨rfl, r.a_pos, r.b_nonneg,
    by simpa only [abs_of_nonneg r.b_nonneg, abs_of_pos r.d_pos] using r.b_lt_d⟩

noncomputable instance instFintypeIndex (N : ℤ) : Fintype (Index N) := by
  refine Fintype.ofInjective (toReps (N := N)) ?_
  intro r s h
  apply index_eq_of_left_mul (1 : SL(2, ℤ))
  rw [Matrix.SpecialLinearGroup.coe_one, one_mul]
  exact congrArg (fun x : FixedDetMatrices.reps N => x.1.1) h

private theorem det_right_mul {N : ℤ} (G : SL(2, ℤ)) (r : Index N) :
    (r.matrix * (G : Mat₂)).det = N := by
  rw [Matrix.det_mul, r.det_matrix, G.det_coe, mul_one]

/-- The new index is obtained by reducing the right product back to triangular form. -/
def rightRepresentative {N : ℤ} (hN : 0 < N) (G : SL(2, ℤ)) (r : Index N) : Index N :=
  representative hN (r.matrix * (G : Mat₂)) (det_right_mul G r)

theorem rightRepresentative_spec {N : ℤ} (hN : 0 < N) (G : SL(2, ℤ)) (r : Index N) :
    ∃ L : SL(2, ℤ), (L : Mat₂) * (r.matrix * (G : Mat₂)) =
      (rightRepresentative hN G r).matrix :=
  representative_spec hN _ (det_right_mul G r)

@[simp]
theorem rightRepresentative_one {N : ℤ} (hN : 0 < N) (r : Index N) :
    rightRepresentative hN 1 r = r := by
  obtain ⟨L, hL⟩ := rightRepresentative_spec hN 1 r
  exact left_representative_unique (M := 1) hL (by simp)

theorem rightRepresentative_mul {N : ℤ} (hN : 0 < N) (G H : SL(2, ℤ)) (r : Index N) :
    rightRepresentative hN H (rightRepresentative hN G r) = rightRepresentative hN (G * H) r := by
  obtain ⟨L, hL⟩ := rightRepresentative_spec hN G r
  obtain ⟨M, hM⟩ := rightRepresentative_spec hN H (rightRepresentative hN G r)
  obtain ⟨K, hK⟩ := rightRepresentative_spec hN (G * H) r
  refine left_representative_unique (L := M * L) (M := K) ?_ hK
  calc
    (↑(M * L) : Mat₂) * (r.matrix * (↑(G * H) : Mat₂)) =
        (M : Mat₂) * (((L : Mat₂) * (r.matrix * (G : Mat₂))) * (H : Mat₂)) := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    _ = _ := by rw [hL, hM]

/-- Right multiplication by any integral determinant-one matrix permutes the Hecke indices. -/
def rightPerm {N : ℤ} (hN : 0 < N) (G : SL(2, ℤ)) : Equiv.Perm (Index N) where
  toFun := rightRepresentative hN G
  invFun := rightRepresentative hN G⁻¹
  left_inv r := by rw [rightRepresentative_mul, mul_inv_cancel, rightRepresentative_one]
  right_inv r := by rw [rightRepresentative_mul, inv_mul_cancel, rightRepresentative_one]

/-- Reindex the weight-zero sum of a function invariant under left row operations on
determinant-`N` matrices. -/
theorem sum_right_mul_eq {N : ℤ} (hN : 0 < N) (G : SL(2, ℤ)) {B : Type*} [AddCommMonoid B]
    (f : Mat₂ → B) (hf : ∀ (L : SL(2, ℤ)) (A : Mat₂), A.det = N → f ((L : Mat₂) * A) = f A) :
    (∑ r : Index N, f (r.matrix * (G : Mat₂))) = ∑ r : Index N, f r.matrix := by
  refine Fintype.sum_equiv (rightPerm hN G)
    (fun r => f (r.matrix * (G : Mat₂))) (fun r => f r.matrix) ?_
  intro r
  obtain ⟨L, hL⟩ := rightRepresentative_spec hN G r
  change f (r.matrix * (G : Mat₂)) = f (rightRepresentative hN G r).matrix
  exact (hf L _ (det_right_mul G r)).symm.trans (congrArg f hL)

end D5.S3.Arith.ModularForms.HeckeCosetTriangularRepresentatives
