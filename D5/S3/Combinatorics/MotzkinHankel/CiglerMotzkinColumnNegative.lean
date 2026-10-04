/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnNegative
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnNegative
   mirror-E: none(waiver:specialized-negative-index-unit-endpoint)
   anchors: []
   utility: none
   digest: The specialized backward sequence has a unit endpoint one index beyond its size. -/

import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDeterminant
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelNegative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnNegative

open Polynomial Finset CiglerMotzkinHankelDefs CiglerMotzkinColumnDefs
open CiglerMotzkinHankelOrthogonal CiglerMotzkinHankelNegative

/-- A zero row gives the negative gap, and reversed monicity gives its first unit endpoint. -/
theorem negative_endpoint (h : ℕ) (g : (ℤ[X])[X]) (hg : g.IsMonicOfDegree h) :
    (∀ gap : ℕ, 1 ≤ gap → gap ≤ h →
      (Matrix.of fun i j : Fin h =>
        ((if i.val < gap then Polynomial.map specialize.toRingHom
            (backward (gap - 1 - i.val))
          else Polynomial.map specialize.toRingHom (orthogonal (i.val - gap))) %ₘ g).coeff
            j.val).det = 0) ∧
    (Matrix.of fun i j : Fin h =>
      ((Polynomial.map specialize.toRingHom (backward (h - i.val))) %ₘ g).coeff j.val).det =
        (-1 : ℤ[X]) ^ (h + 1).choose 2 := by
  classical
  have t_image : specialize tVar = (X : ℤ[X]) := by simp [specialize, tVar]
  have s_image : specialize sVar = (X : ℤ[X]) := by simp [specialize, sVar]
  have backward_zero : Polynomial.map specialize.toRingHom (backward 0) = 0 := by
    simp [backward, t_image, s_image]
  have reflected : ∀ r : ℕ,
      Polynomial.map specialize.toRingHom (backward (r + 1)) =
        -Polynomial.map specialize.toRingHom (orthogonal r) := by
    apply Nat.twoStepInduction
    · simp [backward, orthogonal, t_image, s_image]
    · simp [backward, orthogonal, t_image, s_image]
    · intro r previous current
      rw [show r + 2 + 1 = (r + 1) + 2 by omega, backward,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_sub,
        Polynomial.map_X, Polynomial.map_C]
      rw [current, previous, orthogonal,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_sub,
        Polynomial.map_X, Polynomial.map_C]
      ring
  have monic (r : ℕ) :
      (Polynomial.map specialize.toRingHom (orthogonal r)).IsMonicOfDegree r := by
    constructor
    · rw [(orthogonal_basis r).1.monic.natDegree_map, (orthogonal_basis r).1.natDegree_eq]
    · exact (orthogonal_basis r).1.monic.map _
  have coefficients (r a : ℕ) (larger : r < a) :
      (Polynomial.map specialize.toRingHom (orthogonal r)).coeff a = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [(monic r).natDegree_eq]
    exact larger
  have reversed : ∀ count : ℕ,
      (Matrix.of fun i j : Fin count =>
        (-Polynomial.map specialize.toRingHom (orthogonal (count - 1 - i.val))).coeff
          j.val).det = (-1 : ℤ[X]) ^ (count + 1).choose 2 := by
    intro count
    induction count with
    | zero => simp
    | succ count ih =>
      let A : Matrix (Fin (count + 1)) (Fin (count + 1)) ℤ[X] := Matrix.of fun i j =>
        (-Polynomial.map specialize.toRingHom (orthogonal (count - i.val))).coeff j.val
      have last (i : Fin (count + 1)) (different : i ≠ 0) : A i (Fin.last count) = 0 := by
        have positive : 0 < i.val := by
          have unequal : i.val ≠ 0 := by
            intro equal
            exact different (Fin.ext equal)
          omega
        simp only [A, Matrix.of_apply, coeff_neg, Fin.val_last]
        rw [coefficients (count - i.val) count (by omega), neg_zero]
      have corner : A 0 (Fin.last count) = -1 := by
        simp only [A, Matrix.of_apply, Fin.val_zero, Nat.sub_zero, Fin.val_last, coeff_neg]
        have leading := (monic count).monic.coeff_natDegree
        rw [(monic count).natDegree_eq] at leading
        rw [leading]
      have minor : A.submatrix (0 : Fin (count + 1)).succAbove
          (Fin.last count).succAbove =
          Matrix.of (fun i j : Fin count =>
            (-Polynomial.map specialize.toRingHom (orthogonal (count - 1 - i.val))).coeff
              j.val) := by
        ext i j
        simp only [A, Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_zero,
          Fin.succAbove_last, Fin.val_castSucc, Fin.val_succ]
        rw [show count - (i.val + 1) = count - 1 - i.val by omega]
      change A.det = _
      rw [Matrix.det_succ_column A (Fin.last count), sum_eq_single 0]
      · simp only [Fin.val_zero, Fin.val_last, zero_add, corner]
        have choose_step : (count + 1 + 1).choose 2 =
            (count + 1).choose 2 + (count + 1) := by
          simpa [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ (count + 1) 1
        rw [minor, ih, choose_step, pow_add, pow_succ]
        ring
      · intro i _ different
        rw [last i different]
        ring
      · simp
  constructor
  · intro gap positive within
    let pivot : Fin h := ⟨gap - 1, by omega⟩
    apply Matrix.det_eq_zero_of_row_eq_zero pivot
    intro j
    have top : pivot.val < gap := by dsimp [pivot]; omega
    simp only [Matrix.of_apply, top, if_true]
    have index : gap - 1 - pivot.val = 0 := by simp [pivot]
    rw [index, backward_zero, zero_modByMonic, coeff_zero]
  · have entries (i j : Fin h) :
        ((Polynomial.map specialize.toRingHom (backward (h - i.val))) %ₘ g).coeff j.val =
        (-Polynomial.map specialize.toRingHom (orthogonal (h - 1 - i.val))).coeff j.val := by
      have index : h - i.val = (h - 1 - i.val) + 1 := by omega
      rw [index, reflected, (modByMonic_eq_self_iff hg.monic).mpr]
      rw [degree_neg, (orthogonal_basis _).1.monic.degree_map,
        degree_eq_natDegree (orthogonal_basis _).1.monic.ne_zero,
        (orthogonal_basis _).1.natDegree_eq, degree_eq_natDegree hg.monic.ne_zero,
        hg.natDegree_eq]
      exact_mod_cast (show h - 1 - i.val < h by omega)
    simp only [entries]
    exact reversed h

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnNegative
