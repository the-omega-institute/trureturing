/- GID: D5/S3/Combinatorics/Partitions/SpechtSchurBialternant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtSchurBialternant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected tableau and Schur suppliers for the ordinary Specht Frobenius comparison. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected declarations from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Namespaces and root references adapted to the existing D5 source chain.
License, selection, consumers and retirement:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtSchurAlternant
import Mathlib.Tactic.LinearCombination

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

open MvPolynomial Finset

namespace TauCeti

variable {R : Type*} [CommRing R]

private theorem alternant_eq_X_last_pow_mul_det {n : ℕ} (e : Fin (n + 1) → ℕ)
    (he : ∀ j : Fin n, e j.succ ≤ e j.castSucc) :
    alternant (Fin (n + 1)) R e = X (Fin.last n) ^ e (Fin.last n) *
      (Matrix.of fun i j : Fin n => (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^ e j.castSucc -
        X i.castSucc ^ e j.succ * X (Fin.last n) ^ (e j.castSucc - e j.succ)).det := by
  set y : MvPolynomial (Fin (n + 1)) R := X (Fin.last n) with hy

  set U : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) R) :=
    Matrix.of fun k j =>
      (if k = j then 1 else 0) - if (k : ℕ) = j + 1 then y ^ (e j - e k) else 0 with hU
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular U fun k j hkj => ?_]
    · simp [hU]
    · have hkj' : k < j := OrderDual.toDual_lt_toDual.mp hkj
      have h2 : (k : ℕ) ≠ j + 1 := by omega
      simp [hU, hkj'.ne, h2]
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) R) :=
    Matrix.of fun i j => X i ^ e j with hA
  have hAU_last : ∀ i, (A * U) i (Fin.last n) = X i ^ e (Fin.last n) := by
    intro i
    rw [Matrix.mul_apply]
    simp only [hU, hA, Matrix.of_apply, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ite_true]
    rw [sum_eq_zero fun k _ => ite_eq_right (by simp only [Fin.val_last]; omega), sub_zero]
  have hAU_cs : ∀ i (j : Fin n), (A * U) i j.castSucc =
      X i ^ e j.castSucc - X i ^ e j.succ * y ^ (e j.castSucc - e j.succ) := by
    intro i j
    rw [Matrix.mul_apply]
    simp only [hU, hA, Matrix.of_apply, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ite_true]
    congr 1
    rw [sum_eq_single j.succ (fun k _ hk => ite_eq_right fun h => hk (Fin.ext (by
      simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢; omega))) (fun h => absurd (mem_univ _) h)]
    simp
  have hrow : ∀ j : Fin n, (A * U) (Fin.last n) j.castSucc = 0 := by
    intro j
    rw [hAU_cs, ← pow_add, Nat.add_sub_cancel' (he j), sub_self]

  rw [alternant_def, ← hA, ← mul_one (Matrix.det _), ← hdetU, ← Matrix.det_mul,
    Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  simp only [hrow, mul_zero, zero_mul, sum_const_zero, zero_add, Fin.succAbove_last,
    hAU_last, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, ← hy]
  exact congrArg (y ^ e (Fin.last n) * Matrix.det ·)
    (Matrix.ext fun i j => by rw [Matrix.submatrix_apply, hAU_cs, Matrix.of_apply])

theorem alternant_eq_prod_mul_sum_interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram)
    (hμ : μ.colLen 0 ≤ n + 1) :
    alternant (Fin (n + 1)) R (fun j => μ.betaNumber (n + 1) j) =
      (∏ i : Fin n, (X i.castSucc - X (Fin.last n))) *
        ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          X (Fin.last n) ^ (μ.card - ν.card) *
            rename Fin.castSucc (alternant (Fin n) R fun j => ν.betaNumber n j) := by
  set y : MvPolynomial (Fin (n + 1)) R := X (Fin.last n) with hy
  set e : Fin (n + 1) → ℕ := fun j => μ.betaNumber (n + 1) j with he
  have he_anti : ∀ j : Fin n, e j.succ ≤ e j.castSucc := by
    intro j
    have := μ.rowLen_anti j (j + 1) (Nat.le_succ _)
    simp only [he, YoungDiagram.betaNumber_def, Fin.val_succ, Fin.val_castSucc]
    omega

  set N : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (n + 1)) R) := Matrix.of fun i j =>
    ∑ m ∈ Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j),
      X i.castSucc ^ (m + (n - 1 - j)) * y ^ (μ.rowLen j - m) with hN
  have hblock : (Matrix.of fun i j : Fin n => (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^
      e j.castSucc - X i.castSucc ^ e j.succ * y ^ (e j.castSucc - e j.succ)) =
      Matrix.of fun i j : Fin n => (X i.castSucc - y) * N i j := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.of_apply, Matrix.of_apply, hN, Matrix.of_apply]
    set a := μ.rowLen ((j : ℕ) + 1)
    set b := μ.rowLen j
    set c := n - 1 - j
    have hab : a ≤ b := μ.rowLen_anti _ _ (Nat.le_succ _)
    have h1 : e j.castSucc = b + 1 + c := by
      simp only [he, YoungDiagram.betaNumber_def, Fin.val_castSucc]
      omega
    have h2 : e j.succ = a + c := by
      simp only [he, YoungDiagram.betaNumber_def, Fin.val_succ]
      omega
    have h3 : e j.castSucc - e j.succ = b + 1 - a := by rw [h1, h2]; omega

    have hab1 : a ≤ b + 1 := Nat.le_succ_of_le hab
    have hgeom := (Commute.all (X i.castSucc : MvPolynomial (Fin (n + 1)) R) y).geom_sum₂_Ico_mul
      hab1
    have hsum : ∑ m ∈ Icc a b, (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^ (m + c) *
        y ^ (b - m) = X i.castSucc ^ c *
          ∑ m ∈ Ico a (b + 1), X i.castSucc ^ m * y ^ (b + 1 - 1 - m) := by
      rw [Finset.Ico_add_one_right_eq_Icc, Finset.mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [pow_add, Nat.add_sub_cancel]
      ring
    rw [hsum, h3, h1, h2]
    linear_combination (-(X i.castSucc ^ c : MvPolynomial (Fin (n + 1)) R)) * hgeom

  have hsum : ∑ ν ∈ YoungDiagram.interlacingShapes n μ, y ^ (μ.card - ν.card) *
      rename Fin.castSucc (alternant (Fin n) R fun j => ν.betaNumber n j) =
      ∑ r ∈ Fintype.piFinset fun j : Fin n => Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j),
        y ^ (μ.card - ∑ j, r j) *
          rename Fin.castSucc (alternant (Fin n) R fun j => r j + (n - 1 - j)) := by
    simp only [YoungDiagram.betaNumber_def]
    rw [← YoungDiagram.sum_interlacingShapes_eq_sum_piFinset hμ]
    refine sum_congr rfl fun ν hν => ?_
    rw [YoungDiagram.card_eq_sum_range_rowLen ν (YoungDiagram.mem_interlacingShapes.mp hν).2,
      ← Fin.sum_univ_eq_sum_range]

  have hdet_sum : (Matrix.of fun i j : Fin n =>
      ∑ m ∈ Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j),
        X i.castSucc ^ (m + (n - 1 - j)) * y ^ (μ.rowLen j - m)).det =
      ∑ r ∈ Fintype.piFinset (fun j : Fin n =>
        Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j)),
        (Matrix.of fun i j : Fin n =>
          X i.castSucc ^ (r j + (n - 1 - j)) * y ^ (μ.rowLen j - r j)).det := by
    simp_rw [← Matrix.det_transpose (Matrix.of _), Matrix.det.eq_1]
    have h := (Matrix.detRowAlternating (R := MvPolynomial (Fin (n + 1)) R)
      (n := Fin n)).toMultilinearMap.map_sum_finset
        (fun j (m : ℕ) i => X i.castSucc ^ (m + (n - 1 - j)) * y ^ (μ.rowLen j - m))
        (fun j : Fin n => Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j))
    simp only [AlternatingMap.coe_multilinearMap] at h
    convert h using 3 with r
    · congr 1
      ext j i
      simp [Finset.sum_apply]
    · rfl
  have hel : e (Fin.last n) = μ.rowLen n := by simp [he, YoungDiagram.betaNumber_def]
  rw [alternant_eq_X_last_pow_mul_det e he_anti, ← hy, hel, hblock, Matrix.det_mul_column, hN,
    hdet_sum, hsum, mul_left_comm, Finset.mul_sum]
  congr 1
  refine sum_congr rfl fun r hr => ?_
  have hr' : ∀ j ∈ univ, r j ≤ μ.rowLen j := fun j _ =>
    (mem_Icc.mp (Fintype.mem_piFinset.mp hr j)).2
  have hdet : (Matrix.of fun i j : Fin n =>
      (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^ (r j + (n - 1 - j)) *
        y ^ (μ.rowLen j - r j)).det = (∏ j : Fin n, y ^ (μ.rowLen j - r j)) *
          rename Fin.castSucc (alternant (Fin n) R fun j => r j + (n - 1 - j)) := by
    rw [alternant_def, AlgHom.map_det, ← Matrix.det_mul_row]
    congr 1
    ext i j : 1
    simp [mul_comm]
  have hcard : μ.card = ∑ j : Fin n, μ.rowLen j + μ.rowLen n := by
    rw [YoungDiagram.card_eq_sum_range_rowLen μ hμ, sum_range_succ, Fin.sum_univ_eq_sum_range]
  have hle : ∑ j : Fin n, r j ≤ ∑ j : Fin n, μ.rowLen j := sum_le_sum hr'
  rw [hdet, ← mul_assoc, prod_pow_eq_pow_sum, ← pow_add, sum_tsub_distrib _ hr', hcard]
  congr 2
  omega

theorem injective_staircase (N : ℕ) : Function.Injective fun j : Fin N => N - 1 - (j : ℕ) :=
  fun i j hij => by
    have := i.isLt
    have := j.isLt
    exact Fin.ext (by simp only at hij; omega)

theorem diagramSchurPoly_mul_alternant (N : ℕ) (μ : _root_.YoungDiagram) (hμ : μ.colLen 0 ≤ N) :
    diagramSchurPoly N R μ * alternant (Fin N) R (fun j => N - 1 - j) =
      alternant (Fin N) R fun j => μ.betaNumber N j := by
  have hbot : ∀ i, (⊥ : _root_.YoungDiagram).rowLen i = 0 := fun i =>
    Nat.eq_zero_of_not_pos fun h =>
      _root_.YoungDiagram.notMem_bot _ (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr h)
  have hbotc : (⊥ : _root_.YoungDiagram).colLen 0 = 0 :=
    Nat.eq_zero_of_not_pos fun h =>
      _root_.YoungDiagram.notMem_bot _ (_root_.YoungDiagram.mem_iff_lt_colLen.mpr h)
  induction N generalizing μ with
  | zero =>
    have hμ0 : μ = ⊥ := YoungDiagram.rowLen_injective (funext fun i => by
      rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.zero_le i)), hbot])
    subst hμ0
    simp [diagramSchurPoly_bot, alternant_def, YoungDiagram.betaNumber_def]
  | succ n ih =>

    have hvan : alternant (Fin (n + 1)) R (fun j => n - j) =
        (∏ i : Fin n, (X i.castSucc - X (Fin.last n))) *
          rename Fin.castSucc (alternant (Fin n) R fun j => n - 1 - j) := by
      have hshapes : YoungDiagram.interlacingShapes n ⊥ = {⊥} := by
        ext ν
        simp only [YoungDiagram.mem_interlacingShapes, mem_singleton]
        refine ⟨fun h => le_bot_iff.mp h.1.le, ?_⟩
        rintro rfl
        exact ⟨YoungDiagram.interlacedBy_iff.mpr fun i => by simp [hbot], by simp [hbotc]⟩
      simpa [hshapes, hbot, YoungDiagram.betaNumber_def] using
        alternant_eq_prod_mul_sum_interlacingShapes (R := R) n ⊥ (by simp [hbotc])
    simp only [Nat.add_sub_cancel]
    rw [diagramSchurPoly_eq_sum_interlacingShapes, hvan,
      alternant_eq_prod_mul_sum_interlacingShapes n μ hμ, sum_mul, mul_sum]
    refine sum_congr rfl fun ν hν => ?_
    rw [← ih ν (YoungDiagram.mem_interlacingShapes.mp hν).2, map_mul]
    ring

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
