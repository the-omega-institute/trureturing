/- GID: D5/S3/Arith/Congruence/PrimeRectangleTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/PrimeRectangleTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transfer weighted layer moments through actual residue-prefix kernel caps. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S3.Arith.Congruence.PrimeRectangleTransfer

/-- Actual residue-prefix caps, depending on depth and the old point, transfer
weighted layer moments to the full rectangle load. Kernel normalization
retains the undistorted zero layer. -/
theorem prefix_weighted_rectangle_second_moment_le
    {X I : Type*} [Fintype X] [Fintype I]
    (p H : ℕ) (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (A : Fin (H + 1) → I → X → ℝ) (hA : ∀ e i x, 0 ≤ A e i x)
    (b : Fin (H + 1) → I → ℕ)
    (K : X → Fin (p ^ H) → ℝ)
    (hK0 : ∀ x y, 0 ≤ K x y) (hKsum : ∀ x, ∑ y, K x y = 1)
    (M : ℕ → X → ℝ) (G : ℕ → ℝ)
    (hprefix : ∀ t, 1 ≤ t → t ≤ H → ∀ r x,
      (∑ y : Fin (p ^ H), K x y *
        (if y.val % p ^ t = r % p ^ t then 1 else 0)) ≤ M t x)
    (hG0 : (∑ x, μ x * (∑ i, A 0 i x) ^ 2) ≤ G 0)
    (hG : ∀ t, 1 ≤ t → t ≤ H → ∀ e : Fin (H + 1), e.val ≤ t →
      (∑ x, μ x * M t x * (∑ i, A e i x) ^ 2) ≤ G t) :
    (∑ x, ∑ y : Fin (p ^ H), μ x * K x y *
      (∑ e : Fin (H + 1), ∑ i, A e i x *
        (if y.val % p ^ e.val = b e i % p ^ e.val then 1 else 0)) ^ 2) ≤
      G 0 + ∑ t ∈ Finset.Icc 1 H, (2 * (t : ℝ) + 1) * G t := by
  classical
  let D (e : Fin (H + 1)) (i : I) (y : Fin (p ^ H)) : ℝ :=
    if y.val % p ^ e.val = b e i % p ^ e.val then 1 else 0
  let F (e : Fin (H + 1)) (x : X) : ℝ := ∑ i, A e i x
  let Z (e : Fin (H + 1)) (x : X) (y : Fin (p ^ H)) : ℝ :=
    ∑ i, A e i x * D e i y
  let W (t : ℕ) (x : X) : ℝ := if t = 0 then 1 else M t x
  have hW (t : ℕ) (ht : t ≤ H) (x : X) : 0 ≤ W t x := by
    by_cases ht0 : t = 0
    · simp only [W, if_pos ht0, zero_le_one]
    · simp only [W, if_neg ht0]
      refine le_trans ?_ (hprefix t (by omega) ht 0 x)
      apply Finset.sum_nonneg
      intro y _
      apply mul_nonneg (hK0 x y)
      split_ifs <;> norm_num
  have square_bound (t : ℕ) (ht : t ≤ H) (e : Fin (H + 1)) (he : e.val ≤ t) :
      (∑ x, μ x * W t x * F e x ^ 2) ≤ G t := by
    by_cases ht0 : t = 0
    · have he0 : e = 0 := by
        apply Fin.ext
        simp only [Fin.val_zero]
        omega
      simpa only [ht0, he0, W, if_true, mul_one, F] using hG0
    · simpa only [W, if_neg ht0, F] using hG t (by omega) ht e he
  have coordinate (e f : Fin (H + 1)) (i j : I) (x : X) :
      (∑ y, K x y * D e i y * D f j y) ≤ W (max e.val f.val) x := by
    by_cases hzero : max e.val f.val = 0
    · have he0 : e.val = 0 := by omega
      have hf0 : f.val = 0 := by omega
      have de (y : Fin (p ^ H)) : D e i y = 1 := by
        apply if_pos
        simp only [he0, pow_zero, Nat.mod_one]
      have df (y : Fin (p ^ H)) : D f j y = 1 := by
        apply if_pos
        simp only [hf0, pow_zero, Nat.mod_one]
      simp only [de, df, mul_one, hKsum, W, if_pos hzero, le_refl]
    · simp only [W, if_neg hzero]
      rcases le_total e.val f.val with hef | hfe
      · rw [max_eq_right hef]
        calc
          _ ≤ ∑ y, K x y * D f j y := by
            apply Finset.sum_le_sum
            intro y _
            dsimp only [D]
            split_ifs <;> simp_all
          _ ≤ M f.val x := hprefix f.val (by omega) (by omega) (b f j) x
      · rw [max_eq_left hfe]
        calc
          _ ≤ ∑ y, K x y * D e i y := by
            apply Finset.sum_le_sum
            intro y _
            dsimp only [D]
            split_ifs <;> simp_all
          _ ≤ M e.val x := hprefix e.val (by omega) (by omega) (b e i) x
  have pointwise (e f : Fin (H + 1)) (x : X) :
      (∑ y, K x y * (Z e x y * Z f x y)) ≤ W (max e.val f.val) x * (F e x * F f x) := by
    calc
      _ = ∑ i, ∑ j, A e i x * A f j x *
          (∑ y, K x y * D e i y * D f j y) := by
        dsimp [Z]
        simp only [Finset.sum_mul_sum]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ ∑ i, ∑ j, A e i x * A f j x * W (max e.val f.val) x := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (coordinate e f i j x)
          (mul_nonneg (hA e i x) (hA f j x))
      _ = W (max e.val f.val) x * (F e x * F f x) := by
        dsimp [F]
        simp only [Finset.sum_mul_sum]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have old_pair (e f : Fin (H + 1)) :
      (∑ x, μ x * W (max e.val f.val) x * (F e x * F f x)) ≤
        G (max e.val f.val) := by
    have ht : max e.val f.val ≤ H := by omega
    calc
      _ ≤ ∑ x, (μ x * W (max e.val f.val) x * F e x ^ 2 +
          μ x * W (max e.val f.val) x * F f x ^ 2) / 2 := by
        apply Finset.sum_le_sum
        intro x _
        nlinarith [mul_nonneg (mul_nonneg (hμ x) (hW _ ht x))
          (sq_nonneg (F e x - F f x))]
      _ = ((∑ x, μ x * W (max e.val f.val) x * F e x ^ 2) +
          (∑ x, μ x * W (max e.val f.val) x * F f x ^ 2)) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ G (max e.val f.val) := by
        have he := square_bound _ ht e (le_max_left _ _)
        have hf := square_bound _ ht f (le_max_right _ _)
        linarith
  have pair (e f : Fin (H + 1)) :
      (∑ x, ∑ y, μ x * K x y * (Z e x y * Z f x y)) ≤
        G (max e.val f.val) := by
    calc
      _ = ∑ x, μ x * (∑ y, K x y * (Z e x y * Z f x y)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ ∑ x, μ x * (W (max e.val f.val) x * (F e x * F f x)) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (pointwise e f x) (hμ x)
      _ = ∑ x, μ x * W (max e.val f.val) x * (F e x * F f x) := by
        simp only [mul_assoc]
      _ ≤ _ := old_pair e f
  have max_count (c : ℕ → ℝ) (N : ℕ) :
      (∑ e ∈ Finset.range N, ∑ f ∈ Finset.range N, c (max e f)) =
        ∑ t ∈ Finset.range N, (2 * (t : ℝ) + 1) * c t := by
    induction N with
    | zero => simp
    | succ N ih =>
        have column : (∑ e ∈ Finset.range N, c (max e N)) = (N : ℝ) * c N := by
          have pointwise : ∀ e ∈ Finset.range N, c (max e N) = c N := by
            intro e he
            rw [max_eq_right (Nat.le_of_lt (Finset.mem_range.mp he))]
          simp_rw [Finset.sum_congr rfl pointwise]
          simp
        have row : (∑ f ∈ Finset.range (N + 1), c (max N f)) =
            ((N : ℝ) + 1) * c N := by
          have pointwise : ∀ f ∈ Finset.range (N + 1), c (max N f) = c N := by
            intro f hf
            rw [max_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hf))]
          rw [Finset.sum_congr rfl pointwise]
          simp
        rw [Finset.sum_range_succ]
        simp_rw [Finset.sum_range_succ]
        rw [Finset.sum_add_distrib, ih, column]
        rw [Finset.sum_range_succ] at row
        simp only [max_self] at row
        simp only [max_self]
        rw [row]
        ring
  have coefficient : (∑ e : Fin (H + 1), ∑ f : Fin (H + 1),
      G (max e.val f.val)) =
      G 0 + ∑ t ∈ Finset.Icc 1 H, (2 * (t : ℝ) + 1) * G t := by
    calc
      _ = ∑ e ∈ Finset.range (H + 1), ∑ f ∈ Finset.range (H + 1),
          G (max e f) := by
        have inner (e : ℕ) : (∑ f : Fin (H + 1), G (max e f.val)) =
            ∑ f ∈ Finset.range (H + 1), G (max e f) :=
          Fin.sum_univ_eq_sum_range (fun f : ℕ => G (max e f)) (H + 1)
        simp_rw [inner]
        exact Fin.sum_univ_eq_sum_range (fun e : ℕ =>
          ∑ f ∈ Finset.range (H + 1), G (max e f)) (H + 1)
      _ = ∑ t ∈ Finset.range (H + 1), (2 * (t : ℝ) + 1) * G t :=
        max_count G (H + 1)
      _ = _ := by
        have partition : Finset.range (H + 1) = insert 0 (Finset.Icc 1 H) := by
          ext t
          simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [partition, Finset.sum_insert (by simp)]
        simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
  rw [← coefficient]
  change (∑ x, ∑ y, μ x * K x y * (∑ e, Z e x y) ^ 2) ≤
    ∑ e : Fin (H + 1), ∑ f : Fin (H + 1), G (max e.val f.val)
  calc
    _ = ∑ e, ∑ f, ∑ x, ∑ y, μ x * K x y * (Z e x y * Z f x y) := by
      simp only [pow_two, Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (p ^ H))))
          (t := (Finset.univ : Finset (Fin (H + 1)))),
        Finset.sum_comm (s := (Finset.univ : Finset X))
          (t := (Finset.univ : Finset (Fin (H + 1))))]
    _ ≤ ∑ e : Fin (H + 1), ∑ f : Fin (H + 1), G (max e.val f.val) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      exact pair e f

#print axioms prefix_weighted_rectangle_second_moment_le

end D5.S3.Arith.Congruence.PrimeRectangleTransfer
