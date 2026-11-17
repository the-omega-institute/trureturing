/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionGradingEstimate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Collision degrees control the square-root scale and inverse-length remainders. -/

import Mathlib

/-! Degree bookkeeping and scale estimates for quadratic collision terms. -/

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

/-- A nonvanishing quadratic collision has one label per retained block and
at least two per unretained block. The remaining labels are its degree. -/
theorem collision_degree_decomposition {B : Type*} [Fintype B] [DecidableEq B]
    (m : B → ℕ) (S : Finset B) (hret : ∀ b ∈ S, 1 ≤ m b)
    (hfree : ∀ b ∉ S, 2 ≤ m b) :
    (∑ b, m b) = 2 * Sᶜ.card + S.card +
      ((∑ b ∈ S, (m b - 1)) + ∑ b ∈ Sᶜ, (m b - 2)) := by
  have hr : (∑ b ∈ S, (m b - 1)) + S.card = ∑ b ∈ S, m b := by
    calc
      _ = ∑ b ∈ S, ((m b - 1) + 1) := by simp [Finset.sum_add_distrib]
      _ = _ := Finset.sum_congr rfl (fun b hb => by have := hret b hb; omega)
  have hf : (∑ b ∈ Sᶜ, (m b - 2)) + 2 * Sᶜ.card = ∑ b ∈ Sᶜ, m b := by
    calc
      _ = ∑ b ∈ Sᶜ, ((m b - 2) + 2) := by simp [Finset.sum_add_distrib, Nat.mul_comm]
      _ = _ := Finset.sum_congr rfl (fun b hb => by
        have := hfree b (Finset.mem_compl.mp hb); omega)
  have hsum := S.sum_add_sum_compl m
  omega

private theorem collision_degree_zero_iff {B : Type*} [Fintype B] [DecidableEq B]
    (m : B → ℕ) (S : Finset B) (hret : ∀ b ∈ S, 1 ≤ m b)
    (hfree : ∀ b ∉ S, 2 ≤ m b) :
    ((∑ b ∈ S, (m b - 1)) + ∑ b ∈ Sᶜ, (m b - 2)) = 0 ↔
      (∀ b ∈ S, m b = 1) ∧ (∀ b ∉ S, m b = 2) := by
  constructor
  · intro hd
    constructor
    · intro b hb
      have hle := Finset.single_le_sum (fun b _ => Nat.zero_le (m b - 1)) hb
      have hp := hret b hb
      omega
    · intro b hb
      have hle := Finset.single_le_sum (fun b _ => Nat.zero_le (m b - 2))
        (Finset.mem_compl.mpr hb)
      have hp := hfree b hb
      omega
  · rintro ⟨hr, hf⟩
    have hr0 : (∑ b ∈ S, (m b - 1)) = 0 :=
      Finset.sum_eq_zero (fun b hb => by rw [hr b hb]; rfl)
    have hf0 : (∑ b ∈ Sᶜ, (m b - 2)) = 0 :=
      Finset.sum_eq_zero (fun b hb => by rw [hf b (Finset.mem_compl.mp hb)]; rfl)
    rw [hr0, hf0]

private theorem collision_scale_identity (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (q r d : ℕ) :
    L ^ (q + d) * H ^ q * (Real.sqrt (H * L)) ^ r =
      (Real.sqrt (H * L)) ^ (2 * q + r + d) * (Real.sqrt (L / H)) ^ d := by
  have hs : (Real.sqrt (H * L)) ^ 2 = H * L :=
    Real.sq_sqrt (mul_nonneg hH.le hL)
  have hsr : Real.sqrt (H * L) * Real.sqrt (L / H) = L := by
    rw [← Real.sqrt_mul (mul_nonneg hH.le hL),
      show H * L * (L / H) = L ^ 2 by field_simp [hH.ne']]
    exact Real.sqrt_sq hL
  calc
    _ = (H * L) ^ q * (Real.sqrt (H * L)) ^ r * L ^ d := by
      rw [pow_add, mul_pow]
      ring
    _ = (Real.sqrt (H * L)) ^ (2 * q) * (Real.sqrt (H * L)) ^ r *
        (Real.sqrt (H * L) * Real.sqrt (L / H)) ^ d := by
      rw [pow_mul, hs, hsr]
    _ = _ := by rw [mul_pow, pow_add, pow_add]; ring

/-- A collision configuration of degree `d` gains exactly `d` powers of the
square-root scale ratio, with a coefficient bounded solely by its total order. -/
theorem collision_grading_bound (C H L : ℝ) (hC : 1 ≤ C) (hH : 0 < H)
    (hL : 0 ≤ L) (q r d : ℕ) :
    ((C + 1) * L) ^ (q + d) * C ^ (q + 1) * H ^ q *
        (Real.sqrt (H * L)) ^ r ≤
      (C + 1) ^ (2 * q + r + d + 1) *
        (Real.sqrt (H * L)) ^ (2 * q + r + d) * (Real.sqrt (L / H)) ^ d := by
  have hC0 : 0 ≤ C := by linarith
  have hCp : 1 ≤ C + 1 := by linarith
  have hcoeff : (C + 1) ^ (q + d) * C ^ (q + 1) ≤
      (C + 1) ^ (2 * q + r + d + 1) := by
    calc
      _ ≤ (C + 1) ^ (q + d) * (C + 1) ^ (q + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC0 (by linarith) _)
          (pow_nonneg (by linarith) _)
      _ = (C + 1) ^ ((q + d) + (q + 1)) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hCp (by omega)
  calc
    _ = ((C + 1) ^ (q + d) * C ^ (q + 1)) *
        (L ^ (q + d) * H ^ q * (Real.sqrt (H * L)) ^ r) := by
      rw [mul_pow]
      ring
    _ ≤ (C + 1) ^ (2 * q + r + d + 1) *
        (L ^ (q + d) * H ^ q * (Real.sqrt (H * L)) ^ r) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by rw [collision_scale_identity H L hH hL]; ring

/-- The multiplicity grading gives the uniform analytic bound and identifies
its zero-degree configurations as retained singletons and unretained pairs. -/
theorem collision_partition_grading_bound {B : Type*} [Fintype B] [DecidableEq B]
    (m : B → ℕ) (S : Finset B) (hret : ∀ b ∈ S, 1 ≤ m b)
    (hfree : ∀ b ∉ S, 2 ≤ m b) (C H L : ℝ) (hC : 1 ≤ C)
    (hH : 0 < H) (hL : 0 ≤ L) :
    let k := ∑ b, m b
    let δ := (∑ b ∈ S, (m b - 1)) + ∑ b ∈ Sᶜ, (m b - 2)
    (((C + 1) * L) ^ (k - Fintype.card B) * C ^ (Sᶜ.card + 1) *
        H ^ Sᶜ.card * (Real.sqrt (H * L)) ^ S.card ≤
      (C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k * (Real.sqrt (L / H)) ^ δ) ∧
      (δ = 0 ↔ (∀ b ∈ S, m b = 1) ∧ (∀ b ∉ S, m b = 2)) := by
  dsimp only
  have hk := collision_degree_decomposition m S hret hfree
  have ht := S.card_compl_add_card
  constructor
  · have hexp : (∑ b, m b) - Fintype.card B = Sᶜ.card +
        ((∑ b ∈ S, (m b - 1)) + ∑ b ∈ Sᶜ, (m b - 2)) := by omega
    rw [hexp, hk]
    exact collision_grading_bound C H L hC hH hL Sᶜ.card S.card _
  · exact collision_degree_zero_iff m S hret hfree

/-- Every positive collision degree is bounded by one square-root scale ratio
when the length scale dominates the coefficient scale. -/
theorem collision_positive_grading_bound (C H L : ℝ) (hC : 1 ≤ C)
    (hHL : L ≤ H) (hL : 1 ≤ L) (q r d : ℕ) (hd : 1 ≤ d) :
    ((C + 1) * L) ^ (q + d) * C ^ (q + 1) * H ^ q *
        (Real.sqrt (H * L)) ^ r ≤
      (C + 1) ^ (2 * q + r + d + 1) *
        (Real.sqrt (H * L)) ^ (2 * q + r + d) * Real.sqrt (L / H) := by
  have hH : 0 < H := by linarith
  have hL0 : 0 ≤ L := by linarith
  refine (collision_grading_bound C H L hC hH hL0 q r d).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [pow_one] using pow_le_pow_of_le_one
    (Real.sqrt_nonneg (L / H))
    (Real.sqrt_le_one.mpr ((div_le_one hH).mpr hHL)) hd

/-- Removing one free component from a zero-degree configuration gains an
inverse length factor, without requiring a bound on the top distinct moment. -/
theorem collision_free_component_bound (C H L : ℝ) (hC : 1 ≤ C)
    (hH : 0 < H) (hL : 0 ≤ L) (n r : ℕ) :
    ((C + 1) * L) ^ (n + 1) * C ^ (n + 1) * H ^ n *
        (Real.sqrt (H * L)) ^ r ≤
      ((C + 1) ^ (2 * (n + 1) + r + 1) *
        (Real.sqrt (H * L)) ^ (2 * (n + 1) + r)) / H := by
  apply (le_div_iff₀ hH).mpr
  calc
    _ = ((C + 1) * L) ^ (n + 1) * C ^ (n + 1) * H ^ (n + 1) *
        (Real.sqrt (H * L)) ^ r := by rw [pow_succ H]; ring
    _ ≤ ((C + 1) * L) ^ (n + 1) * C ^ ((n + 1) + 1) * H ^ (n + 1) *
        (Real.sqrt (H * L)) ^ r := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Real.sqrt_nonneg _) _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hH.le _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC (by omega))
        (pow_nonneg (mul_nonneg (by linarith) hL) _)
    _ ≤ _ := by
      simpa only [Nat.add_zero, pow_zero, mul_one] using
        collision_grading_bound C H L hC hH hL (n + 1) r 0

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
