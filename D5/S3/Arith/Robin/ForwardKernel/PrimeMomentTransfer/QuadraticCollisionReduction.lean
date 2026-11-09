/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCollisionReduction
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCollisionReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic tuple reduction isolates errors at repeated shifts. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ArithmeticTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.IndexEqualityPatterns

/-! Quadratic reductions and their local error support. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private def linearPower (s y : ℝ) (r : ℕ) : ℝ :=
  (red r s).1 * y + (red r s).2

private lemma linearPower_error (s y T : ℝ) (hT : 1 ≤ T)
    (hy : |y| ≤ T) (ha : |s - 2| ≤ T) (hb : |s - 1| ≤ T)
    (r : ℕ) (hr : 2 ≤ r) (hr4 : r ≤ 4) :
    |y ^ r - linearPower s y r| ≤
      (8 * T) ^ (r - 2) * |y ^ 2 - (s - 2) * y - (s - 1)| := by
  by_cases hq : y ^ 2 = (s - 2) * y + (s - 1)
  · have he : y ^ r - linearPower s y r = 0 := by
      rw [red_pow s y hq r]
      simp only [linearPower, sub_self]
    rw [he, abs_zero]
    positivity
  let a := s - 2
  let b := s - 1
  have hT0 : 0 ≤ T := by linarith
  have hδ : 0 ≤ |y ^ 2 - a * y - b| := abs_nonneg _
  have h3 : |y + a| ≤ 8 * T := (abs_add_le _ _).trans (by linarith)
  have h4 : |y ^ 2 + a * y + a ^ 2 + b| ≤ (8 * T) ^ 2 := by
    calc
      _ ≤ |y| ^ 2 + |a| * |y| + |a| ^ 2 + |b| := by
        simp only [← abs_pow, ← abs_mul]
        exact (abs_add_le (y ^ 2 + a * y + a ^ 2) b).trans
            (add_le_add ((abs_add_le (y ^ 2 + a * y) (a ^ 2)).trans
              (add_le_add (abs_add_le (y ^ 2) (a * y)) le_rfl)) le_rfl)
      _ ≤ T ^ 2 + T * T + T ^ 2 + T := by
        gcongr
      _ ≤ (8 * T) ^ 2 := by nlinarith
  interval_cases r
  · simp [linearPower, red, pow_two]
    ring_nf
    exact le_rfl
  · have he : y ^ 3 - linearPower s y 3 =
        (y + a) * (y ^ 2 - a * y - b) := by dsimp [linearPower, red, a, b]; ring
    rw [he, abs_mul]
    simpa using mul_le_mul_of_nonneg_right h3 hδ
  · have he : y ^ 4 - linearPower s y 4 =
        (y ^ 2 + a * y + a ^ 2 + b) * (y ^ 2 - a * y - b) := by
      dsimp [linearPower, red, a, b]; ring
    rw [he, abs_mul]
    simpa using mul_le_mul_of_nonneg_right h4 hδ

private lemma linearPower_bound (s y T : ℝ) (hT : 1 ≤ T)
    (hy : |y| ≤ T) (ha : |s - 2| ≤ T) (hb : |s - 1| ≤ T)
    (r : ℕ) (hr : 1 ≤ r) (hr4 : r ≤ 4) :
    |linearPower s y r| ≤ (8 * T) ^ r := by
  have hT0 : 0 ≤ T := by linarith
  by_cases hr2 : 2 ≤ r
  · have he := linearPower_error s y T hT hy ha hb r hr2 hr4
    have hd : |y ^ 2 - (s - 2) * y - (s - 1)| ≤ 3 * T ^ 2 := by
      calc
        _ ≤ |y| ^ 2 + |s - 2| * |y| + |s - 1| := by
          simp only [← abs_pow, ← abs_mul]
          exact (abs_sub _ _).trans
            (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ T ^ 2 + T * T + T := by gcongr
        _ ≤ 3 * T ^ 2 := by nlinarith
    calc
      |linearPower s y r| ≤ |y ^ r| + |y ^ r - linearPower s y r| := by
        have heq : linearPower s y r = y ^ r + (linearPower s y r - y ^ r) := by ring
        conv_lhs => rw [heq]
        simpa only [abs_sub_comm] using abs_add_le (y ^ r) (linearPower s y r - y ^ r)
      _ ≤ T ^ r + (8 * T) ^ (r - 2) * (3 * T ^ 2) := by
        apply add_le_add
        · simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg y) hy r
        · exact he.trans (mul_le_mul_of_nonneg_left hd (by positivity))
      _ ≤ (8 * T) ^ r := by interval_cases r <;> norm_num <;> nlinarith [sq_nonneg T]
  · have : r = 1 := by omega
    subst r
    simpa [linearPower, red] using hy.trans (show T ≤ 8 * T by linarith)

private lemma product_difference_bound (D : Finset ℕ) (f g u : ℕ → ℝ)
    (hu : ∀ e ∈ D, 0 ≤ u e)
    (hf : ∀ e ∈ D, |f e| ≤ u e) (hg : ∀ e ∈ D, |g e| ≤ u e) :
    |∏ e ∈ D, f e - ∏ e ∈ D, g e| ≤
      ∑ e ∈ D, |f e - g e| * ∏ v ∈ D.erase e, u v := by
  have he := Finset.prod_add_ordered D g (fun e => f e - g e)
  simp only [add_sub_cancel] at he
  rw [show (∏ e ∈ D, f e) - ∏ e ∈ D, g e =
      ∑ e ∈ D, (f e - g e) * (∏ v ∈ D with v < e, f v) *
        ∏ v ∈ D with e < v, g v by linarith [he]]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e heD
  have hprod (A : Finset ℕ) (hA : A ⊆ D) (v : ℕ → ℝ)
      (hv : ∀ e ∈ D, |v e| ≤ u e) : |∏ e ∈ A, v e| ≤ ∏ e ∈ A, u e := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun e he => hv e (hA he))
  have hdisj : Disjoint (D.filter (fun v => v < e)) (D.filter (fun v => e < v)) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    have := (Finset.mem_filter.mp hv).2
    have := (Finset.mem_filter.mp hw).2
    omega
  have herase : D.erase e = (D.filter (fun v => v < e)) ∪ (D.filter (fun v => e < v)) := by
    ext v
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hne, hv⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, h⟩
    · rintro (⟨hv, h⟩ | ⟨hv, h⟩)
      · exact ⟨ne_of_lt h, hv⟩
      · exact ⟨ne_of_gt h, hv⟩
  rw [abs_mul, abs_mul]
  calc
    _ ≤ |f e - g e| * (∏ v ∈ D with v < e, u v) * ∏ v ∈ D with e < v, u v := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hprod _ (Finset.filter_subset _ _) f hf) (abs_nonneg _))
        (hprod _ (Finset.filter_subset _ _) g hg) (abs_nonneg _)
        (mul_nonneg (abs_nonneg _)
          (Finset.prod_nonneg (fun v hv => hu v (Finset.mem_filter.mp hv).1)))
    _ = _ := by rw [herase, Finset.prod_union hdisj]; ring

/-- The subset expansion of the reduced tuple is the product of the reduced powers. -/
private theorem reducedAt_eq_product {k : ℕ} (s : ℝ) (n : ℕ) (d : Fin k → ℕ) :
    reducedAt s n d =
      ∏ e ∈ Finset.univ.image d,
        ((red (mult d e) s).1 * (ArithmeticFunction.vonMangoldt (n + e) - 1) +
          (red (mult d e) s).2) := by
  rw [Finset.prod_add]
  unfold reducedAt
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.prod_mul_distrib]
  ring

/-- The reduction error of a tuple of at most four shifts is supported on repeated shifts. -/
theorem product_reducedAt_error_bound {k : ℕ} (hk : k ≤ 4)
    (s T : ℝ) (hT : 1 ≤ T) (hs2 : |s - 2| ≤ T) (hs1 : |s - 1| ≤ T)
    (n : ℕ) (d : Fin k → ℕ)
    (hy : ∀ e ∈ Finset.univ.image d, |ArithmeticFunction.vonMangoldt (n + e) - 1| ≤ T) :
    |(∏ i, (ArithmeticFunction.vonMangoldt (n + d i) - 1)) - reducedAt s n d| ≤
      (8 * T) ^ (k - 2) *
        ∑ e ∈ (Finset.univ.image d).filter (fun e => 2 ≤ mult d e),
          |(ArithmeticFunction.vonMangoldt (n + e) - 1) ^ 2 -
            (s - 2) * (ArithmeticFunction.vonMangoldt (n + e) - 1) - (s - 1)| := by
  classical
  let D := Finset.univ.image d
  let y := fun e => ArithmeticFunction.vonMangoldt (n + e) - 1
  have hm (e : ℕ) (he : e ∈ D) : 1 ≤ mult d e ∧ mult d e ≤ 4 := by
    constructor
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
      change 1 ≤ (Finset.univ.filter (fun j => d j = e)).card
      exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    · exact (Finset.card_filter_le _ _).trans (by simpa using hk)
  have hsum : ∑ e ∈ D, mult d e = k := by
    simpa only [mult, D, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_univ, Fintype.card_fin] using
      (Finset.sum_comp (s := (Finset.univ : Finset (Fin k))) (fun _ : ℕ => (1 : ℕ)) d).symm
  rw [reducedAt_eq_product, Finset.prod_comp y d]
  change |(∏ e ∈ D, y e ^ mult d e) - ∏ e ∈ D, linearPower s (y e) (mult d e)| ≤ _
  calc
    _ ≤ ∑ e ∈ D, |y e ^ mult d e - linearPower s (y e) (mult d e)| *
        ∏ v ∈ D.erase e, (8 * T) ^ mult d v := by
      apply product_difference_bound
      · intro e _; positivity
      · intro e he
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hy e he).trans (by linarith)) _
      · intro e he
        exact linearPower_bound s (y e) T hT (hy e he) hs2 hs1 _ (hm e he).1 (hm e he).2
    _ ≤ ∑ e ∈ D, if 2 ≤ mult d e then
        (8 * T) ^ (k - 2) * |y e ^ 2 - (s - 2) * y e - (s - 1)| else 0 := by
      apply Finset.sum_le_sum
      intro e he
      by_cases hm2 : 2 ≤ mult d e
      · rw [ite_eq_left hm2]
        have heq : mult d e + ∑ v ∈ D.erase e, mult d v = k := by
          rw [Finset.add_sum_erase D _ he]
          exact hsum
        calc
          _ ≤ ((8 * T) ^ (mult d e - 2) *
              |y e ^ 2 - (s - 2) * y e - (s - 1)|) *
                ∏ v ∈ D.erase e, (8 * T) ^ mult d v := by
            gcongr
            exact linearPower_error s (y e) T hT (hy e he) hs2 hs1 _ hm2 (hm e he).2
          _ = _ := by
            rw [Finset.prod_pow_eq_pow_sum]
            have hexp : mult d e - 2 + ∑ v ∈ D.erase e, mult d v = k - 2 := by omega
            rw [mul_right_comm, ← pow_add, hexp]
      · have hm1 : mult d e = 1 := by have := (hm e he).1; omega
        simp [hm1, linearPower, red]
    _ = _ := by rw [← Finset.sum_filter, Finset.mul_sum]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
