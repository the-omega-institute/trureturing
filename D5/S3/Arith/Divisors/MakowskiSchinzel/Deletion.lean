/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/Deletion
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/Deletion
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Finite product bounds and the necessary reciprocal mass condition. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.Reduction

/-! Reciprocal mass forced by finite deletion inequalities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel

open Finset

/-- A finite product is bounded by the geometric sum of its total increment. -/
private theorem prod_one_add_le_geom_bound (s : Finset ℕ) (x : ℕ → ℚ) (t : ℚ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hs : ∑ i ∈ s, x i ≤ t) :
    ∏ i ∈ s, (1 + x i) ≤ ∑ j ∈ range (s.card + 1), t ^ j := by
  classical
  have ht : 0 ≤ t := (sum_nonneg hx).trans hs
  revert hx hs
  refine s.strongInductionOn ?_
  intro s ih hx hs
  by_cases he : s = ∅
  · subst s
    simp
  have hn : 0 < s.card := card_pos.mpr (nonempty_iff_ne_empty.mpr he)
  have hp (i : ℕ) (hi : i ∈ s) :
      ∏ j ∈ s.filter (· < i), (1 + x j) ≤ ∑ j ∈ range s.card, t ^ j := by
    have hsub : s.filter (· < i) ⊂ s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _, ?_⟩
      intro h
      have : i ∈ s.filter (· < i) := h.symm ▸ hi
      simpa using this
    have hsum : ∑ j ∈ s.filter (· < i), x j ≤ t :=
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (by intro j hj _; exact hx j hj)).trans hs
    have hh := ih _ hsub (fun j hj => hx j (mem_filter.mp hj).1) hsum
    exact hh.trans (sum_le_sum_of_subset_of_nonneg
      (range_mono (by have := card_lt_card hsub; omega))
      (by intro j _ _; exact pow_nonneg ht j))
  rw [prod_one_add_ordered]
  calc
    1 + ∑ i ∈ s, x i * ∏ j ∈ s.filter (· < i), (1 + x j) ≤
        1 + ∑ i ∈ s, x i * ∑ j ∈ range s.card, t ^ j := by
      refine add_le_add (le_refl 1) ?_
      exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hp i hi) (hx i hi)
    _ = 1 + (∑ i ∈ s, x i) * ∑ j ∈ range s.card, t ^ j := by
      rw [sum_mul]
    _ ≤ 1 + t * ∑ j ∈ range s.card, t ^ j := by
      refine add_le_add (le_refl 1) ?_
      exact mul_le_mul_of_nonneg_right hs (sum_nonneg fun j _ => pow_nonneg ht j)
    _ = ∑ j ∈ range (s.card + 1), t ^ j := by
      rw [sum_range_succ']
      simp_rw [pow_succ', ← mul_sum]
      ring

/-- The finite geometric product bound has equality exactly in its degenerate cases. -/
theorem prod_one_add_le_geom (s : Finset ℕ) (x : ℕ → ℚ) (t : ℚ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hs : ∑ i ∈ s, x i ≤ t) :
    (∏ i ∈ s, (1 + x i) ≤ ∑ j ∈ range (s.card + 1), t ^ j) ∧
      ((∏ i ∈ s, (1 + x i) = ∑ j ∈ range (s.card + 1), t ^ j) ↔
        s.card = 0 ∨ t = 0 ∨ (s.card = 1 ∧ ∑ i ∈ s, x i = t)) := by
  classical
  have ht : 0 ≤ t := (sum_nonneg hx).trans hs
  refine ⟨prod_one_add_le_geom_bound s x t hx hs, ?_⟩
  constructor
  · intro heq
    by_cases hc0 : s.card = 0
    · exact Or.inl hc0
    by_cases ht0 : t = 0
    · exact Or.inr (Or.inl ht0)
    by_cases hc1 : s.card = 1
    · obtain ⟨a, ha⟩ := card_eq_one.mp hc1
      have hxt : ∑ i ∈ s, x i = t := by
        rw [ha] at heq ⊢
        simpa [sum_range_succ] using heq
      exact Or.inr (Or.inr ⟨hc1, hxt⟩)
    have hc2 : 2 ≤ s.card := by omega
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hG : 1 < ∑ j ∈ range s.card, t ^ j := by
      have htwo : 1 + t ≤ ∑ j ∈ range s.card, t ^ j := by
        calc
          1 + t = ∑ j ∈ range 2, t ^ j := by simp [sum_range_succ]
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono hc2)
            (by intro j _ _; exact pow_nonneg ht j)
      linarith
    have hstrict : ∏ i ∈ s, (1 + x i) < ∑ j ∈ range (s.card + 1), t ^ j := by
      by_cases hz : ∀ i ∈ s, x i = 0
      · have hprod : ∏ i ∈ s, (1 + x i) = 1 :=
          prod_eq_one (by intro i hi; simp [hz i hi])
        have hinc : (∑ j ∈ range s.card, t ^ j) ≤
            ∑ j ∈ range (s.card + 1), t ^ j :=
          sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
            (by intro j _ _; exact pow_nonneg ht j)
        rw [hprod]
        exact hG.trans_le hinc
      have hpos : (s.filter fun i => 0 < x i).Nonempty := by
        push_neg at hz
        obtain ⟨i, hi, hxi⟩ := hz
        exact ⟨i, mem_filter.mpr ⟨hi, lt_of_le_of_ne (hx i hi) (Ne.symm hxi)⟩⟩
      let P := s.filter fun i => 0 < x i
      let i := P.min' hpos
      have hi : i ∈ s ∧ 0 < x i := mem_filter.mp (min'_mem P hpos)
      have hprefix : ∏ j ∈ s.filter (· < i), (1 + x j) = 1 := by
        apply prod_eq_one
        intro j hj
        obtain ⟨hjs, hji⟩ := mem_filter.mp hj
        have hj0 : x j = 0 := by
          by_contra hne
          have hjpos : 0 < x j := lt_of_le_of_ne (hx j hjs) (Ne.symm hne)
          have hle := min'_le P j (mem_filter.mpr ⟨hjs, hjpos⟩)
          change i ≤ j at hle
          omega
        simp [hj0]
      have hp (j : ℕ) (hj : j ∈ s) :
          ∏ k ∈ s.filter (· < j), (1 + x k) ≤ ∑ k ∈ range s.card, t ^ k := by
        have hsub : s.filter (· < j) ⊂ s := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _, ?_⟩
          intro h
          have : j ∈ s.filter (· < j) := h.symm ▸ hj
          simpa using this
        have hsum : ∑ k ∈ s.filter (· < j), x k ≤ t :=
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (by intro k hk _; exact hx k hk)).trans hs
        have hh := prod_one_add_le_geom_bound _ x t
          (fun k hk => hx k (mem_filter.mp hk).1) hsum
        exact hh.trans (sum_le_sum_of_subset_of_nonneg
          (range_mono (by have := card_lt_card hsub; omega))
          (by intro k _ _; exact pow_nonneg ht k))
      have hsumlt :
          (∑ j ∈ s, x j * ∏ k ∈ s.filter (· < j), (1 + x k)) <
            ∑ j ∈ s, x j * ∑ k ∈ range s.card, t ^ k := by
        apply sum_lt_sum
        · intro j hj
          exact mul_le_mul_of_nonneg_left (hp j hj) (hx j hj)
        · refine ⟨i, hi.1, ?_⟩
          simpa only [hprefix, mul_one] using mul_lt_mul_of_pos_left hG hi.2
      rw [prod_one_add_ordered]
      calc
        _ < 1 + ∑ j ∈ s, x j * ∑ k ∈ range s.card, t ^ k := by
          linarith only [hsumlt]
        _ = 1 + (∑ j ∈ s, x j) * ∑ k ∈ range s.card, t ^ k := by rw [sum_mul]
        _ ≤ 1 + t * ∑ k ∈ range s.card, t ^ k := by
          have hh : (∑ j ∈ s, x j) * (∑ k ∈ range s.card, t ^ k) ≤
              t * ∑ k ∈ range s.card, t ^ k :=
            mul_le_mul_of_nonneg_right hs (sum_nonneg fun k _ => pow_nonneg ht k)
          linarith only [hh]
        _ = ∑ k ∈ range (s.card + 1), t ^ k := by
          rw [sum_range_succ']
          simp_rw [pow_succ', ← mul_sum]
          ring
    exact False.elim (hstrict.ne heq)
  · rintro (hc0 | ht0 | ⟨hc1, hsum⟩)
    · have he : s = ∅ := card_eq_zero.mp hc0
      simp [he]
    · have hx0 : ∀ i ∈ s, x i = 0 := by
        have hsum0 : ∑ i ∈ s, x i = 0 := by rw [ht0] at hs; linarith [sum_nonneg hx]
        exact (sum_eq_zero_iff_of_nonneg hx).mp hsum0
      have hprod : ∏ i ∈ s, (1 + x i) = 1 :=
        prod_eq_one (by intro i hi; simp [hx0 i hi])
      rw [hprod, ht0, sum_range_succ']
      simp
    · obtain ⟨a, ha⟩ := card_eq_one.mp hc1
      rw [ha] at hsum ⊢
      simpa [sum_range_succ] using congrArg (fun z : ℚ => 1 + z) hsum

/-- A deletion product that beats its geometric factor must have mass greater than one. -/
theorem necessary_mass {r : ℕ} (hr : 0 < r) (Q : Finset ℕ)
    (hdel : geom r Q.card < ∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ)) :
    1 < ∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) := by
  have hq : ∀ q ∈ Q, 1 < q := by
    intro q hq
    by_contra h
    have hsmall : q ≤ 1 := by omega
    have hz : (q : ℚ) / (q - 1 : ℕ) = 0 := by interval_cases q <;> norm_num
    have hp : (∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ)) = 0 := prod_eq_zero hq hz
    have hg : 0 ≤ geom r Q.card := by
      unfold geom
      exact sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg r)) i
    rw [hp] at hdel
    linarith
  by_contra h
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have hsum : ∑ q ∈ Q, (1 : ℚ) / (q - 1 : ℕ) ≤ 1 / (r : ℚ) := by
    apply (le_div_iff₀ hrq).mpr
    have hh := le_of_not_gt h
    simpa only [div_eq_mul_inv, one_mul, sum_mul, mul_sum, mul_comm, mul_one] using hh
  have hprod := (prod_one_add_le_geom Q (fun q => 1 / (q - 1 : ℕ))
    (1 / (r : ℚ)) (by intro q _; positivity) hsum).1
  have heq : (∏ q ∈ Q, (1 + (1 : ℚ) / (q - 1 : ℕ))) =
      ∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ) := by
    apply prod_congr rfl
    intro q hmem
    have hq1 := hq q hmem
    have hqn : (q - 1 : ℕ) ≠ 0 := by omega
    have hqc : ((q - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hqn
    apply (eq_div_iff hqc).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hqc]
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ q))
  rw [heq] at hprod
  exact (not_lt_of_ge hprod) (by simpa only [geom, one_div] using hdel)

#print axioms prod_one_add_le_geom
#print axioms necessary_mass

end D5.S3.Arith.MakowskiSchinzel
