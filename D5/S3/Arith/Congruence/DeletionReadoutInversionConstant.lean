/- GID: D5/S3/Arith/Congruence/DeletionReadoutInversionConstant
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/DeletionReadoutInversionConstant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full deletion readouts invert with a sharp product stability constant. -/

import D5.S3.PrimeGaps.SieveCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.Congruence.DeletionReadoutInversionConstant

/-- The reading that deletes the coordinate value `a i` at every index in `T`. -/
noncomputable def R {r : ℕ} {m : Fin r → ℕ} (T : Finset (Fin r))
    (a : ∀ i, Fin (m i)) (z : (∀ i, Fin (m i)) → ℝ) : ℝ :=
  ∑ c, z c * ∏ i ∈ T, if c i = a i then 0 else 1

/-- The maximum absolute deletion reading over all coordinate sets and deleted values. -/
noncomputable def obsNorm {r : ℕ} (m : Fin r → ℕ) (hm : ∀ i, 2 ≤ m i)
    (z : (∀ i, Fin (m i)) → ℝ) : ℝ := by
  classical
  letI : ∀ i, Nonempty (Fin (m i)) := fun i ↦
    ⟨⟨0, lt_of_lt_of_le (by norm_num) (hm i)⟩⟩
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun p : Finset (Fin r) × (∀ i, Fin (m i)) ↦ |R p.1 p.2 z|)

/-- The absolute row sum of the tensor inverse of the full-deletion reading. -/
noncomputable def kappa {r : ℕ} (m : Fin r → ℕ) : ℝ :=
  ∏ i, (2 - 1 / ((m i : ℝ) - 1))

/-- Full deletion readings reconstruct every coordinate with constant `kappa`; the constant is
attained by the tensor vector with distinguished entries `2 * m i - 3` and all other entries
equal to `-1`. -/
theorem deletion_readout_inversion_constant (r : ℕ) (m : Fin r → ℕ)
    (hm : ∀ i, 2 ≤ m i) (z : (∀ i, Fin (m i)) → ℝ) :
    (∀ c, |z c| ≤ kappa m * obsNorm m hm z) ∧
      ∀ cstar : ∀ i, Fin (m i),
        let w : (∀ i, Fin (m i)) → ℝ := fun c ↦
          ∏ i, if c i = cstar i then 2 * (m i : ℝ) - 3 else -1
        obsNorm m hm w = ∏ i, ((m i : ℝ) - 1) ∧
          |w cstar| = kappa m * obsNorm m hm w := by
  classical
  letI : ∀ i, Nonempty (Fin (m i)) := fun i ↦
    ⟨⟨0, lt_of_lt_of_le (by norm_num) (hm i)⟩⟩
  let B : ∀ i, Fin (m i) → Fin (m i) → ℝ := fun i c a ↦
    1 / ((m i : ℝ) - 1) - if c = a then 1 else 0
  have hden_pos : ∀ i, 0 < (m i : ℝ) - 1 := by
    intro i
    apply sub_pos.mpr
    exact_mod_cast lt_of_lt_of_le (by omega : 1 < 2) (hm i)
  have hrecip_nonneg : ∀ i, 0 ≤ 1 / ((m i : ℝ) - 1) := by
    intro i
    exact one_div_nonneg.mpr (hden_pos i).le
  have hrecip_le_one : ∀ i, 1 / ((m i : ℝ) - 1) ≤ 1 := by
    intro i
    apply (div_le_iff₀ (hden_pos i)).2
    have hmi : (2 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm i
    linarith
  have hlocal_inverse : ∀ i (c x : Fin (m i)),
      (∑ a : Fin (m i), B i c a * (if x = a then 0 else 1)) =
        if c = x then 1 else 0 := by
    intro i c x
    have hfirst :
        (∑ a : Fin (m i),
          (1 / ((m i : ℝ) - 1)) * (if x = a then 0 else 1)) = 1 := by
      calc
        _ = 0 + ((m i : ℝ) - 1) * (1 / ((m i : ℝ) - 1)) := by
          simpa [eq_comm] using
            (LongGapsBetweenPrimes.sum_one_exception x 0
              (1 / ((m i : ℝ) - 1)))
        _ = 1 := by
          rw [zero_add, mul_one_div_cancel (ne_of_gt (hden_pos i))]
    have hsecond :
        (∑ a : Fin (m i),
          (if c = a then (1 : ℝ) else 0) * (if x = a then 0 else 1)) =
          if c = x then 0 else 1 := by
      by_cases hcx : c = x
      · subst x
        rw [if_pos rfl]
        apply Finset.sum_eq_zero
        intro a _
        by_cases hca : c = a <;> simp [hca]
      · rw [if_neg hcx]
        calc
          _ = ∑ a : Fin (m i), if c = a then (1 : ℝ) else 0 := by
            apply Fintype.sum_congr
            intro a
            by_cases hca : c = a
            · subst a
              simp [Ne.symm hcx]
            · simp [hca]
          _ = 1 := by simp
    calc
      (∑ a : Fin (m i), B i c a * (if x = a then 0 else 1)) =
          (∑ a : Fin (m i),
            (1 / ((m i : ℝ) - 1)) * (if x = a then 0 else 1)) -
            ∑ a : Fin (m i),
              (if c = a then (1 : ℝ) else 0) * (if x = a then 0 else 1) := by
        simp only [B, sub_mul, Finset.sum_sub_distrib]
      _ = if c = x then 1 else 0 := by
        rw [hfirst, hsecond]
        split <;> simp_all
  have hlocal_row : ∀ i (c : Fin (m i)),
      (∑ a : Fin (m i), |B i c a|) = 2 - 1 / ((m i : ℝ) - 1) := by
    intro i c
    calc
      (∑ a : Fin (m i), |B i c a|) =
          ∑ a : Fin (m i),
            if a = c then |1 / ((m i : ℝ) - 1) - 1|
            else |1 / ((m i : ℝ) - 1)| := by
        apply Fintype.sum_congr
        intro a
        by_cases hac : a = c
        · subst a
          simp [B]
        · have hca : c ≠ a := Ne.symm hac
          simp [B, hac, hca]
      _ = |1 / ((m i : ℝ) - 1) - 1| +
          ((m i : ℝ) - 1) * |1 / ((m i : ℝ) - 1)| := by
        exact LongGapsBetweenPrimes.sum_one_exception c _ _
      _ = 2 - 1 / ((m i : ℝ) - 1) := by
        rw [abs_of_nonneg (hrecip_nonneg i),
          abs_of_nonpos (sub_nonpos.mpr (hrecip_le_one i))]
        field_simp [ne_of_gt (hden_pos i)]
        ring
  have hinverse : ∀ c : (∀ i, Fin (m i)),
      z c = ∑ a : (∀ i, Fin (m i)),
        (∏ i, B i (c i) (a i)) * R Finset.univ a z := by
    intro c
    symm
    calc
      (∑ a : (∀ i, Fin (m i)),
          (∏ i, B i (c i) (a i)) * R Finset.univ a z) =
          ∑ a : (∀ i, Fin (m i)), ∑ x : (∀ i, Fin (m i)),
            (∏ i, B i (c i) (a i)) *
              (z x * ∏ i, if x i = a i then 0 else 1) := by
        simp only [R, Finset.mul_sum]
      _ = ∑ x : (∀ i, Fin (m i)), ∑ a : (∀ i, Fin (m i)),
            (∏ i, B i (c i) (a i)) *
              (z x * ∏ i, if x i = a i then 0 else 1) := by
        rw [Finset.sum_comm]
      _ = ∑ x : (∀ i, Fin (m i)), z x * ∑ a : (∀ i, Fin (m i)),
            ∏ i, B i (c i) (a i) * (if x i = a i then 0 else 1) := by
        apply Fintype.sum_congr
        intro x
        rw [Finset.mul_sum]
        apply Fintype.sum_congr
        intro a
        calc
          _ = z x * ((∏ i, B i (c i) (a i)) *
              ∏ i, if x i = a i then 0 else 1) := by ring
          _ = _ := by rw [← Finset.prod_mul_distrib]
      _ = ∑ x : (∀ i, Fin (m i)), z x * ∏ i,
            ∑ a : Fin (m i), B i (c i) a * (if x i = a then 0 else 1) := by
        apply Fintype.sum_congr
        intro x
        rw [Fintype.prod_sum (fun i (a : Fin (m i)) ↦
          B i (c i) a * (if x i = a then 0 else 1))]
      _ = ∑ x : (∀ i, Fin (m i)),
          z x * ∏ i, if c i = x i then 1 else 0 := by
        simp_rw [hlocal_inverse]
      _ = ∑ x : (∀ i, Fin (m i)), z x * (if c = x then 1 else 0) := by
        apply Fintype.sum_congr
        intro x
        congr 1
        by_cases hcx : c = x
        · subst x
          simp
        · have hpoint : ∃ i, c i ≠ x i := Function.ne_iff.mp hcx
          obtain ⟨i, hi⟩ := hpoint
          rw [if_neg hcx]
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      _ = z c := by simp
  have hreadout_le : ∀ T a, |R T a z| ≤ obsNorm m hm z := by
    intro T a
    change |R T a z| ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun p : Finset (Fin r) × (∀ i, Fin (m i)) ↦ |R p.1 p.2 z|)
    exact Finset.le_sup'
      (fun p : Finset (Fin r) × (∀ i, Fin (m i)) ↦ |R p.1 p.2 z|)
      (Finset.mem_univ (T, a))
  have hrow_sum : ∀ c : (∀ i, Fin (m i)),
      (∑ a : (∀ i, Fin (m i)), |∏ i, B i (c i) (a i)|) = kappa m := by
    intro c
    simp only [Finset.abs_prod]
    rw [← Fintype.prod_sum (fun i (a : Fin (m i)) ↦ |B i (c i) a|)]
    simp_rw [hlocal_row]
    rfl
  constructor
  · intro c
    calc
      |z c| = |∑ a : (∀ i, Fin (m i)),
          (∏ i, B i (c i) (a i)) * R Finset.univ a z| := by
        rw [hinverse]
      _ ≤ ∑ a : (∀ i, Fin (m i)),
          |(∏ i, B i (c i) (a i)) * R Finset.univ a z| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a : (∀ i, Fin (m i)),
          |∏ i, B i (c i) (a i)| * |R Finset.univ a z| := by
        simp only [abs_mul]
      _ ≤ ∑ a : (∀ i, Fin (m i)),
          |∏ i, B i (c i) (a i)| * obsNorm m hm z := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (hreadout_le Finset.univ a) (abs_nonneg _)
      _ = (∑ a : (∀ i, Fin (m i)), |∏ i, B i (c i) (a i)|) *
          obsNorm m hm z := by
        rw [Finset.sum_mul]
      _ = kappa m * obsNorm m hm z := by rw [hrow_sum]
  · intro cstar
    let w : (∀ i, Fin (m i)) → ℝ := fun c ↦
      ∏ i, if c i = cstar i then 2 * (m i : ℝ) - 3 else -1
    change obsNorm m hm w = ∏ i, ((m i : ℝ) - 1) ∧
      |w cstar| = kappa m * obsNorm m hm w
    have hw_total : ∀ i,
        (∑ x : Fin (m i),
          if x = cstar i then 2 * (m i : ℝ) - 3 else -1) =
          (m i : ℝ) - 2 := by
      intro i
      calc
        _ = (2 * (m i : ℝ) - 3) + ((m i : ℝ) - 1) * (-1) := by
          simpa using LongGapsBetweenPrimes.sum_one_exception (cstar i)
            (2 * (m i : ℝ) - 3) (-1)
        _ = (m i : ℝ) - 2 := by ring
    have hw_delete : ∀ i (a : Fin (m i)),
        (∑ x : Fin (m i),
          (if x = cstar i then 2 * (m i : ℝ) - 3 else -1) *
            (if x = a then 0 else 1)) =
          if a = cstar i then -((m i : ℝ) - 1) else (m i : ℝ) - 1 := by
      intro i a
      calc
        _ = ∑ x : Fin (m i),
              ((if x = cstar i then 2 * (m i : ℝ) - 3 else -1) -
                if x = a then
                  (if x = cstar i then 2 * (m i : ℝ) - 3 else -1)
                else 0) := by
          apply Fintype.sum_congr
          intro x
          by_cases hxa : x = a <;> simp [hxa]
        _ = (∑ x : Fin (m i),
              if x = cstar i then 2 * (m i : ℝ) - 3 else -1) -
              ∑ x : Fin (m i), if x = a then
                (if x = cstar i then 2 * (m i : ℝ) - 3 else -1) else 0 := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ x : Fin (m i),
              if x = cstar i then 2 * (m i : ℝ) - 3 else -1) -
              (if a = cstar i then 2 * (m i : ℝ) - 3 else -1) := by
          simp
        _ = if a = cstar i then -((m i : ℝ) - 1) else (m i : ℝ) - 1 := by
          rw [hw_total]
          split <;> ring
    have hreading : ∀ (T : Finset (Fin r)) (a : ∀ i, Fin (m i)),
        |R T a w| =
          ∏ i, if i ∈ T then (m i : ℝ) - 1 else (m i : ℝ) - 2 := by
      intro T a
      have hfactor : R T a w =
          ∏ i, ∑ x : Fin (m i),
            (if x = cstar i then 2 * (m i : ℝ) - 3 else -1) *
              (if i ∈ T then (if x = a i then 0 else 1) else 1) := by
        calc
          R T a w = ∑ c : (∀ i, Fin (m i)), ∏ i,
              (if c i = cstar i then 2 * (m i : ℝ) - 3 else -1) *
                (if i ∈ T then (if c i = a i then 0 else 1) else 1) := by
            unfold R w
            apply Fintype.sum_congr
            intro c
            calc
              _ = (∏ i, if c i = cstar i then 2 * (m i : ℝ) - 3 else -1) *
                  ∏ i, if i ∈ T then (if c i = a i then 0 else 1) else 1 := by
                rw [Fintype.prod_ite_mem]
              _ = _ := by rw [← Finset.prod_mul_distrib]
          _ = _ := (Fintype.prod_sum (fun i (x : Fin (m i)) ↦
            (if x = cstar i then 2 * (m i : ℝ) - 3 else -1) *
              (if i ∈ T then (if x = a i then 0 else 1) else 1))).symm
      rw [hfactor, Finset.abs_prod]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ T
      · rw [if_pos hi]
        simp only [hi, if_true, hw_delete]
        by_cases ha : a i = cstar i
        · rw [if_pos ha, abs_neg, abs_of_nonneg]
          have hmi : (2 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm i
          linarith
        · rw [if_neg ha, abs_of_nonneg]
          have hmi : (2 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm i
          linarith
      · rw [if_neg hi]
        simp only [hi, if_false, mul_one, hw_total]
        rw [abs_of_nonneg]
        have hmi : (2 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm i
        linarith
    have hreading_upper : ∀ (T : Finset (Fin r)) (a : ∀ i, Fin (m i)),
        |R T a w| ≤ ∏ i, ((m i : ℝ) - 1) := by
      intro T a
      rw [hreading]
      apply Finset.prod_le_prod
      · intro i _
        have hmi : (2 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm i
        split
        · linarith
        · linarith
      · intro i _
        split <;> linarith
    have hnorm : obsNorm m hm w = ∏ i, ((m i : ℝ) - 1) := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro p _
        exact hreading_upper p.1 p.2
      · have hfull : |R Finset.univ cstar w| ≤ obsNorm m hm w := by
          change |R Finset.univ cstar w| ≤
            Finset.univ.sup' Finset.univ_nonempty
              (fun p : Finset (Fin r) × (∀ i, Fin (m i)) ↦ |R p.1 p.2 w|)
          exact Finset.le_sup'
            (fun p : Finset (Fin r) × (∀ i, Fin (m i)) ↦ |R p.1 p.2 w|)
            (Finset.mem_univ (Finset.univ, cstar))
        change (∏ i, ((m i : ℝ) - 1)) ≤ obsNorm m hm w
        rw [hreading Finset.univ cstar] at hfull
        simpa only [Finset.mem_univ, if_true] using hfull
    refine ⟨hnorm, ?_⟩
    have hw_at : |w cstar| = ∏ i, (2 * (m i : ℝ) - 3) := by
      simp only [w, ↓reduceIte, Finset.abs_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [abs_of_nonneg]
      have hmi : (2 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm i
      linarith
    rw [hw_at, hnorm]
    unfold kappa
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    field_simp [ne_of_gt (hden_pos i)]; ring

#print axioms deletion_readout_inversion_constant

end D5.S3.Arith.Congruence.DeletionReadoutInversionConstant
