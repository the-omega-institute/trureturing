/- GID: D5/S3/TotalVariation/ParryResetEstimates
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParryResetEstimates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform three-step minorization and golden suffix tail for the actual Parry law. -/

import D5.S3.TotalVariation.ParryResetLaw

open scoped BigOperators
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.ParryResetLaw
namespace D5.S3.TotalVariation.ParryResetEstimates

/-- Both signed zero-suffix states receive at least one eighth of every three-step row.
The two concrete paths are three resets and reset-increment-reset. -/
theorem parry_three_step_minorization (k : ℕ) (hk : 2 ≤ k)
    (s : State k) (a : Bool) :
    1 / 8 ≤ (kernel k (parryParameter k) ^ 3) s (a, ⟨0, by omega⟩) := by
  classical
  let p := parryParameter k
  let z : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, by omega⟩
  obtain ⟨hr, hb, hS, hQ, hrow, hπ, hπsum, hstat, hflip⟩ := parry_stationary_law k hk
  have hp : 0 < p := by dsimp [p]; linarith [hr.1]
  have hh (j : Fin k) : 0 < suffixWeight k p j := lt_of_lt_of_le hp (hb j).1
  have hz : suffixWeight k p z = 1 := by
    simpa [suffixWeight, rootSum, z] using hr.2.2
  have hstep (x : State k) : kernel k p x (!x.1,z) = p / suffixWeight k p x.2 := by
    simp [kernel, z]
  have h3 (x u v y : State k) :
      kernel k p x u * kernel k p u v * kernel k p v y ≤ (kernel k p ^ 3) x y := by
    have h2 : kernel k p x u * kernel k p u v ≤ (kernel k p ^ 2) x v := by
      rw [pow_two, Matrix.mul_apply]
      exact Finset.single_le_sum (fun j _ => mul_nonneg (hQ x j) (hQ j v))
        (Finset.mem_univ u)
    calc
      _ ≤ (kernel k p ^ 2) x v * kernel k p v y :=
        mul_le_mul_of_nonneg_right h2 (hQ v y)
      _ ≤ (kernel k p ^ 3) x y := by
        rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, Matrix.mul_apply]
        exact Finset.single_le_sum
          (fun j _ => mul_nonneg (Matrix.pow_apply_nonneg hQ 2 x j) (hQ j y))
          (Finset.mem_univ v)
  have hbound : (1 / 8 : ℝ) ≤ p ^ 3 / suffixWeight k p s.2 := by
    have hcube : (1 / 8 : ℝ) ≤ p^3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hr.1.le 3
      norm_num at h
      exact h
    apply (le_div_iff₀ (hh s.2)).mpr
    nlinarith [(hb s.2).2]
  by_cases ha : a = !s.1
  · subst a
    calc
      _ ≤ p ^ 3 / suffixWeight k p s.2 := hbound
      _ = kernel k p s (!s.1,z) * kernel k p (!s.1,z) (s.1,z) *
          kernel k p (s.1,z) (!s.1,z) := by
        rw [hstep, show kernel k p (!s.1,z) (s.1,z) = p by
          simpa [hz] using hstep (!s.1,z), hstep, hz]
        ring
      _ ≤ _ := h3 s (!s.1,z) (s.1,z) (!s.1,z)
  · have ha' : a = s.1 := by
      cases hs : s.1 <;> cases a <;> simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false, not_false_eq_true]
    subst a
    have hinc : kernel k p (!s.1,z) (!s.1,o) = p * suffixWeight k p o := by
      simp [kernel, z, o, hz]
    have hreset : kernel k p (!s.1,o) (s.1,z) = p / suffixWeight k p o := by
      simpa using hstep (!s.1,o)
    calc
      _ ≤ p ^ 3 / suffixWeight k p s.2 := hbound
      _ = kernel k p s (!s.1,z) * kernel k p (!s.1,z) (!s.1,o) *
          kernel k p (!s.1,o) (s.1,z) := by
        rw [hstep, hinc, hreset]
        field_simp [(hh o).ne']
        <;> ring
      _ ≤ _ := h3 s (!s.1,z) (!s.1,o) (s.1,z)

/-- The actual stationary suffix tail is bounded independently of the forbidden-run length,
including when the tail is empty. The exponent is an integer, so no truncation occurs. -/
theorem parry_suffix_tail (k : ℕ) (hk : 2 ≤ k) (L : ℕ) :
    (∑ s : State k with L ≤ s.2.val, parryLaw k s) ≤
      Real.goldenRatio ^ (2 - (L : ℤ)) := by
  classical
  let p := parryParameter k
  let g := Real.goldenRatio⁻¹
  obtain ⟨hr, hb, hS, hQ, hrow, hπ, hπsum, hstat, hflip⟩ := parry_stationary_law k hk
  have hp : 0 ≤ p := by dsimp [p]; linarith [hr.1]
  have hg : 0 ≤ g := inv_nonneg.mpr Real.goldenRatio_pos.le
  have hg1 : g < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hSpos : 0 < normalizer k := by linarith
  have hbnd (s : State k) : parryLaw k s ≤ g^s.2.val / 2 := by
    unfold parryLaw
    change p^s.2.val * suffixWeight k p s.2 / (2 * normalizer k) ≤ _
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*normalizer k)).mpr
    have hpow : p^s.2.val ≤ g^s.2.val := pow_le_pow_left₀ hp hr.2.1 _
    have h0 : 0 ≤ p^s.2.val := pow_nonneg hp _
    have hg0 : 0 ≤ g^s.2.val := pow_nonneg hg _
    nlinarith [(hb s.2).2, mul_le_mul_of_nonneg_left hS hg0,
      mul_le_mul_of_nonneg_left (hb s.2).2 h0]
  have hsum : (∑ j : Fin k with L ≤ j.val, g^j.val) =
      ∑ j ∈ Finset.Ico L k, g^j := by
    apply Finset.sum_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hj).2,j.isLt⟩
    · intro a _ b _ he
      exact Fin.ext he
    · intro j hj
      refine ⟨⟨j,(Finset.mem_Ico.mp hj).2⟩, ?_, rfl⟩
      simp [(Finset.mem_Ico.mp hj).1]
    · intro j _
      rfl
  calc
    _ ≤ ∑ s : State k with L ≤ s.2.val, g^s.2.val/2 :=
      Finset.sum_le_sum fun s _ => hbnd s
    _ = ∑ j ∈ Finset.Ico L k, g^j := by
      rw [← hsum]
      simp only [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    _ ≤ g^L / (1-g) := geom_sum_Ico_le_of_lt_one hg hg1
    _ = Real.goldenRatio ^ (2-(L:ℤ)) := by
      have hφ := Real.goldenRatio_sq
      have hφ0 := Real.goldenRatio_ne_zero
      rw [zpow_sub₀ hφ0, zpow_ofNat, zpow_natCast]
      change (Real.goldenRatio⁻¹)^L / (1-Real.goldenRatio⁻¹) = _
      rw [inv_pow]
      generalize hv : Real.goldenRatio = φ at *
      have hφ1 : φ - 1 ≠ 0 := by
        have hlt : 1 < φ := by rw [← hv]; exact Real.one_lt_goldenRatio
        linarith
      field_simp [hφ1]
      nlinarith

#print axioms parry_three_step_minorization
#print axioms parry_suffix_tail
end D5.S3.TotalVariation.ParryResetEstimates
