/- GID: D5/S3/TotalVariation/PositiveParitySpectrum
   generality: G
   mirror-B: D5/B/S3/TotalVariation/PositiveParitySpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive parity spectra are realizable exactly when their half-space moment products are ordered. -/

import D5.S3.TotalVariation.GroupedParityBias
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open D5.S3.TotalVariation.GroupedParityBias

namespace D5.S3.TotalVariation.PositiveParitySpectrum

variable {A : Type*} [AddCommGroup A] [Fintype A]

private theorem character_sum (ψ : AddChar A ℂ) :
    (∑ a, sign ψ a) = if ψ = 0 then (Fintype.card A : ℝ) else 0 := by
  classical
  have h := congrArg Complex.re (AddChar.sum_eq_ite ψ)
  by_cases heq : ψ = 0
  · simp [sign, heq] at h ⊢
  · simpa [sign, Complex.re_sum, heq] using h

private theorem char_orthog (two : ∀ x : A, x + x = 0) (ψ φ : AddChar A ℂ) :
    (∑ a, sign ψ a * sign φ a) =
      if ψ = φ then (Fintype.card A : ℝ) else 0 := by
  classical
  have hadd (a : A) : sign (ψ + φ) a = sign ψ a * sign φ a := by
    rcases value_cases two ψ a with h | h <;> simp [sign, h]
  have hself : φ + φ = 0 := by
    ext a
    rw [AddChar.add_apply, ← AddChar.map_add_eq_mul, two, AddChar.map_zero_eq_one]
    rfl
  have hneg : -φ = φ := (eq_neg_iff_add_eq_zero.mpr hself).symm
  simp_rw [← hadd, character_sum, ← eq_neg_iff_add_eq_zero, hneg]

private theorem weighted_orthog (two : ∀ x : A, x + x = 0) (ψ φ : AddChar A ℂ) :
    (∑ a, ((1 - sign ψ a) / 2) * sign φ a) =
      ((if φ = 0 then (Fintype.card A : ℝ) else 0) -
        (if ψ = φ then (Fintype.card A : ℝ) else 0)) / 2 := by
  classical
  calc
    _ = (∑ a, (sign φ a - sign ψ a * sign φ a)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, character_sum, char_orthog two]

private noncomputable def columnLog (m : AddChar A ℂ → ℝ) (a : A) : ℝ :=
  (-2 / (Fintype.card A : ℝ)) * ∑ φ, sign φ a * Real.log (m φ)

private theorem columnLog_invert (two : ∀ x : A, x + x = 0)
    (m : AddChar A ℂ → ℝ) (hzero : m 0 = 1) (ψ : AddChar A ℂ) :
    (∑ a, ((1 - sign ψ a) / 2) * columnLog m a) = Real.log (m ψ) := by
  classical
  let N : ℝ := Fintype.card A
  have hN : N ≠ 0 := by positivity
  calc
    _ = (-2 / N) * ∑ φ, Real.log (m φ) * ∑ a, ((1 - sign ψ a) / 2) * sign φ a := by
      unfold columnLog
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro φ _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (-2 / N) * ∑ φ, (-(if ψ = φ then N else 0) * Real.log (m φ) / 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro φ _
      rw [weighted_orthog two]
      by_cases h : φ = 0
      · subst φ
        simp [hzero]
      · by_cases hh : ψ = φ
        · simp [h, hh, N]
          ring
        · simp [h, hh, N]
    _ = (-2 / N) * (-N * Real.log (m ψ) / 2) := by
      rw [Finset.sum_eq_single ψ]
      · simp
      · intro φ _ h
        simp [Ne.symm h]
      · simp
    _ = _ := by field_simp

private theorem affine_law_of_positive_moments (two : ∀ x : A, x + x = 0)
    (m : AddChar A ℂ → ℝ) (hzero : m 0 = 1) (hm : ∀ ψ, 0 < m ψ)
    (hcone : ∀ a : A, a ≠ 0 → 0 ≤ ∑ φ, sign φ a * Real.log (m φ)) :
    ∃ q : A → ℝ, (∀ a, q a ∈ Set.Ioc (0 : ℝ) 1) ∧
      ∀ ψ, moment (law id 0 q) ψ = m ψ := by
  classical
  let q (a : A) : ℝ := if a = 0 then 1 else Real.exp (columnLog m a)
  have hq (a : A) : q a ∈ Set.Ioc (0 : ℝ) 1 := by
    by_cases h : a = 0
    · simp [q, h]
    have hc : columnLog m a ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)) (hcone a h)
    refine ⟨?_, ?_⟩
    · simpa [q, h] using Real.exp_pos (columnLog m a)
    · simpa [q, h] using Real.exp_le_one_iff.mpr hc
  refine ⟨q, hq, ?_⟩
  intro ψ
  have hg (a : A) : groupBias id q a = q a := by
    unfold groupBias
    rw [Finset.prod_filter]
    rw [Finset.prod_eq_single a]
    · simp
    · intro b _ h
      simp [h]
    · simp
  have hs0 : sign ψ 0 = 1 := by simp [sign]
  rw [moment_factor two, hs0, one_mul]
  simp_rw [hg]
  have hprod : 0 < ∏ a with sign ψ a = -1, q a :=
    Finset.prod_pos fun a _ => (hq a).1
  apply Real.log_injOn_pos hprod (hm ψ)
  rw [Real.log_prod (fun a _ => (hq a).1.ne'), Finset.sum_filter]
  rw [← columnLog_invert two m hzero ψ]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a = 0
  · subst a
    norm_num [hs0]
  rcases value_cases two ψ a with h | h <;> norm_num [sign, h, q, ha]

private theorem affinity_iff_positive_cone (two : ∀ x : A, x + x = 0)
    (m : AddChar A ℂ → ℝ) (hzero : m 0 = 1) (hm : ∀ ψ, 0 < m ψ) :
    (∃ q : A → ℝ, (∀ a, q a ∈ Set.Ioc (0 : ℝ) 1) ∧
      ∀ ψ, moment (law id 0 q) ψ = m ψ) ↔
    ∀ a : A, a ≠ 0 → 0 ≤ ∑ φ, sign φ a * Real.log (m φ) := by
  classical
  refine ⟨?_, affine_law_of_positive_moments two m hzero hm⟩
  intro h a ha
  obtain ⟨q, hq, hmeans⟩ := h
  have hEq := loginvert two id 0 q (fun i => (hq i).1) a ha
  have hAbs (ψ : AddChar A ℂ) : |m ψ| = m ψ := abs_of_pos (hm ψ)
  simp_rw [hmeans, hAbs] at hEq
  have hBiasPos : 0 < groupBias id q a := Finset.prod_pos fun i _ => (hq i).1
  have hBiasLe : groupBias id q a ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (hq i).1.le) (fun i _ => (hq i).2)
  have hLogNonpos := Real.log_nonpos hBiasPos.le hBiasLe
  by_contra! hneg
  have hcoef : (-2 / (Fintype.card A : ℝ)) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) (by positivity)
  exact (not_lt_of_ge hLogNonpos) (hEq.symm ▸ mul_pos_of_neg_of_neg hcoef hneg)

private theorem producttest_iff_logtest (two : ∀ x : A, x + x = 0)
    (m : AddChar A ℂ → ℝ) (hm : ∀ ψ, 0 < m ψ) (a : A) :
    (∏ φ with sign φ a = -1, m φ) ≤ (∏ φ with sign φ a = 1, m φ) ↔
      0 ≤ ∑ φ, sign φ a * Real.log (m φ) := by
  classical
  have hprod {b : ℝ} : 0 < ∏ φ with sign φ a = b, m φ := Finset.prod_pos fun φ _ => hm φ
  rw [← Real.log_le_log_iff hprod hprod, Real.log_prod (fun φ _ => (hm φ).ne'),
    Real.log_prod (fun φ _ => (hm φ).ne'), ← sub_nonneg]
  have hdiff :
      (∑ φ with sign φ a = 1, Real.log (m φ)) -
        (∑ φ with sign φ a = -1, Real.log (m φ)) =
      ∑ φ, sign φ a * Real.log (m φ) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro φ _
    rcases value_cases two φ a with h | h <;> norm_num [sign, h]
  rw [hdiff]

private theorem affinity_iff_positive_producttest (two : ∀ x : A, x + x = 0)
    (m : AddChar A ℂ → ℝ) (hzero : m 0 = 1) (hm : ∀ ψ, 0 < m ψ) :
    (∃ q : A → ℝ, (∀ a, q a ∈ Set.Ioc (0 : ℝ) 1) ∧
      ∀ ψ, moment (law id 0 q) ψ = m ψ) ↔
    ∀ a : A, a ≠ 0 → (∏ φ with sign φ a = -1, m φ) ≤ (∏ φ with sign φ a = 1, m φ) := by
  rw [affinity_iff_positive_cone two m hzero hm]
  simp_rw [producttest_iff_logtest two m hm]

omit [AddCommGroup A] in
theorem singleton_group_bias (q : A → ℝ) (a : A) : groupBias id q a = q a := by
  classical
  unfold groupBias
  rw [Finset.prod_filter, Finset.prod_eq_single a]
  · simp
  · intro b _ h
    simp [h]
  · simp

theorem exists_negative_sign (two : ∀ x : A, x + x = 0) (a : A) (ha : a ≠ 0) :
    ∃ ψ : AddChar A ℂ, sign ψ a = -1 := by
  classical
  by_contra! hh
  have hone (ψ : AddChar A ℂ) : ψ a = 1 := by
    rcases value_cases two ψ a with h | h
    · exact h
    · exact (hh ψ (by simp [sign, h])).elim
  have h := AddChar.sum_apply_eq_ite a
  simp [hone, ha] at h

private theorem abs_moments_positive_realization {I : Type*} [Fintype I]
    (two : ∀ x : A, x + x = 0) (column : I → A) (offset : A) (q : I → ℝ)
    (hq : ∀ i, |q i| ≤ 1) (hpos : ∀ ψ, 0 < |moment (law column offset q) ψ|) :
    ∃ r : A → ℝ, (∀ a, r a ∈ Set.Ioc (0 : ℝ) 1) ∧
      ∀ ψ, moment (law id 0 r) ψ = |moment (law column offset q) ψ| := by
  classical
  let r (a : A) : ℝ := if a = 0 then 1 else |groupBias column q a|
  have absSign (ψ : AddChar A ℂ) : |sign ψ offset| = 1 := by
    rcases value_cases two ψ offset with h | h <;> simp [sign, h]
  have ordinary ψ : moment (law id 0 r) ψ = |moment (law column offset q) ψ| := by
    rw [moment_factor two, moment_factor two, abs_mul, absSign, one_mul, Finset.abs_prod]
    have hZero : sign ψ 0 = 1 := by simp [sign]
    rw [hZero, one_mul]
    apply Finset.prod_congr rfl
    intro a ha
    rw [singleton_group_bias]
    have h : a ≠ 0 := by
      intro heq
      subst a
      have hBad := (Finset.mem_filter.mp ha).2
      norm_num [hZero] at hBad
    simp [r, h]
  refine ⟨r, ?_, ordinary⟩
  intro a
  by_cases ha : a = 0
  · simp [r, ha]
  refine ⟨?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_negative_sign two a ha
    have hm := hpos ψ
    rw [← ordinary ψ, moment_factor two] at hm
    have hZero : sign ψ 0 = 1 := by simp [sign]
    rw [hZero, one_mul] at hm
    simp_rw [singleton_group_bias] at hm
    have haMem : a ∈ (Finset.univ.filter fun c => sign ψ c = -1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hψ⟩
    have hNonzero : r a ≠ 0 := by
      intro hz
      exact hm.ne' (Finset.prod_eq_zero haMem hz)
    exact lt_of_le_of_ne (by simp [r, ha]) hNonzero.symm
  · simp only [r, ite_eq_right ha]
    rw [groupBias, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => hq i


/-- For each nonzero column, the moments of the characters that read the column
have product at most the product for the characters that do not. -/
def orderedMomentProducts (p : A → ℝ) : Prop := by
  classical
  exact ∀ a : A, a ≠ 0 →
    (∏ ψ with sign ψ a = -1, moment p ψ) ≤ (∏ ψ with sign ψ a = 1, moment p ψ)

/-- For a normalized law with strictly positive sign moments, every affine
independent-bit representation satisfies the half-space product inequalities.
Conversely, the inequalities provide a representation with one bit per
nonzero column. In the construction the coordinate at zero is inert. -/
theorem positive_moment_realizability
    (two : ∀ x : A, x + x = 0) (p : A → ℝ) (hnorm : ∑ x, p x = 1)
    (hpos : ∀ ψ, 0 < moment p ψ) :
    (∀ {I : Type*} [Fintype I] (c : I → A) (s : A) (q : I → ℝ),
      (∀ i, |q i| ≤ 1) → law c s q = p → orderedMomentProducts p) ∧
    (orderedMomentProducts p → ∃ q : A → ℝ,
      (∀ a, q a ∈ Set.Ioc (0 : ℝ) 1) ∧ law id 0 q = p) := by
  classical
  have hzero : moment p 0 = 1 := by simpa [moment, sign] using hnorm
  have criterion := affinity_iff_positive_producttest two (moment p) hzero hpos
  constructor
  · intro I _ c s q hq hlaw
    have habs (ψ : AddChar A ℂ) : 0 < |moment (law c s q) ψ| := by
      rw [hlaw, abs_of_pos (hpos ψ)]
      exact hpos ψ
    obtain ⟨r, hr, hrealize⟩ := abs_moments_positive_realization two c s q hq habs
    apply criterion.mp
    refine ⟨r, hr, ?_⟩
    intro ψ
    rw [hrealize, hlaw, abs_of_pos (hpos ψ)]
  · intro h
    obtain ⟨r, hr, hrealize⟩ := criterion.mpr h
    exact ⟨r, hr, law_from_moments two _ _ hrealize⟩

end D5.S3.TotalVariation.PositiveParitySpectrum
