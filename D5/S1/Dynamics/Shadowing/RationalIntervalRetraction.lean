/- GID: D5/S1/Dynamics/Shadowing/RationalIntervalRetraction
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/RationalIntervalRetraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite weighted orbit retraction on the entire closed rational pseudo-orbit domain. -/

import D5.S1.Dynamics.Shadowing.RationalIntervalAction
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Algebra.Order.Field

/-! The finite marker sums have no global continuity assertion at empty-marker points. -/

open Set Filter
open scoped Topology BigOperators

namespace D5.S1.Dynamics.Shadowing.RationalInterval

abbrev P := CompactSelector.Space f (1 / 256)

/-- Actual interval weight, with zero values at both band boundaries. -/
noncomputable def weight (u : I) : ℝ := max 0 (((u : ℝ) - 1 / 3) * (2 / 3 - u))

/-- A continuous extension of the weighted odds; its denominator is always at least `1/3`. -/
noncomputable def weightedOdds (u : I) : ℝ :=
  weight u * u / max (1 / 3) (1 - (u : ℝ))

private theorem weight_nonneg (u : I) : 0 ≤ weight u := le_max_left _ _

private theorem weight_pos_iff (u : I) :
    0 < weight u ↔ (1 / 3 : ℝ) < u ∧ (u : ℝ) < 2 / 3 := by
  simp only [weight, lt_max_iff, lt_self_iff_false, false_or]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with h | h
    · constructor <;> linarith [h.1, h.2]
    · exfalso
      linarith [h.1, h.2]
  · rintro ⟨h₁, h₂⟩
    exact mul_pos (by linarith) (by linarith)

private theorem weight_eq_zero_iff (u : I) :
    weight u = 0 ↔ ¬ ((1 / 3 : ℝ) < u ∧ (u : ℝ) < 2 / 3) := by
  rw [← weight_pos_iff, not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h (weight_nonneg u)⟩

private theorem weightedOdds_nonneg (u : I) : 0 ≤ weightedOdds u :=
  div_nonneg (mul_nonneg (weight_nonneg u) u.property.1)
    (le_trans (by norm_num) (le_max_left _ _))

private theorem weightedOdds_eq_zero (u : I) (h : weight u = 0) :
    weightedOdds u = 0 := by simp [weightedOdds, h]

private theorem weightedOdds_bounds (u : I) :
    weight u / 2 ≤ weightedOdds u ∧ weightedOdds u ≤ 2 * weight u := by
  by_cases h : weight u = 0
  · simp [h, weightedOdds_eq_zero u h]
  · obtain ⟨hl, hu⟩ := (weight_pos_iff u).mp
      (lt_of_le_of_ne (weight_nonneg u) (Ne.symm h))
    have hd : 0 < 1 - (u : ℝ) := by linarith
    have hm : max (1 / 3 : ℝ) (1 - u) = 1 - u := max_eq_right (by linarith)
    rw [weightedOdds, hm]
    constructor
    · apply (le_div_iff₀ hd).mpr
      nlinarith [weight_nonneg u]
    · apply (div_le_iff₀ hd).mpr
      nlinarith [weight_nonneg u]

private theorem continuous_weight : Continuous weight := by
  unfold weight
  fun_prop

private theorem continuous_weightedOdds : Continuous weightedOdds := by
  unfold weightedOdds
  exact (continuous_weight.mul continuous_subtype_val).div
    (continuous_const.max (continuous_const.sub continuous_subtype_val))
    (fun u => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3)
      (le_max_left _ _)))

private def markers (x : P) : Set ℤ :=
  bandMarkers (fun k => (x.1 k : ℝ)) (1 / 3) (2 / 3)

private theorem marker_finite (x : P) : (markers x).Finite :=
  (rational_interval_marker_classification (le_refl (1 / 256)) x.1
    ((closedPseudoOrbit_iff _ _).mp x.2)).1

private theorem marker_cases (x : P) :
    (∀ k, (x.1 k : ℝ) < 1 / 3) ∨ (∀ k, (2 / 3 : ℝ) < x.1 k) ∨
      ∃ a b : ℤ, a ≤ b ∧ b - a ≤ 2 ∧ markers x = Set.Icc a b ∧
        (∀ k, k < a → (x.1 k : ℝ) ≤ 1 / 3) ∧
        (∀ k, b < k → (2 / 3 : ℝ) ≤ x.1 k) :=
  (rational_interval_marker_classification (le_refl (1 / 256)) x.1
    ((closedPseudoOrbit_iff _ _).mp x.2)).2.2.1

private theorem marker_pair_span (x : P) {i j : ℤ}
    (hi : i ∈ markers x) (hj : j ∈ markers x) : i - j ≤ 2 ∧ j - i ≤ 2 := by
  rcases marker_cases x with hl | hu | ⟨a, b, _, hab, heq, _, _⟩
  · exact False.elim ((not_lt_of_ge (hl i).le) hi.1)
  · exact False.elim ((not_lt_of_ge (hu i).le) hi.2)
  · rw [heq] at hi hj
    rcases hi with ⟨hai, hib⟩
    rcases hj with ⟨haj, hjb⟩
    constructor <;> omega

/-- The denominator is the actual finite sum of the marker weights. -/
noncomputable def W (x : P) : ℝ := ∑ᶠ k : ℤ, weight (x.1 k)

/-- The numerator retains the original absolute integer phase factor. -/
noncomputable def A (x : P) : ℝ := ∑ᶠ k : ℤ, (2 : ℝ) ^ (-k) * weightedOdds (x.1 k)

private theorem weight_support (x : P) :
    Function.support (fun k => weight (x.1 k)) = markers x := by
  ext k
  change weight (x.1 k) ≠ 0 ↔ (1 / 3 : ℝ) < x.1 k ∧ (x.1 k : ℝ) < 2 / 3
  constructor
  · intro h
    exact (weight_pos_iff _).mp (lt_of_le_of_ne (weight_nonneg _) (Ne.symm h))
  · intro h
    exact ((weight_pos_iff _).mpr h).ne'

private theorem A_support_subset (x : P) :
    Function.support (fun k => (2 : ℝ) ^ (-k) * weightedOdds (x.1 k)) ⊆ markers x := by
  intro k hk
  by_contra hn
  have hz := (weight_eq_zero_iff (x.1 k)).mpr hn
  exact hk (by simp [weightedOdds_eq_zero _ hz])

private theorem W_finite (x : P) : (fun k => weight (x.1 k)).HasFiniteSupport := by
  rw [Function.HasFiniteSupport, weight_support]
  exact marker_finite x

private theorem A_finite (x : P) :
    (fun k => (2 : ℝ) ^ (-k) * weightedOdds (x.1 k)).HasFiniteSupport :=
  (marker_finite x).subset (A_support_subset x)

private theorem W_nonneg (x : P) : 0 ≤ W x := finsum_nonneg fun k => weight_nonneg _

private theorem A_nonneg (x : P) : 0 ≤ A x :=
  finsum_nonneg fun k => mul_nonneg (by positivity) (weightedOdds_nonneg _)

private theorem W_pos_iff (x : P) : 0 < W x ↔ (markers x).Nonempty := by
  constructor
  · intro h
    by_contra hn
    have he : ∀ k, weight (x.1 k) = 0 := fun k =>
      (weight_eq_zero_iff _).mpr (fun hk => hn ⟨k, hk⟩)
    have hw : W x = 0 := finsum_eq_zero_of_forall_eq_zero he
    linarith
  · rintro ⟨k, hk⟩
    exact finsum_pos (fun i => weight_nonneg _) ⟨k, (weight_pos_iff _).mpr hk⟩ (W_finite x)

/-- Odds compression, evaluated only at nonnegative quotient values. -/
noncomputable def Q (s : ℝ) : ℝ := s / (1 + s)

private theorem Q_mem {s : ℝ} (hs : 0 ≤ s) : Q s ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg hs (by linarith)
  · exact (div_le_one (by linarith : 0 < 1 + s)).mpr (by linarith)

/-- The same explicit map is defined on all closed-error sequences. Empty marker
sets use the cap containing coordinate zero; the cap classification is global. -/
noncomputable def R (x : P) : I := by
  classical
  exact if h : 0 < W x then
    ⟨Q (A x / W x), Q_mem (div_nonneg (A_nonneg x) h.le)⟩
  else if (x.1 0 : ℝ) < 1 / 2 then ⟨0, by norm_num⟩ else ⟨1, by norm_num⟩

private theorem R_marked (x : P) (h : (markers x).Nonempty) :
    (R x : ℝ) = Q (A x / W x) := by simp [R, (W_pos_iff x).mpr h]

private theorem R_lower (x : P) (h : ∀ k, (x.1 k : ℝ) < 1 / 3) :
    (R x : ℝ) = 0 := by
  have hn : ¬ (markers x).Nonempty := by
    rintro ⟨k, hk⟩
    linarith [hk.1, h k]
  have hw := mt (W_pos_iff x).mp hn
  unfold R
  rw [dif_neg hw, if_pos (show (x.1 0 : ℝ) < 1 / 2 by linarith [h 0])]

private theorem R_upper (x : P) (h : ∀ k, (2 / 3 : ℝ) < x.1 k) :
    (R x : ℝ) = 1 := by
  have hn : ¬ (markers x).Nonempty := by
    rintro ⟨k, hk⟩
    linarith [hk.2, h k]
  have hw := mt (W_pos_iff x).mp hn
  unfold R
  rw [dif_neg hw, if_neg (show ¬ (x.1 0 : ℝ) < 1 / 2 by linarith [h 0])]

private theorem W_eq_sum (x : P) (J : Finset ℤ) (hJ : markers x ⊆ J) :
    W x = ∑ k ∈ J, weight (x.1 k) := by
  apply finsum_eq_sum_of_support_subset
  rw [weight_support]
  exact hJ

private theorem A_eq_sum (x : P) (J : Finset ℤ) (hJ : markers x ⊆ J) :
    A x = ∑ k ∈ J, (2 : ℝ) ^ (-k) * weightedOdds (x.1 k) := by
  apply finsum_eq_sum_of_support_toFinset_subset _ (A_finite x)
  intro k hk
  exact hJ (A_support_subset x ((A_finite x).mem_toFinset.mp hk))

/-- Bounds for the weighted average depend on marker locations, without any
uniform positive lower bound on its weight denominator. -/
private theorem quotient_bounds (x : P) {a b : ℤ} (hab : a ≤ b)
    (heq : markers x = Set.Icc a b) :
    (2 : ℝ) ^ (-b) / 2 ≤ A x / W x ∧ A x / W x ≤ 2 * (2 : ℝ) ^ (-a) := by
  classical
  let J := (marker_finite x).toFinset
  have hJ : markers x ⊆ J := fun _ hk => (marker_finite x).mem_toFinset.mpr hk
  have hw : 0 < W x := (W_pos_iff x).mpr ⟨a, by rw [heq]; exact ⟨le_refl _, hab⟩⟩
  have lower : ((2 : ℝ) ^ (-b) / 2) * W x ≤ A x := by
    rw [W_eq_sum x J hJ, A_eq_sum x J hJ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k ∈ markers x := (marker_finite x).mem_toFinset.mp hk
    have hkb : k ≤ b := (heq ▸ hkm).2
    have hpow : (2 : ℝ) ^ (-b) ≤ (2 : ℝ) ^ (-k) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc
      (2 : ℝ) ^ (-b) / 2 * weight (x.1 k) =
          (2 : ℝ) ^ (-b) * (weight (x.1 k) / 2) := by ring
      _ ≤ (2 : ℝ) ^ (-k) * (weight (x.1 k) / 2) :=
        mul_le_mul_of_nonneg_right hpow (div_nonneg (weight_nonneg _) (by norm_num))
      _ ≤ (2 : ℝ) ^ (-k) * weightedOdds (x.1 k) :=
        mul_le_mul_of_nonneg_left (weightedOdds_bounds _).1 (by positivity)
  have upper : A x ≤ (2 * (2 : ℝ) ^ (-a)) * W x := by
    rw [W_eq_sum x J hJ, A_eq_sum x J hJ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k ∈ markers x := (marker_finite x).mem_toFinset.mp hk
    have hak : a ≤ k := (heq ▸ hkm).1
    have hpow : (2 : ℝ) ^ (-k) ≤ (2 : ℝ) ^ (-a) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc
      (2 : ℝ) ^ (-k) * weightedOdds (x.1 k) ≤
          (2 : ℝ) ^ (-k) * (2 * weight (x.1 k)) :=
        mul_le_mul_of_nonneg_left (weightedOdds_bounds _).2 (by positivity)
      _ ≤ (2 : ℝ) ^ (-a) * (2 * weight (x.1 k)) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg (by norm_num) (weight_nonneg _))
      _ = (2 * (2 : ℝ) ^ (-a)) * weight (x.1 k) := by ring
  exact ⟨(le_div_iff₀ hw).mpr lower, (div_le_iff₀ hw).mpr upper⟩

/-- One persistent marker confines all neighboring supports to one fixed finite window. -/
private theorem local_window {x : P} {j : ℤ} (hj : j ∈ markers x) :
    ∀ᶠ y in 𝓝 x, (markers y).Nonempty ∧
      markers y ⊆ (Finset.Icc (j - 2) (j + 2) : Set ℤ) := by
  have hc : Continuous (fun y : P => weight (y.1 j)) :=
    continuous_weight.comp ((continuous_apply j).comp continuous_subtype_val)
  have hp : ∀ᶠ y in 𝓝 x, 0 < weight (y.1 j) :=
    hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds ((weight_pos_iff _).mpr hj))
  filter_upwards [hp] with y hy
  have hym : j ∈ markers y := (weight_pos_iff _).mp hy
  refine ⟨⟨j, hym⟩, fun k hk => ?_⟩
  have hs := marker_pair_span y hk hym
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

private theorem continuousAt_R_marked (x : P) (hx : (markers x).Nonempty) :
    ContinuousAt (fun y : P => (R y : ℝ)) x := by
  classical
  obtain ⟨j, hj⟩ := hx
  let J := Finset.Icc (j - 2) (j + 2)
  let WJ : P → ℝ := fun y => ∑ k ∈ J, weight (y.1 k)
  let AJ : P → ℝ := fun y => ∑ k ∈ J, (2 : ℝ) ^ (-k) * weightedOdds (y.1 k)
  have hwc : Continuous WJ := by
    apply continuous_finsetSum
    intro k hk
    exact continuous_weight.comp ((continuous_apply k).comp continuous_subtype_val)
  have hac : Continuous AJ := by
    apply continuous_finsetSum
    intro k hk
    exact continuous_const.mul
      (continuous_weightedOdds.comp ((continuous_apply k).comp continuous_subtype_val))
  have he := local_window hj
  have hJ := he.self_of_nhds
  have hW : WJ x = W x := (W_eq_sum x J hJ.2).symm
  have hA : AJ x = A x := (A_eq_sum x J hJ.2).symm
  have hWpos : 0 < WJ x := by rw [hW]; exact (W_pos_iff x).mpr ⟨j, hj⟩
  have hz := hac.continuousAt.div hwc.continuousAt hWpos.ne'
  have hden : 1 + AJ x / WJ x ≠ 0 := by
    rw [hW, hA]
    have := div_nonneg (A_nonneg x) (W_nonneg x)
    linarith
  have hq : ContinuousAt (fun y => Q (AJ y / WJ y)) x :=
    hz.div (continuousAt_const.add hz) hden
  apply hq.congr_of_eventuallyEq
  filter_upwards [he] with y hy
  rw [R_marked y hy.1, A_eq_sum y J hy.2, W_eq_sum y J hy.2]

/-- At a lower cylinder, possible marker blocks escape to positive time. -/
theorem R_lower_cylinder (x : P) (j : ℤ) (hj : (x.1 j : ℝ) < 1 / 2) :
    (R x : ℝ) ≤ 8 * (2 : ℝ) ^ (-j) := by
  rcases marker_cases x with hl | hu | ⟨a, b, hab, hspan, heq, hleft, hright⟩
  · rw [R_lower x hl]
    positivity
  · exfalso
    linarith [hu j]
  · have hjb : j ≤ b := by
      by_contra h
      linarith [hright j (lt_of_not_ge h)]
    have hja : j - 2 ≤ a := by omega
    have hm : (markers x).Nonempty := ⟨a, by rw [heq]; exact ⟨le_refl _, hab⟩⟩
    have hz : 0 ≤ A x / W x := div_nonneg (A_nonneg x) (W_nonneg x)
    rw [R_marked x hm]
    calc
      Q (A x / W x) ≤ A x / W x := by
        exact (div_le_iff₀ (by linarith : 0 < 1 + A x / W x)).mpr (by nlinarith)
      _ ≤ 2 * (2 : ℝ) ^ (-a) := (quotient_bounds x hab heq).2
      _ ≤ 2 * (2 : ℝ) ^ (2 - j) := mul_le_mul_of_nonneg_left
        (zpow_le_zpow_right₀ (by norm_num) (by omega)) (by norm_num)
      _ = 8 * (2 : ℝ) ^ (-j) := by
        rw [show 2 - j = (2 : ℤ) + -j by omega, zpow_add₀ (by norm_num)]
        norm_num
        ring

/-- At an upper cylinder, possible marker blocks escape to negative time. -/
theorem R_upper_cylinder (x : P) (j : ℤ) (hj : (1 / 2 : ℝ) < x.1 j) :
    1 - (R x : ℝ) ≤ 8 * (2 : ℝ) ^ j := by
  rcases marker_cases x with hl | hu | ⟨a, b, hab, hspan, heq, hleft, hright⟩
  · exfalso
    linarith [hl j]
  · rw [R_upper x hu]
    simp only [sub_self]
    positivity
  · have haj : a ≤ j := by
      by_contra h
      linarith [hleft j (lt_of_not_ge h)]
    have hbj : b ≤ j + 2 := by omega
    have hm : (markers x).Nonempty := ⟨a, by rw [heq]; exact ⟨le_refl _, hab⟩⟩
    let z := A x / W x
    have hz : 0 ≤ z := div_nonneg (A_nonneg x) (W_nonneg x)
    have hlow : (2 : ℝ) ^ (-j - 2) / 2 ≤ z :=
      (div_le_div_of_nonneg_right
        (zpow_le_zpow_right₀ (by norm_num) (by omega)) (by norm_num)).trans
        (quotient_bounds x hab heq).1
    have hphase : (2 : ℝ) ^ (-j - 2) / 2 * (8 * (2 : ℝ) ^ j) = 1 := by
      rw [zpow_sub₀ (by norm_num), zpow_neg]
      norm_num
      field_simp
      <;> norm_num
    have hprod : 1 ≤ z * (8 * (2 : ℝ) ^ j) := by
      rw [← hphase]
      exact mul_le_mul_of_nonneg_right hlow (by positivity)
    rw [R_marked x hm]
    change 1 - z / (1 + z) ≤ 8 * (2 : ℝ) ^ j
    have hid : 1 - z / (1 + z) = 1 / (1 + z) := by
      field_simp
      ring
    rw [hid]
    apply (div_le_iff₀ (by linarith : 0 < 1 + z)).mpr
    nlinarith [show 0 < (2 : ℝ) ^ j by positivity]

/-- Continuity includes every nonconstant empty lower-cap sequence. -/
private theorem continuousAt_R_lower (x : P) (hx : ∀ k, (x.1 k : ℝ) < 1 / 3) :
    ContinuousAt (fun y : P => (R y : ℝ)) x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => (8 : ℝ) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 8
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  have hc : Continuous (fun y : P => (y.1 (n : ℤ) : ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply (n : ℤ)).comp continuous_subtype_val)
  have he : ∀ᶠ y in 𝓝 x, (y.1 (n : ℤ) : ℝ) < 1 / 2 :=
    hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith [hx (n : ℤ)]))
  filter_upwards [he] with y hy
  rw [Real.dist_eq, R_lower x hx, sub_zero, abs_of_nonneg (R y).property.1]
  apply lt_of_le_of_lt (R_lower_cylinder y (n : ℤ) hy)
  simpa only [zpow_neg, zpow_natCast, one_div, inv_pow] using hn

/-- Continuity includes every nonconstant empty upper-cap sequence. -/
private theorem continuousAt_R_upper (x : P) (hx : ∀ k, (2 / 3 : ℝ) < x.1 k) :
    ContinuousAt (fun y : P => (R y : ℝ)) x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => (8 : ℝ) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 8
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  have hc : Continuous (fun y : P => (y.1 (-(n : ℤ)) : ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply (-(n : ℤ))).comp continuous_subtype_val)
  have he : ∀ᶠ y in 𝓝 x, (1 / 2 : ℝ) < y.1 (-(n : ℤ)) :=
    hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith [hx (-(n : ℤ))]))
  filter_upwards [he] with y hy
  rw [Real.dist_eq, R_upper x hx, abs_sub_comm, abs_of_nonneg (by linarith [(R y).property.2])]
  apply lt_of_le_of_lt (R_upper_cylinder y (-(n : ℤ)) hy)
  simpa only [zpow_neg, zpow_natCast, one_div, inv_pow] using hn

/-- The explicit finite weighted quotient extends continuously across both empty caps. -/
theorem continuous_R : Continuous R := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases marker_cases x with hl | hu | ⟨a, b, hab, _, heq, _, _⟩
  · exact continuousAt_R_lower x hl
  · exact continuousAt_R_upper x hu
  · exact continuousAt_R_marked x ⟨a, by rw [heq]; exact ⟨le_refl _, hab⟩⟩

/-- Reindexing is valid for every integer translation of the finite sums. -/
theorem W_shift (x : P) (l : ℤ) : W (CompactSelector.shift f l x) = W x := by
  change (∑ᶠ k : ℤ, weight (x.1 (l + k))) = ∑ᶠ k : ℤ, weight (x.1 k)
  exact finsum_comp (g := fun k => weight (x.1 k))
    (Equiv.addLeft l) (Equiv.addLeft l).bijective

theorem A_shift (x : P) (l : ℤ) :
    A (CompactSelector.shift f l x) = (2 : ℝ) ^ l * A x := by
  change (∑ᶠ k : ℤ, (2 : ℝ) ^ (-k) * weightedOdds (x.1 (l + k))) =
    (2 : ℝ) ^ l * ∑ᶠ k : ℤ, (2 : ℝ) ^ (-k) * weightedOdds (x.1 k)
  have hphase (k : ℤ) : (2 : ℝ) ^ (-k) = (2 : ℝ) ^ l * (2 : ℝ) ^ (-(l + k)) := by
    rw [← zpow_add₀ (by norm_num)]
    congr 1
    omega
  calc
    _ = ∑ᶠ k : ℤ, (2 : ℝ) ^ l * ((2 : ℝ) ^ (-(l + k)) * weightedOdds (x.1 (l + k))) :=
      finsum_congr fun k => by rw [hphase]; ring
    _ = (2 : ℝ) ^ l * ∑ᶠ k : ℤ, (2 : ℝ) ^ (-(l + k)) * weightedOdds (x.1 (l + k)) :=
      (mul_finsum _ _).symm
    _ = _ := congrArg ((2 : ℝ) ^ l * ·)
      (finsum_comp (g := fun k => (2 : ℝ) ^ (-k) * weightedOdds (x.1 k))
        (Equiv.addLeft l) (Equiv.addLeft l).bijective)

private theorem Q_scale {s c : ℝ} (hs : 0 ≤ s) (hc : 0 < c) :
    Q (c * s) = c * Q s / (1 - Q s + c * Q s) := by
  have hq := Q_mem hs
  have hd := (denominator_pos hc (⟨Q s, hq⟩ : I)).ne'
  have h₁ : 1 + s ≠ 0 := by positivity
  have h₂ : 1 + c * s ≠ 0 := by positivity
  unfold Q at hd ⊢
  apply (div_eq_div_iff h₂ hd).mpr
  field_simp [h₁]
  ring

/-- Exact one-step equivariance holds also on empty-marker sequences. -/
theorem R_shift_one (x : P) : R (CompactSelector.shift f 1 x) = f (R x) := by
  apply Subtype.ext
  by_cases hw : 0 < W x
  · have hws : 0 < W (CompactSelector.shift f 1 x) := by rwa [W_shift]
    rw [show (R (CompactSelector.shift f 1 x) : ℝ) =
      Q (A (CompactSelector.shift f 1 x) / W (CompactSelector.shift f 1 x)) by simp [R, hws]]
    rw [W_shift, A_shift, zpow_one, f_coe]
    have hr : (R x : ℝ) = Q (A x / W x) := by simp [R, hw]
    rw [hr]
    change Q (2 * A x / W x) = 2 * Q (A x / W x) / (1 + Q (A x / W x))
    rw [show 2 * A x / W x = 2 * (A x / W x) by ring]
    rw [Q_scale (div_nonneg (A_nonneg x) hw.le) (by norm_num)]
    congr 1
    ring
  · rcases marker_cases x with hl | hu | ⟨a, b, hab, _, heq, _, _⟩
    · have hls : ∀ k, ((CompactSelector.shift f 1 x).1 k : ℝ) < 1 / 3 := fun k => hl (1 + k)
      rw [R_lower _ hls, f_coe, R_lower x hl]
      norm_num [rationalIntervalMap]
    · have hus : ∀ k, (2 / 3 : ℝ) < (CompactSelector.shift f 1 x).1 k := fun k => hu (1 + k)
      rw [R_upper _ hus, f_coe, R_upper x hu]
      norm_num [rationalIntervalMap]
    · exact False.elim (hw ((W_pos_iff x).mpr ⟨a, by rw [heq]; exact ⟨le_refl _, hab⟩⟩))

/-- The same rational map commutes with the selector at every positive or negative time. -/
theorem R_shift (x : P) (l : ℤ) :
    R (CompactSelector.shift f l x) = (f ^ l) (R x) :=
  CompactSelector.equivariant_integer f R R_shift_one l x

private theorem odds_action (c : ℝ) (hc : 0 < c) (u : I) (hu : (u : ℝ) < 1) :
    (action c hc u : ℝ) / (1 - (action c hc u : ℝ)) = c * ((u : ℝ) / (1 - u)) := by
  have hd := (denominator_pos hc u).ne'
  have hu' : 1 - (u : ℝ) ≠ 0 := by linarith
  have hdiff : 1 - (action c hc u : ℝ) = (1 - (u : ℝ)) / (1 - u + c * u) := by
    rw [action_coe]
    field_simp
    ring
  rw [hdiff, action_coe]
  field_simp

private theorem trueOrbit_marked (p : I) (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1) :
    (markers (CompactSelector.trueOrbit f (by norm_num : (0 : ℝ) ≤ 1 / 256) p)).Nonempty := by
  let x : P := CompactSelector.trueOrbit f (by norm_num) p
  change (markers x).Nonempty
  rcases marker_cases x with hl | hu | ⟨a, b, hab, _, heq, _, _⟩
  · have hlim := orbit_pos_tendsto p hp
    have hle : (1 : ℝ) ≤ 1 / 3 := le_of_tendsto hlim (Eventually.of_forall fun n => (hl n).le)
    norm_num at hle
  · have hlim := orbit_neg_tendsto p hp'
    have hle : (2 / 3 : ℝ) ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun n => (hu (-(n : ℤ))).le)
    norm_num at hle
  · exact ⟨a, by rw [heq]; exact ⟨le_refl _, hab⟩⟩

private theorem trueOrbit_phase (p : I) (hp : (p : ℝ) < 1) (k : ℤ) :
    let x : P := CompactSelector.trueOrbit f (by norm_num) p
    (2 : ℝ) ^ (-k) * weightedOdds (x.1 k) = weight (x.1 k) * ((p : ℝ) / (1 - p)) := by
  dsimp only
  let y := (f ^ k) p
  change (2 : ℝ) ^ (-k) * weightedOdds y = weight y * ((p : ℝ) / (1 - p))
  by_cases hw : weight y = 0
  · simp [hw, weightedOdds_eq_zero y hw]
  · have hy := (weight_pos_iff y).mp (lt_of_le_of_ne (weight_nonneg y) (Ne.symm hw))
    have hmax : max (1 / 3 : ℝ) (1 - (y : ℝ)) = 1 - y := max_eq_right (by linarith [hy.2])
    have ho : (y : ℝ) / (1 - y) = (2 : ℝ) ^ k * ((p : ℝ) / (1 - p)) := by
      change ((f ^ k) p : ℝ) / (1 - ((f ^ k) p : ℝ)) = _
      rw [f_zpow]
      exact odds_action _ (by positivity) p hp
    rw [weightedOdds, hmax]
    calc
      (2 : ℝ) ^ (-k) * (weight y * y / (1 - (y : ℝ))) =
          weight y * ((2 : ℝ) ^ (-k) * ((y : ℝ) / (1 - y))) := by ring
      _ = weight y * ((2 : ℝ) ^ (-k) * ((2 : ℝ) ^ k * ((p : ℝ) / (1 - p)))) := by rw [ho]
      _ = weight y * ((p : ℝ) / (1 - p)) := by
        have hcancel : (2 : ℝ) ^ (-k) * (2 : ℝ) ^ k = 1 := by
          rw [← zpow_add₀ (by norm_num), neg_add_cancel, zpow_zero]
        rw [← mul_assoc ((2 : ℝ) ^ (-k)), hcancel, one_mul]

/-- Every true orbit is fixed, including both endpoint orbits. -/
theorem R_trueOrbit (p : I) :
    R (CompactSelector.trueOrbit f (by norm_num : (0 : ℝ) ≤ 1 / 256) p) = p := by
  apply Subtype.ext
  rcases eq_or_lt_of_le p.property.1 with hp | hp
  · have hp0 : p = ⟨0, by norm_num⟩ := Subtype.ext hp.symm
    subst p
    apply R_lower
    intro k
    change ((f ^ k) ⟨0, by norm_num⟩ : ℝ) < 1 / 3
    rw [f_zpow, homeomorph_apply, action_zero]
    norm_num
  · rcases lt_or_eq_of_le p.property.2 with hp' | hp'
    · let x : P := CompactSelector.trueOrbit f (by norm_num) p
      have hm := trueOrbit_marked p hp hp'
      have hw := (W_pos_iff x).mpr hm
      have ha : A x = W x * ((p : ℝ) / (1 - p)) := by
        unfold A W
        rw [finsum_mul]
        exact finsum_congr (trueOrbit_phase p hp')
      change (R x : ℝ) = (p : ℝ)
      rw [R_marked x hm, ha, mul_div_cancel_left₀ _ hw.ne']
      unfold Q
      have hd : 1 - (p : ℝ) ≠ 0 := by linarith
      field_simp
      <;> ring
    · have hp1 : p = ⟨1, by norm_num⟩ := Subtype.ext hp'
      subst p
      apply R_upper
      intro k
      change (2 / 3 : ℝ) < ((f ^ k) ⟨1, by norm_num⟩ : ℝ)
      rw [f_zpow, homeomorph_apply, action_top]
      norm_num

/-- The completed compact-selector result now applies to this one explicit `R`:
all accuracies, all integer centers, and all two-sided limit-error sequences. -/
theorem R_global_and_limit_shadowing :
    (∀ ε > 0, ∃ γ > 0, ∃ hγδ : γ ≤ (1 / 256 : ℝ),
      ∀ (x : CompactSelector.Space f γ) (k : ℤ),
        dist ((f ^ k) (R (CompactSelector.inclusion f hγδ x))) (x.1 k) < ε) ∧
    (∀ x : P, Tendsto (CompactSelector.linkError f x.1) cofinite (𝓝 0) →
      (∀ ε > 0, ∃ N : ℕ, ∀ k : ℤ, N ≤ k.natAbs →
        dist ((f ^ k) (R x)) (x.1 k) < ε) ∧
      Tendsto (fun k : ℤ => dist ((f ^ k) (R x)) (x.1 k)) cofinite (𝓝 0)) :=
  CompactSelector.global_and_limit_shadowing f (by norm_num) R continuous_R R_trueOrbit R_shift_one

#print axioms continuous_R
#print axioms R_shift
#print axioms R_trueOrbit
#print axioms R_global_and_limit_shadowing

end D5.S1.Dynamics.Shadowing.RationalInterval
