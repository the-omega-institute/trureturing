/- GID: D5/S3/TotalVariation/Pinsker
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Pinsker
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define finite total variation, pin its normalization, and prove Pinsker's inequality. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `Pinsker`, `totalVariation`, `total variation`,
     `KullbackLeibler`, `klDiv`, `klFun`, `binary divergence`, `two-point`,
     `klFun.*sq`, `log_le_sub_one_of_pos`, and `le_log_one_add_of_nonneg`.
   * No theorem named for Pinsker's inequality, no finite real-valued total-variation/KL bridge,
     and no scalar binary Pinsker bound was found. Mathlib's similarly named total variations are
     variations of functions, vector measures, or signed measures. Its information-theoretic
     `InformationTheory.klDiv` is measure-valued in `ℝ≥0∞`; this file does not rebuild a bridge
     to it.
   * Repository grep over every Lean declaration below `D5/S3` found the frozen finite-real
     `klDivergence` and its DPI/Gibbs theorems, but no total-variation definition or Pinsker bound.
   * The proof below therefore reuses the frozen zero-support DPI identity and Gibbs inequality;
     only the scalar binary estimate and the finite positive-part identity are proved here.
-/

import D5.S3.Divergence.GrandmotherTheorem
import D5.S3.DivergenceSupport.ZeroSupportDPI

namespace D5.S3.TotalVariation.Pinsker

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open D5.S3.DivergenceSupport.ZeroSupportDPI

/-- Total variation of two finite real mass functions, in the probability-theory normalization:
one half of their `L¹` distance. The factor `1 / 2` makes disjoint probability masses have
distance one and is pinned by `total_variation_eq_sum_positive`. -/
noncomputable def totalVariation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, |p i - q i|

/-- For mass functions of equal total mass, total variation is exactly the mass excess on the
coordinates where `p` dominates `q`. No sign hypothesis is needed: equal total mass alone balances
the positive and negative parts of `p - q`. -/
theorem total_variation_eq_sum_positive {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hmass : ∑ i, p i = ∑ i, q i) :
    totalVariation p q = ∑ i with q i ≤ p i, (p i - q i) := by
  classical
  let positive : ℝ := ∑ i with q i ≤ p i, (p i - q i)
  let negative : ℝ := ∑ i with ¬q i ≤ p i, (p i - q i)
  have htotal : (∑ i, (p i - q i)) = 0 := by
    rw [Finset.sum_sub_distrib, hmass, sub_self]
  have hbalance : positive + negative = 0 := by
    dsimp [positive, negative]
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)]
    exact htotal
  have habs : (∑ i, |p i - q i|) = positive - negative := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)
      (fun i => |p i - q i|)]
    change (∑ i with q i ≤ p i, |p i - q i|) +
        (∑ i with ¬q i ≤ p i, |p i - q i|) = positive - negative
    have hpositive_abs :
        (∑ i with q i ≤ p i, |p i - q i|) = positive := by
      dsimp [positive]
      apply Finset.sum_congr rfl
      intro i hi
      exact abs_of_nonneg (sub_nonneg.mpr (Finset.mem_filter.mp hi).2)
    have hnegative_abs :
        (∑ i with ¬q i ≤ p i, |p i - q i|) = -negative := by
      dsimp [negative]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_nonpos]
      exact sub_nonpos.mpr (le_of_not_ge (Finset.mem_filter.mp hi).2)
    rw [hpositive_abs, hnegative_abs, sub_eq_add_neg]
  rw [totalVariation, habs]
  dsimp [positive] at hbalance ⊢
  linarith

/-- Pinsker's inequality for two Bernoulli mass functions. The last two hypotheses are precisely
discrete absolute continuity on the two points: a zero of either reference mass forces the
corresponding source mass to vanish. -/
theorem binary_pinsker (a b : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hac_zero : b = 0 → a = 0)
    (hac_one : 1 - b = 0 → 1 - a = 0) :
    2 * (a - b) ^ 2 ≤
      a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  by_cases hb_zero : b = 0
  · have ha_zero := hac_zero hb_zero
    simp [hb_zero, ha_zero]
  by_cases hb_one : b = 1
  · have ha_one : a = 1 := by
      have := hac_one (by simp [hb_one])
      linarith
    simp [hb_one, ha_one]
  have hb_pos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb_zero)
  have hb_lt_one : b < 1 := lt_of_le_of_ne hb.2 hb_one
  have h_one_sub_b_ne : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb_one)
  let f : ℝ → ℝ := fun x =>
    x * Real.log x + (1 - x) * Real.log (1 - x) - x * Real.log b -
      (1 - x) * Real.log (1 - b) - 2 * (x - b) ^ 2
  let f' : ℝ → ℝ := fun x =>
    Real.log x - Real.log (1 - x) - Real.log b + Real.log (1 - b) - 4 * (x - b)
  let f'' : ℝ → ℝ := fun x => x⁻¹ + (1 - x)⁻¹ - 4
  have hf_continuous : Continuous f := by
    dsimp [f]
    exact (((Real.continuous_mul_log.add
          (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).sub
        (continuous_id.mul continuous_const)).sub
      ((continuous_const.sub continuous_id).mul continuous_const)).sub
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 2))
  have hf_deriv (x : ℝ) (hx_pos : 0 < x) (hx_lt_one : x < 1) :
      HasDerivAt f (f' x) x := by
    have h_one_sub_x : 0 < 1 - x := sub_pos.mpr hx_lt_one
    have h_entropy_complement :=
      (Real.hasDerivAt_mul_log h_one_sub_x.ne').comp x
        ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
    have hraw := (((((Real.hasDerivAt_mul_log hx_pos.ne').add h_entropy_complement).sub
        ((hasDerivAt_id x).mul_const (Real.log b))).sub
      (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul_const
        (Real.log (1 - b)))).sub
      (HasDerivAt.const_mul 2 (((hasDerivAt_id x).sub_const b).pow 2)))
    have hnormalized : HasDerivAt _ (f' x) x := hraw.congr_deriv (by
      dsimp [f']
      ring)
    refine hnormalized.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    dsimp [f]
  have hf'_deriv (x : ℝ) (hx_pos : 0 < x) (hx_lt_one : x < 1) :
      HasDerivAt f' (f'' x) x := by
    have h_one_sub_x : 0 < 1 - x := sub_pos.mpr hx_lt_one
    have h_log_complement :=
      (Real.hasDerivAt_log h_one_sub_x.ne').comp x
        ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
    have hraw := (((((Real.hasDerivAt_log hx_pos.ne').sub h_log_complement).sub_const
        (Real.log b)).add_const (Real.log (1 - b))).sub
      (HasDerivAt.const_mul 4 ((hasDerivAt_id x).sub_const b)))
    have hnormalized : HasDerivAt _ (f'' x) x := hraw.congr_deriv (by
      dsimp [f'']
      ring)
    refine hnormalized.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    dsimp [f']
  have hf''_nonneg (x : ℝ) (hx : x ∈ interior (Set.Icc (0 : ℝ) 1)) : 0 ≤ f'' x := by
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa using hx
    have hprod_pos : 0 < x * (1 - x) := mul_pos hx'.1 (sub_pos.mpr hx'.2)
    have hidentity : f'' x * (x * (1 - x)) = (2 * x - 1) ^ 2 := by
      dsimp [f'']
      field_simp [hx'.1.ne', (sub_pos.mpr hx'.2).ne']
      ring
    nlinarith [sq_nonneg (2 * x - 1)]
  have hf_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hf_continuous.continuousOn
      (fun x hx => by
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
        exact (hf_deriv x hx'.1 hx'.2).hasDerivWithinAt)
      (fun x hx => by
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
        exact (hf'_deriv x hx'.1 hx'.2).hasDerivWithinAt)
      hf''_nonneg
  have hb_mem : b ∈ Set.Icc (0 : ℝ) 1 := ⟨hb.1, hb.2⟩
  have ha_mem : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.1, ha.2⟩
  have hf_deriv_b : HasDerivAt f 0 b := by
    convert hf_deriv b hb_pos hb_lt_one using 1
    dsimp [f']
    ring
  have hf_b : f b = 0 := by
    dsimp [f]
    ring
  have hf_a_nonneg : 0 ≤ f a := by
    rcases lt_trichotomy a b with hab | hab | hab
    · have hslope := hf_convex.slope_le_of_hasDerivAt ha_mem hb_mem hab hf_deriv_b
      rw [slope_def_field, hf_b] at hslope
      have hnumerator : 0 - f a ≤ 0 := by
        simpa only [zero_mul] using (div_le_iff₀ (sub_pos.mpr hab)).mp hslope
      linarith
    · simp [hab, hf_b]
    · have hslope := hf_convex.le_slope_of_hasDerivAt hb_mem ha_mem hab hf_deriv_b
      rw [slope_def_field, hf_b] at hslope
      have hnumerator : 0 ≤ f a - 0 := by
        simpa only [zero_mul] using (le_div_iff₀ (sub_pos.mpr hab)).mp hslope
      linarith
  have hf_as_divergence :
      f a = a * Real.log (a / b) +
          (1 - a) * Real.log ((1 - a) / (1 - b)) - 2 * (a - b) ^ 2 := by
    by_cases ha_zero : a = 0
    · subst a
      simp [f]
    by_cases ha_one : a = 1
    · subst a
      simp [f]
    have h_one_sub_a_ne : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha_one)
    dsimp [f]
    rw [Real.log_div ha_zero hb_zero, Real.log_div h_one_sub_a_ne h_one_sub_b_ne]
    ring
  rw [hf_as_divergence] at hf_a_nonneg
  linarith

/-- Data processing for the repository's general-support convention. This is the nonnegative
channel form needed by the deterministic two-point channel below; the frozen strict-positive
channel theorem cannot apply to such a channel. -/
theorem kl_divergence_channel_le_zero_support
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1)
    (hac : ∀ x, q x = 0 → p x = 0)
    (hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    klDivergence (channelOutput W p) (channelOutput W q) ≤ klDivergence p q := by
  classical
  have hOutputPNonneg (y : Y) : 0 ≤ channelOutput W p y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp.1 x) (hW.1 x y)
  have hOutputQNonneg (y : Y) : 0 ≤ channelOutput W q y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hq.1 x) (hW.1 x y)
  have hOutputAC (y : Y) (hy : channelOutput W q y = 0) :
      channelOutput W p y = 0 :=
    channel_output_absolute_continuity p q W hq.1 hac hW.1 y hy
  have hJointAC (x : X) (y : Y) (hxy : q x * W x y = 0) :
      p x * W x y = 0 := by
    rcases mul_eq_zero.mp hxy with hqx | hWxy
    · simp [hac x hqx]
    · simp [hWxy]
  have hWeightedPosteriorNonneg (y : Y) :
      0 ≤ channelOutput W p y *
        klDivergence (posterior W p y) (posterior W q y) := by
    by_cases hOutputPZero : channelOutput W p y = 0
    · simp [hOutputPZero]
    have hOutputPPos : 0 < channelOutput W p y :=
      lt_of_le_of_ne (hOutputPNonneg y) (Ne.symm hOutputPZero)
    have hOutputQNe : channelOutput W q y ≠ 0 := by
      intro hOutputQZero
      exact hOutputPZero (hOutputAC y hOutputQZero)
    have hOutputQPos : 0 < channelOutput W q y :=
      lt_of_le_of_ne (hOutputQNonneg y) (Ne.symm hOutputQNe)
    have hPosteriorP :
        (∀ x, 0 ≤ posterior W p y x) ∧ ∑ x, posterior W p y x = 1 := by
      refine ⟨fun x => div_nonneg (mul_nonneg (hp.1 x) (hW.1 x y)) hOutputPPos.le, ?_⟩
      simp only [posterior, ← Finset.sum_div]
      exact div_self hOutputPZero
    have hPosteriorQ :
        (∀ x, 0 ≤ posterior W q y x) ∧ ∑ x, posterior W q y x = 1 := by
      refine ⟨fun x => div_nonneg (mul_nonneg (hq.1 x) (hW.1 x y)) hOutputQPos.le, ?_⟩
      simp only [posterior, ← Finset.sum_div]
      exact div_self hOutputQNe
    have hPosteriorAC (x : X) (hx : posterior W q y x = 0) :
        posterior W p y x = 0 := by
      simp only [posterior] at hx ⊢
      have hJointQZero : q x * W x y = 0 := by
        exact (div_eq_zero_iff).mp hx |>.resolve_right hOutputQNe
      simp [hJointAC x y hJointQZero]
    exact mul_nonneg hOutputPPos.le
      (kl_divergence_nonneg _ _ hPosteriorP hPosteriorQ hPosteriorAC)
  rw [classical_dpi_identity_zero_support p q W hp hq hac hW]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun y _ => hWeightedPosteriorNonneg y)

/-- Pinsker's inequality for nonnegative normalized finite mass functions under the repository's
discrete absolute-continuity convention `q i = 0 → p i = 0`. -/
theorem pinsker_inequality {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    2 * (totalVariation p q) ^ 2 ≤ klDivergence p q := by
  classical
  let W : ι → Bool → ℝ := fun i y =>
    match y with
    | true => if q i ≤ p i then 1 else 0
    | false => if q i ≤ p i then 0 else 1
  let a : ℝ := ∑ i with q i ≤ p i, p i
  let b : ℝ := ∑ i with q i ≤ p i, q i
  have hW : (∀ i y, 0 ≤ W i y) ∧ ∀ i, ∑ y, W i y = 1 := by
    constructor
    · intro i y
      cases y <;> by_cases hi : q i ≤ p i <;> simp [W, hi]
    · intro i
      rw [Fintype.sum_bool]
      by_cases hi : q i ≤ p i <;> simp [W, hi]
  have hOutputPTrue : channelOutput W p true = a := by
    rw [channelOutput]
    simp [W, a, Finset.sum_filter]
  have hOutputQTrue : channelOutput W q true = b := by
    rw [channelOutput]
    simp [W, b, Finset.sum_filter]
  have hOutputSum (r : ι → ℝ) (hr : ∑ i, r i = 1) :
      channelOutput W r true + channelOutput W r false = 1 := by
    rw [channelOutput, channelOutput, ← Finset.sum_add_distrib]
    calc
      (∑ i, (r i * W i true + r i * W i false)) = ∑ i, r i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : q i ≤ p i <;> simp [W, hi]
      _ = 1 := hr
  have hOutputPFalse : channelOutput W p false = 1 - a := by
    linarith [hOutputSum p hp.2, hOutputPTrue]
  have hOutputQFalse : channelOutput W q false = 1 - b := by
    linarith [hOutputSum q hq.2, hOutputQTrue]
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact Finset.sum_nonneg fun i _ => hp.1 i
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact Finset.sum_nonneg fun i _ => hq.1 i
  have ha_le_one : a ≤ 1 := by
    have hcomplement : 0 ≤ ∑ i with ¬q i ≤ p i, p i :=
      Finset.sum_nonneg fun i _ => hp.1 i
    have hpartition :=
      Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i) p
    dsimp [a]
    rw [hp.2] at hpartition
    linarith
  have hb_le_one : b ≤ 1 := by
    have hcomplement : 0 ≤ ∑ i with ¬q i ≤ p i, q i :=
      Finset.sum_nonneg fun i _ => hq.1 i
    have hpartition :=
      Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i) q
    dsimp [b]
    rw [hq.2] at hpartition
    linarith
  have hOutputAC (y : Bool) (hy : channelOutput W q y = 0) :
      channelOutput W p y = 0 :=
    channel_output_absolute_continuity p q W hq.1 hac hW.1 y hy
  have habsoluteZero : b = 0 → a = 0 := by
    intro hbZero
    have := hOutputAC true (by rwa [hOutputQTrue])
    rwa [hOutputPTrue] at this
  have habsoluteOne : 1 - b = 0 → 1 - a = 0 := by
    intro hbOne
    have := hOutputAC false (by rwa [hOutputQFalse])
    rwa [hOutputPFalse] at this
  have hbinary := binary_pinsker a b ⟨ha_nonneg, ha_le_one⟩ ⟨hb_nonneg, hb_le_one⟩
    habsoluteZero habsoluteOne
  have hOutputKL :
      klDivergence (channelOutput W p) (channelOutput W q) =
        a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) := by
    rw [klDivergence, Fintype.sum_bool, hOutputPTrue, hOutputQTrue,
      hOutputPFalse, hOutputQFalse]
  have htv : totalVariation p q = a - b := by
    rw [total_variation_eq_sum_positive p q (hp.2.trans hq.2.symm)]
    dsimp [a, b]
    rw [Finset.sum_sub_distrib]
  calc
    2 * (totalVariation p q) ^ 2 = 2 * (a - b) ^ 2 := by rw [htv]
    _ ≤ a * Real.log (a / b) +
        (1 - a) * Real.log ((1 - a) / (1 - b)) := hbinary
    _ = klDivergence (channelOutput W p) (channelOutput W q) := hOutputKL.symm
    _ ≤ klDivergence p q :=
      kl_divergence_channel_le_zero_support p q W hp hq hac hW

end D5.S3.TotalVariation.Pinsker
