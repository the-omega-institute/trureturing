/- GID: D5/S3/Analytic/Oscillation/MontgomeryCountDiscrepancy
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomeryCountDiscrepancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform Montgomery unit-band profile forces unbounded two-term count discrepancy. -/

import D5.S3.Analytic.Oscillation.MontgomeryAutocorrelationLimit
import D5.S3.Analytic.Oscillation.BandLimitedWindowVariance
import Mathlib.Algebra.Order.Field.Pointwise

/-! A uniform Montgomery unit-band profile forces unbounded two-term count discrepancy. -/

namespace D5.S3.Analytic.Oscillation.MontgomeryCountDiscrepancy

noncomputable section

open SmoothedSpectrumCounting MontgomeryAutocorrelationLimit

namespace SpatialTail

open MeasureTheory Set Finset


private lemma integrate_scaled_shift (q : ℝ → ℝ) (a γ : ℝ) (ha : 0 < a) :
    (∫ y : ℝ, q (a * (y - γ))) = a⁻¹ * ∫ u : ℝ, q u := by
  simp_rw [sub_eq_add_neg]
  change (∫ y : ℝ, (fun z => q (a * z)) (y + -γ)) = _
  rw [integral_add_right_eq_self (fun z => q (a * z)) (-γ),
    Measure.integral_comp_mul_left, smul_eq_mul, abs_of_pos (inv_pos.mpr ha)]

private lemma scaled_shift_spatial_tail (g : ℝ → ℝ) (hg : Integrable g) (a H R γ : ℝ) (ha : 0 < a)
    (hleft : R ≤ a * γ) (hright : R ≤ a * (H - γ)) :
    (∫ y in (Icc 0 H)ᶜ, |g (a * (y - γ))|) ≤
      a⁻¹ * ∫ u in {u : ℝ | R ≤ |u|}, |g u| := by
  let Tail : Set ℝ := {u | R ≤ |u|}
  let q := Tail.indicator (fun u => |g u|)
  have hTail : MeasurableSet Tail := measurableSet_le measurable_const continuous_abs.measurable
  have hq : Integrable q := (hg.abs).indicator hTail
  have hqshift : Integrable (fun y => q (a * (y - γ))) := by
    simpa only [sub_eq_add_neg] using (hq.comp_mul_left' ha.ne').comp_add_right (-γ)
  have hpoint : ∀ y ∈ (Icc 0 H)ᶜ, q (a * (y - γ)) = |g (a * (y - γ))| := by
    intro y hy
    have hy' : y < 0 ∨ H < y := by
      by_contra! hn
      exact hy hn
    have hm : a * (y - γ) ∈ Tail := by
      change R ≤ |a * (y - γ)|
      rcases hy' with hy' | hy'
      · have hy'' : γ ≤ -(y - γ) := by linarith
        exact hleft.trans ((mul_le_mul_of_nonneg_left hy'' ha.le).trans (by rw [mul_neg]; exact neg_le_abs _))
      · exact hright.trans ((mul_le_mul_of_nonneg_left (sub_le_sub_right hy'.le _) ha.le).trans (le_abs_self _))
    exact indicator_of_mem hm _
  calc
    _ = ∫ y in (Icc 0 H)ᶜ, q (a * (y - γ)) := by
      apply setIntegral_congr_fun measurableSet_Icc.compl
      exact fun y hy => (hpoint y hy).symm
    _ ≤ ∫ y : ℝ, q (a * (y - γ)) := by
      apply setIntegral_le_integral hqshift
      exact ae_of_all _ fun y => indicator_nonneg (fun _ _ => abs_nonneg _) _
    _ = _ := by
      rw [integrate_scaled_shift _ a γ ha]
      congr 1
      exact integral_indicator hTail

private theorem spatial_tail_le {J : Type*} (s b : Finset J) (hb : b ⊆ s) (γ : J → ℝ)
    (g : ℝ → ℝ) (hg : Integrable g) (a H R : ℝ) (ha : 0 < a)
    (hinterior : ∀ i ∈ s, i ∉ b → R ≤ a * γ i ∧ R ≤ a * (H - γ i)) :
    (∫ y in (Icc 0 H)ᶜ, |∑ i ∈ s, g (a * (y - γ i))|) ≤
      a⁻¹ * ((b.card : ℝ) * (∫ u : ℝ, |g u|) +
        (s.card : ℝ) * (∫ u in {u : ℝ | R ≤ |u|}, |g u|)) := by
  classical
  let f (i : J) (y : ℝ) := g (a * (y - γ i))
  let U := (Icc 0 H)ᶜ
  let T := {u : ℝ | R ≤ |u|}
  let L := ∫ u : ℝ, |g u|
  let E := ∫ u in T, |g u|
  have hE : 0 ≤ E := integral_nonneg fun _ => abs_nonneg _
  have hi (i : J) : Integrable (f i) := by
    simpa only [f, sub_eq_add_neg] using ((hg.comp_mul_left' ha.ne').comp_add_right (-γ i))
  have hsum : (∫ y in U, |∑ i ∈ s, f i y|) ≤ ∑ i ∈ s, ∫ y in U, |f i y| := by
    have hleft := (integrable_finsetSum s (fun i _ => (hi i).integrableOn (s := U))).abs
    have hright := integrable_finsetSum s (fun i _ => (hi i).abs.integrableOn (s := U))
    exact (integral_mono hleft hright fun y => abs_sum_le_sum_abs _ _).trans_eq
      (integral_finsetSum s (fun i _ => (hi i).abs.integrableOn (s := U)))
  have hbi (i : J) : (∫ y in U, |f i y|) ≤ a⁻¹ * L := by
    apply (setIntegral_le_integral (hi i).abs (ae_of_all _ fun _ => abs_nonneg _)).trans_eq
    exact integrate_scaled_shift (fun u => |g u|) a (γ i) ha
  have hsi (i : J) (hi : i ∈ s \ b) : (∫ y in U, |f i y|) ≤ a⁻¹ * E := by
    obtain ⟨hleft, hright⟩ := hinterior i (mem_sdiff.mp hi).1 (mem_sdiff.mp hi).2
    exact scaled_shift_spatial_tail g hg a H R (γ i) ha hleft hright
  refine hsum.trans ?_
  rw [← sum_sdiff hb (f := fun i => ∫ y in U, |f i y|)]
  have hB : (∑ i ∈ b, ∫ y in U, |f i y|) ≤ (b.card : ℝ) * (a⁻¹ * L) := by
    simpa only [sum_const, nsmul_eq_mul] using (sum_le_sum fun i (_ : i ∈ b) => hbi i)
  have hS : (∑ i ∈ s \ b, ∫ y in U, |f i y|) ≤ (s.card : ℝ) * (a⁻¹ * E) := by
    calc
      _ ≤ ((s \ b).card : ℝ) * (a⁻¹ * E) := by
        simpa only [sum_const, nsmul_eq_mul] using (sum_le_sum hsi)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset)
        (mul_nonneg (inv_nonneg.mpr ha.le) hE)
  exact (add_le_add hS hB).trans_eq (by ring)

end SpatialTail

namespace Square

open MeasureTheory Finset


private lemma shifted_integrable (g : ℝ → ℝ) (hg : Integrable g) {a : ℝ} (ha : 0 < a)
    (b : ℝ) : Integrable (fun x => g (a * (x - b))) := by
  simpa only [sub_eq_add_neg] using (hg.comp_mul_left' ha.ne').comp_add_right (-b)

private theorem smoothed_count_square {J : Type*} (s : Finset J) (x : J → ℝ) (g : ℝ → ℝ)
    (hg : Integrable g) (B : ℝ) (hgB : ∀ u, ‖g u‖ ≤ B)
    (a : ℝ) (ha : 0 < a) :
    a * (∫ y : ℝ, (∑ j ∈ s, g (a * (y - x j))) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, ∫ u : ℝ, g u * g (u + a * (x i - x j)) := by
  let v (i : J) (y : ℝ) := g (a * (y - x i))
  have hi (i : J) : Integrable (v i) := shifted_integrable g hg ha (x i)
  have hprod (i j : J) : Integrable (fun y => v i y * v j y) :=
    (hi i).mul_bdd (hi j).aestronglyMeasurable (ae_of_all _ (fun y => hgB _))
  change a * (∫ y : ℝ, (∑ j ∈ s, v j y) ^ 2) = _
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum _ (fun j _ => hprod i j))]
  simp_rw [integral_finsetSum s (fun j _ => hprod _ j), mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let q (u : ℝ) := g u * g (u + a * (x i - x j))
  have hfg : (fun y : ℝ => v i y * v j y) = fun y => q (a * (y - x i)) := by
    funext y
    dsimp [q, v]
    rw [show a * (y - x j) = a * (y - x i) + a * (x i - x j) by ring]
  rw [hfg]
  change a * (∫ y : ℝ, (fun z => q (a * z)) (y - x i)) = ∫ u : ℝ, q u
  simp_rw [sub_eq_add_neg]
  rw [integral_add_right_eq_self (fun z => q (a * z)) (-x i), Measure.integral_comp_mul_left, smul_eq_mul,
    abs_of_pos (inv_pos.mpr ha), ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

end Square

open Filter MeasureTheory Set Finset
open D5.S3.Analytic.Oscillation.OrdinateCounting
open scoped Topology FourierTransform SchwartzMap

private lemma shell_sum_bound {J : Type*} (s : Finset J) (k : J → ℕ) (D : ℕ)
    (B : ℕ → ℝ) (hB : Summable B) (hB0 : ∀ n, 0 ≤ B n)
    (hD : ∀ n, (s.filter (fun j => k j = n)).card ≤ D) :
    ∑ j ∈ s, B (k j) ≤ (D : ℝ) * ∑' n, B n := by
  classical
  rw [← sum_fiberwise_of_maps_to (fun j hj => mem_image_of_mem k hj)]
  calc
    _ ≤ ∑ n ∈ s.image k, (D : ℝ) * B n := by
      apply sum_le_sum
      intro n _
      calc
        _ = ((s.filter (fun j => k j = n)).card : ℝ) * B n := by
          rw [← nsmul_eq_mul, ← sum_const]
          exact sum_congr rfl fun j hj => congrArg B (mem_filter.mp hj).2
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hD n) (hB0 n)
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (hB.sum_le_tsum _ (fun n _ => hB0 n)) (by positivity)

private lemma smoothed_count_bounded (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E : ℝ)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ H : ℝ in atTop, ∀ x : ℝ, |smoothCount S g H x| ≤ K := by
  obtain ⟨D, hD⟩ := shells_bounded S E hcount
  obtain ⟨B, hB, hB0, hdecay⟩ := schwartz_shell_majorant g 0
  refine ⟨(D : ℝ) * ∑' n, B n,
    mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg hB0), ?_⟩
  filter_upwards [hD] with H hDH
  intro x
  let s := CutDensity.copies (S.cut H) S.mult
  let u (j : Σ i : S.index, Fin (S.mult i)) := meanScale H * (x - S.gamma j.1)
  change |∑ j ∈ s, g (u j)| ≤ _
  calc
    _ ≤ ∑ j ∈ s, |g (u j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, B ⌊|u j|⌋₊ := by
      apply sum_le_sum
      intro j _
      simpa only [pow_zero, one_mul] using hdecay (u j)
    _ ≤ _ := shell_sum_bound s (fun j => ⌊|u j|⌋₊) D B hB hB0 (hDH x)

private lemma finite_interval_count {J : Type*} (s : Finset J) (γ : J → ℝ)
    (F : ℝ → ℝ) (a D x y : ℝ) (hxy : x ≤ y)
    (hF : F y - F x ≤ a * (y - x))
    (hD : ∀ t, |PrefixDiscrepancy.prefixCount s γ t - F t| ≤ D) :
    ((s.filter (fun j => x < γ j ∧ γ j ≤ y)).card : ℝ) ≤ a * (y - x) + 2 * D := by
  classical
  let cut (t : ℝ) := s.filter (fun j => γ j ≤ t)
  have hsub : cut x ⊆ cut y := fun j hj => by
    rw [mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.trans hxy⟩
  have he : s.filter (fun j => x < γ j ∧ γ j ≤ y) = cut y \ cut x := by
    ext j
    simp only [cut, mem_filter, Finset.mem_sdiff, ← not_le (a := γ j)]
    tauto
  have hc : ((cut y \ cut x).card : ℝ) =
      PrefixDiscrepancy.prefixCount s γ y - PrefixDiscrepancy.prefixCount s γ x := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    rfl
  rw [he, hc]
  linarith [(abs_le.mp (hD y)).2, (abs_le.mp (hD x)).1]

private lemma spatial_cap (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E : ℝ)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    ∀ᶠ H : ℝ in atTop,
    (∫ x in (Icc 0 H)ᶜ, |smoothCount S g H x|) / H ≤
      ((2 + 4 * max (S.N (2 * Real.pi) : ℝ)
        (E + |CutDensity.countMain (2 * Real.pi) (2 * Real.pi)|) / meanScale H) / H) *
        (∫ u : ℝ, |g u|) +
      ((S.N H : ℝ) / (H * meanScale H)) * (∫ u in {u : ℝ | meanScale H ≤ |u|}, |g u|) := by
  let C := 2 * Real.pi
  let D := max (S.N C : ℝ) (E + |CutDensity.countMain C C|)
  have hC : 1 ≤ C := by dsimp [C]; linarith [Real.pi_gt_three]
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop C] with H hH hHC
  classical
  let a := meanScale H
  let s := CutDensity.copies (S.cut H) S.mult
  let γ (j : Σ i : S.index, Fin (S.mult i)) := S.gamma j.1
  let b := s.filter (fun j => γ j ≤ 1 ∨ H - 1 < γ j)
  let F (t : ℝ) := ∫ x in Iic t, CutDensity.countDensity C H x
  have ha : 0 < a := meanScale_pos hH
  have hH0 := zero_lt_one.trans hH
  have hD : ∀ t, |PrefixDiscrepancy.prefixCount s γ t - F t| ≤ D :=
    CutDensity.uniform_cumulative_bound S (zero_lt_one.trans_le hC) hcount H hHC
  have hsH (j) (hj : j ∈ s) : γ j ≤ H := by
    have hj' := (Finset.mem_sigma.mp hj).1
    simpa only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hj'
  have hb_eq : b =
      (s.filter fun j => 0 < γ j ∧ γ j ≤ 1) ∪ (s.filter fun j => H - 1 < γ j ∧ γ j ≤ H) := by
    ext j
    simp only [b, Finset.mem_union, mem_filter]
    constructor
    · rintro ⟨hj, hj'⟩
      rcases hj' with hj' | hj'
      · exact Or.inl ⟨hj, S.gamma_pos _, hj'⟩
      · exact Or.inr ⟨hj, hj', hsH j hj⟩
    · rintro (⟨hj, _, hj'⟩ | ⟨hj, hj', _⟩)
      · exact ⟨hj, Or.inl hj'⟩
      · exact ⟨hj, Or.inr hj'⟩
  have hb_count : (b.card : ℝ) ≤ 2 * a + 4 * D := by
    have hleft := finite_interval_count s γ F a D 0 1 zero_le_one
      (CutDensity.cumulative_lip hC hH 0 1 zero_le_one) hD
    have hH' : H - 1 ≤ H := by linarith
    have hright := finite_interval_count s γ F a D (H - 1) H hH'
      (CutDensity.cumulative_lip hC hH (H - 1) H hH') hD
    rw [hb_eq]
    refine (show (_ : ℝ) ≤ (s.filter fun j => 0 < γ j ∧ γ j ≤ 1).card +
      (s.filter fun j => H - 1 < γ j ∧ γ j ≤ H).card from by
        exact_mod_cast Finset.card_union_le _ _).trans ?_
    linarith
  have h := SpatialTail.spatial_tail_le s b (filter_subset _ _) γ g g.integrable a H a ha
    (fun j hj hnot => by
      have he : ¬(γ j ≤ 1 ∨ H - 1 < γ j) :=
        fun hb => hnot (mem_filter.mpr ⟨hj, hb⟩)
      exact ⟨le_mul_of_one_le_right ha.le (le_of_not_ge fun h => he (Or.inl h)),
        le_mul_of_one_le_right ha.le (by linarith [le_of_not_gt fun h => he (Or.inr h)])⟩)
  have habs : 0 ≤ ∫ u : ℝ, |g u| := integral_nonneg (fun _ => abs_nonneg _)
  have hcap := h.trans (mul_le_mul_of_nonneg_left
    (add_le_add_left (mul_le_mul_of_nonneg_right hb_count habs) _) (inv_nonneg.mpr ha.le))
  rw [copies_card] at hcap
  refine (div_le_div_of_nonneg_right hcap hH0.le).trans_eq ?_
  change (a⁻¹ * ((2 * a + 4 * D) * _ + _)) / H =
    ((2 + 4 * D / a) / H) * _ + ((S.N H : ℝ) / (H * a)) *
      (∫ u in {u : ℝ | a ≤ |u|}, |g u|)
  field_simp [ha.ne', hH0.ne']

private lemma smoothCount_integrable (S : Spectrum) (g : 𝓢(ℝ, ℝ)) {H : ℝ} (hH : 1 < H) :
    Integrable (smoothCount S g H) := by
  unfold smoothCount
  exact integrable_finsetSum _ fun j _ =>
    ((g.integrable.comp_mul_left' (meanScale_pos hH).ne').comp_sub_right _)

private lemma smoothCount_square_integrable (S : Spectrum) (g : 𝓢(ℝ, ℝ)) {H : ℝ} (hH : 1 < H) :
    Integrable (fun x => smoothCount S g H x ^ 2) := by
  rw [show (fun x => smoothCount S g H x ^ 2) = fun x =>
    smoothCount S g H x * smoothCount S g H x from funext fun x => pow_two _]
  have hi := smoothCount_integrable S g hH
  refine hi.mul_bdd (c := ((CutDensity.copies (S.cut H) S.mult).card : ℝ) *
    (SchwartzMap.seminorm ℝ 0 0) g) hi.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  unfold smoothCount
  calc
    _ ≤ ∑ j ∈ CutDensity.copies (S.cut H) S.mult,
      ‖g (meanScale H * (x - S.gamma j.1))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ CutDensity.copies (S.cut H) S.mult, (SchwartzMap.seminorm ℝ 0 0) g :=
      sum_le_sum fun _ _ => SchwartzMap.norm_le_seminorm ℝ g _
    _ = _ := by rw [sum_const, nsmul_eq_mul]

private lemma tail_integral_limit (g : 𝓢(ℝ, ℝ)) :
    Tendsto (fun H : ℝ => ∫ y in {u : ℝ | meanScale H ≤ |u|}, |g y|) atTop (𝓝 0) := by
  let T (H : ℝ) : Set ℝ := {u | meanScale H ≤ |u|}
  have hT (H : ℝ) : MeasurableSet (T H) := measurableSet_le measurable_const continuous_abs.measurable
  have h : Tendsto (fun H => ∫ y, (T H).indicator (fun y => |g y|) y) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence (fun y => |g y|)
        (F := fun H => (T H).indicator (fun y => |g y|)) (f := fun _ => 0)
        (Eventually.of_forall fun H => (g.integrable.abs.indicator (hT H)).aestronglyMeasurable)
        (Eventually.of_forall fun H => ae_of_all _ fun y => by
          by_cases hy : y ∈ T H
          · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_abs]
          · rw [indicator_of_notMem hy, norm_zero]; exact abs_nonneg _)
        g.integrable.abs (ae_of_all _ fun y => by
          apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
          filter_upwards [meanScale_tendsto.eventually_gt_atTop |y|] with H hH
          have hyn : y ∉ T H := fun yh => hH.not_ge yh
          exact (indicator_of_notMem hyn (fun y : ℝ => |g y|)).symm))
  exact h.congr (fun H => integral_indicator (hT H))

private lemma smooth_outer_norm_limit (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E : ℝ)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    Tendsto (fun H : ℝ => (∫ x in (Icc 0 H)ᶜ, |smoothCount S g H x|) / H) atTop (𝓝 0) := by
  let D := max (S.N (2 * Real.pi) : ℝ) (E + |CutDensity.countMain (2 * Real.pi) (2 * Real.pi)|)
  have hl : Tendsto (fun H : ℝ => (2 + 4 * D / meanScale H) / H) atTop (𝓝 0) :=
    (((tendsto_const_nhds (x := 4 * D)).div_atTop meanScale_tendsto).const_add 2).div_atTop tendsto_id
  have h := (hl.mul_const (∫ u : ℝ, |g u|)).add
    ((normalized_count_tends_one S E hcount).mul (tail_integral_limit g))
  simp only [zero_mul, mul_zero, add_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [spatial_cap S g E hcount, eventually_gt_atTop (1 : ℝ)] with H hcap hH
  rwa [Real.norm_of_nonneg (div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) (by linarith))]

private lemma smooth_outer_square_limit (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E : ℝ)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    Tendsto (fun H : ℝ => (∫ x in (Icc 0 H)ᶜ, smoothCount S g H x ^ 2) / H) atTop (𝓝 0) := by
  obtain ⟨K, hK, hK'⟩ := smoothed_count_bounded S g E hcount
  refine squeeze_zero_norm' ?_ (by
    simpa only [mul_zero] using (smooth_outer_norm_limit S g E hcount).const_mul K)
  filter_upwards [hK', eventually_gt_atTop (1 : ℝ)] with H hKH hH
  have hH0 := zero_lt_one.trans hH
  have hi := (smoothCount_square_integrable S g hH).integrableOn (s := (Icc 0 H)ᶜ)
  have hs := (smoothCount_integrable S g hH).abs.integrableOn (s := (Icc 0 H)ᶜ)
  rw [Real.norm_of_nonneg (div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) hH0.le),
    ← mul_div_assoc, ← integral_const_mul]
  apply div_le_div_of_nonneg_right _ hH0.le
  refine integral_mono hi (hs.const_mul _) fun x => ?_
  rw [← sq_abs, pow_two]
  exact mul_le_mul_of_nonneg_right (hKH x) (abs_nonneg _)

private lemma smooth_outer_integral_limit (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E : ℝ)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    Tendsto (fun H : ℝ => (∫ x in (Icc 0 H)ᶜ, smoothCount S g H x) / H) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (smooth_outer_norm_limit S g E hcount)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with H hH
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (zero_lt_one.trans hH)]
  exact div_le_div_of_nonneg_right (abs_integral_le_integral_abs) (zero_lt_one.trans hH).le

private lemma rescale_interval {H : ℝ} (hH : 0 < H) (f : ℝ → ℝ) :
    (∫ v in Ioo (0 : ℝ) 1, f (H * v)) = (∫ x in Icc 0 H, f x) / H := by
  change (∫ v in Ioo (0 : ℝ) 1, f (H • v)) = _
  rw [Measure.setIntegral_comp_smul_of_pos _ _ _ hH,
    LinearOrderedField.smul_Ioo hH, mul_zero, mul_one, Module.finrank_self, pow_one, smul_eq_mul,
    integral_Icc_eq_integral_Ioo, div_eq_mul_inv, mul_comm]

private lemma normalized_smoothed_mean_limit (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E : ℝ)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    Tendsto (fun H : ℝ => ∫ v in Ioo (0 : ℝ) 1, smoothCount S g H (H * v)) atTop
      (𝓝 (∫ x : ℝ, g x)) := by
  have h := ((normalized_count_tends_one S E hcount).mul_const (∫ x : ℝ, g x)).sub
    (smooth_outer_integral_limit S g E hcount)
  simp only [one_mul, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with H hH
  have hH0 := zero_lt_one.trans hH
  rw [rescale_interval hH0]
  have hi := smoothCount_integrable S g hH
  have he (c : ℝ) : (∫ y : ℝ, g (meanScale H * (y - c))) =
       (meanScale H)⁻¹ * (∫ y : ℝ, g y) :=
    SpatialTail.integrate_scaled_shift g _ c (meanScale_pos hH)
  have hm : (∫ y : ℝ, smoothCount S g H y) =
      (S.N H : ℝ) * ((meanScale H)⁻¹ * (∫ y : ℝ, g y)) := by
    unfold smoothCount
    rw [integral_finsetSum _ (fun j _ => (g.integrable.comp_mul_left'
      (meanScale_pos hH).ne').comp_sub_right _)]
    simp_rw [he, sum_const, nsmul_eq_mul, copies_card]
  rw [← add_sub_cancel_right (∫ x in Icc 0 H, smoothCount S g H x)
     (∫ x in (Icc 0 H)ᶜ, smoothCount S g H x), integral_add_compl measurableSet_Icc hi,
    sub_div, hm]
  ring

private lemma normalized_smoothed_square_limit (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E : ℝ)
    (hg : ∀ u, 1 < |u| → 𝓕 ((fun x => (g x : ℂ))) u = 0)
    (hS : UnitBandTestLimit S)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    Tendsto (fun H : ℝ => ∫ v in Ioo (0 : ℝ) 1, smoothCount S g H (H * v) ^ 2) atTop
      (𝓝 ((∫ x : ℝ, g x) ^ 2 + ∫ u : ℝ, |u| * spectralTest g u)) := by
  have h := (spectral_unweighted_limit_of_test_limit S g E hg hS hcount).sub
    (smooth_outer_square_limit S g E hcount)
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with H hH
  have hH0 := zero_lt_one.trans hH
  have ha := meanScale_pos hH
  have hs := Square.smoothed_count_square (CutDensity.copies (S.cut H) S.mult)
    (fun j => S.gamma j.1) g g.integrable _ (SchwartzMap.norm_le_seminorm ℝ g) (meanScale H) ha
  change meanScale H * (∫ y, smoothCount S g H y ^ 2) = unweightedAuto S g H at hs
  rw [rescale_interval hH0 (fun y => smoothCount S g H y ^ 2), ← hs]
  have hi := smoothCount_square_integrable S g hH
  conv_rhs =>
    rw [show (∫ x in Icc 0 H, smoothCount S g H x ^ 2) =
      (∫ x, smoothCount S g H x ^ 2) - ∫ x in (Icc 0 H)ᶜ, smoothCount S g H x ^ 2
      from eq_sub_of_add_eq (integral_add_compl measurableSet_Icc hi)]
  field_simp [hH0.ne', ha.ne']

private lemma normalized_centered_variance_limit (S : Spectrum) (g : 𝓢(ℝ, ℝ)) (E : ℝ)
    (hg : ∀ u, 1 < |u| → 𝓕 ((fun x => (g x : ℂ))) u = 0)
    (hS : UnitBandTestLimit S)
    (hcount : ∀ t, 2 * Real.pi ≤ t →
      |(S.N t : ℝ) - CutDensity.countMain (2 * Real.pi) t| ≤ E) :
    Tendsto (fun H : ℝ => ∫ v in Ioo (0 : ℝ) 1,
      (smoothCount S g H (H * v) - ∫ x : ℝ, g x) ^ 2) atTop
        (𝓝 (∫ u : ℝ, |u| * spectralTest g u)) := by
  let b := ∫ x : ℝ, g x
  let C (H v : ℝ) := smoothCount S g H (H * v)
  have ha := normalized_smoothed_square_limit S g E hg hS hcount
  have hm := normalized_smoothed_mean_limit S g E hcount
  have h := (ha.sub (hm.const_mul (2 * b))).add_const (b ^ 2)
  have he : (b ^ 2 + ∫ u : ℝ, |u| * spectralTest g u) - (2 * b) * b + b ^ 2 =
      ∫ u : ℝ, |u| * spectralTest g u := by ring
  rw [he] at h
  refine h.congr (fun H => ?_)
  have hC : Continuous (C H) := by
    unfold C smoothCount
    fun_prop
  have hi : IntegrableOn (C H) (Ioo 0 1) := hC.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hi₂ : IntegrableOn (fun v => C H v ^ 2) (Ioo 0 1) :=
    (hC.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hi₀ : IntegrableOn (fun _ : ℝ => b ^ 2) (Ioo 0 1) :=
    integrableOn_const (hs := measure_Ioo_lt_top.ne)
  change _ = ∫ v in Ioo (0 : ℝ) 1, (C H v - b) ^ 2
  have hp (v : ℝ) : (C H v - b) ^ 2 = C H v ^ 2 - (2 * b) * C H v + b ^ 2 := by ring
  simp_rw [hp]
  have hmul := hi.const_mul (2 * b)
  have hadd := integral_add (hi₂.sub hmul) hi₀
  have hsub := integral_sub hi₂ hmul
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul]
  change _ = (∫ v in Ioo (0 : ℝ) 1, C H v ^ 2) - (2 * b) *
    (∫ v in Ioo (0 : ℝ) 1, C H v) + ∫ _v in Ioo (0 : ℝ) 1, b ^ 2
  rw [setIntegral_const, measureReal_def, Real.volume_Ioo]
  simp [C]

/-- A band-limited test limit forces unbounded two-term count discrepancy on every real tail. -/
private lemma test_limit_forces_unbounded_count_discrepancy (S : Spectrum)
    (hS : UnitBandTestLimit S) (D H₀ : ℝ) :
    ∃ H : ℝ, H₀ ≤ H ∧
      D < |(S.N H : ℝ) - H / (2 * Real.pi) * (Real.log (H / (2 * Real.pi)) - 1)| := by
  by_contra! h
  have hb : ∀ᶠ H : ℝ in atTop,
      |(S.N H : ℝ) - CutDensity.countMain (2 * Real.pi) H| ≤ D := by
    filter_upwards [eventually_ge_atTop H₀] with H hH
    convert h H hH using 2
    unfold CutDensity.countMain
    ring
  obtain ⟨E, hE⟩ := CutDensity.eventual_count_bound S (show 0 < 2 * Real.pi by positivity) hb
  let U := max (S.N (2 * Real.pi) : ℝ) (E + |CutDensity.countMain (2 * Real.pi) (2 * Real.pi)|)
  obtain ⟨K, _, hwindows⟩ := BandLimitedWindowVariance.exists_windows_with_unbounded_spectral_variance
  have hU : 0 ≤ U := (Nat.cast_nonneg _).trans (le_max_left _ _)
  have hden : 0 < 4 * Real.pi ^ 2 := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((U * K) ^ 2 * (4 * Real.pi ^ 2))
  obtain ⟨g, hg, hg', hlarge⟩ := hwindows n
  have hlarge' : (U * K) ^ 2 < ∫ u : ℝ, |u| * spectralTest g u := by
    have h := ((lt_div_iff₀ hden).2 hn).trans_le hlarge
    simpa only [spectralTest_eq] using h
  have hlim := normalized_centered_variance_limit S g E hg hS hE
  have hupper := normalized_variance_upper S g E _ hE hlim
  have hp : (U * ∫ u : ℝ, ‖deriv g u‖) ^ 2 ≤ (U * K) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hU (integral_nonneg (fun _ => norm_nonneg _)))
      (mul_le_mul_of_nonneg_left hg' hU) 2
  exact (hupper.trans hp).not_gt hlarge'

/-- The unit-band profile forces unbounded two-term count discrepancy on every real tail. -/
theorem unit_band_profile_forces_unbounded_count_discrepancy (S : Spectrum)
    (hS : UnitBandProfile S) (D H₀ : ℝ) :
    ∃ H : ℝ, H₀ ≤ H ∧
      D < |(S.N H : ℝ) - H / (2 * Real.pi) * (Real.log (H / (2 * Real.pi)) - 1)| :=
  test_limit_forces_unbounded_count_discrepancy S (unitBandTestLimit_of_uniform S hS) D H₀

/-- A bounded frequency-dependent correction to the exponential peak still forces unbounded
two-term count discrepancy on every real tail. -/
theorem concentrated_unit_band_profile_forces_unbounded_count_discrepancy
    (S : Spectrum) (hS : ConcentratedUnitBandProfile S) (D H₀ : ℝ) :
    ∃ H : ℝ, H₀ ≤ H ∧
      D < |(S.N H : ℝ) - H / (2 * Real.pi) * (Real.log (H / (2 * Real.pi)) - 1)| :=
  test_limit_forces_unbounded_count_discrepancy S (unitBandTestLimit_of_concentrated S hS) D H₀

end
end D5.S3.Analytic.Oscillation.MontgomeryCountDiscrepancy
