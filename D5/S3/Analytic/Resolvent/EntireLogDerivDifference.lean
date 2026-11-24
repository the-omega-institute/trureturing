/- GID: D5/S3/Analytic/Resolvent/EntireLogDerivDifference
   generality: G
   mirror-B: D5/B/S3/Analytic/Resolvent/EntireLogDerivDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identify two-point logarithmic derivative differences with the zero divisor. -/

import D5.S3.Weil.ZetaExplicit.Landau
import D5.S3.Weil.ZetaTail.PowerCountTail
import D5.S3.Analytic.Dilation.ScalarUnitDressing
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Schwarz

/-!
The zero divisor is first shown to have a summable inverse-square weight.
Finite disk factorizations and a centered Schwarz estimate then identify the
absolutely convergent two-point sum with the logarithmic derivative difference.
-/

noncomputable section
namespace D5.S3.Analytic.Resolvent.EntireLogDerivDifference
open Complex Filter Set Topology
open Zeta23.WeilEF
open D5.S3.Analytic.Dilation.ScalarUnitDressing

/-- Translation and normalization preserve power growth with an explicit nonnegative constant. -/
theorem normalized_growth {F : ℂ → ℂ} {a : ℂ} {α C : ℝ}
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α)) :
    0 ≤ (max C 0) * (1 + ‖a‖) ^ (max α 0) + max (-Real.log ‖F a‖) 0 ∧
      ∀ z : ℂ, ‖(F a)⁻¹ * F (a + z)‖ ≤
        Real.exp (((max C 0) * (1 + ‖a‖) ^ (max α 0) + max (-Real.log ‖F a‖) 0) *
          (1 + ‖z‖) ^ (max α 0)) := by
  let β := max α 0
  let K := (max C 0) * (1 + ‖a‖) ^ β
  let D := K + max (-Real.log ‖F a‖) 0
  change 0 ≤ D ∧ ∀ z : ℂ,
    ‖(F a)⁻¹ * F (a + z)‖ ≤ Real.exp (D * (1 + ‖z‖) ^ β)
  have hβ : 0 ≤ β := le_max_right _ _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨by dsimp [D]; positivity, fun z => ?_⟩
  by_cases ha : F a = 0
  · simpa only [ha, inv_zero, zero_mul, norm_zero] using
      (Real.exp_pos (D * (1 + ‖z‖) ^ β)).le
  have hr : 1 ≤ (1 + ‖z‖) ^ β :=
    Real.one_le_rpow (by linarith [norm_nonneg z]) hβ
  have hp : C * (1 + ‖a + z‖) ^ α ≤ K * (1 + ‖z‖) ^ β := by
    apply (mul_le_mul_of_nonneg_right (le_max_left C 0)
      (Real.rpow_nonneg (by positivity) _)).trans
    apply (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg (a + z)])
        (le_max_left α 0)) (le_max_right C 0)).trans
    dsimp [K]
    rw [mul_assoc, ← Real.mul_rpow (by positivity) (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (le_max_right C 0)
    apply Real.rpow_le_rpow (by positivity) _ hβ
    nlinarith [norm_add_le a z, mul_nonneg (norm_nonneg a) (norm_nonneg z)]
  have hn : 0 < ‖F a‖ := norm_pos_iff.mpr ha
  calc
    ‖(F a)⁻¹ * F (a + z)‖ = ‖F (a + z)‖ / ‖F a‖ := by
      rw [norm_mul, norm_inv]; ring
    _ ≤ Real.exp (C * (1 + ‖a + z‖) ^ α) / ‖F a‖ :=
      div_le_div_of_nonneg_right (hg _) hn.le
    _ = Real.exp (C * (1 + ‖a + z‖) ^ α - Real.log ‖F a‖) := by
      rw [Real.exp_sub, Real.exp_log hn]
    _ ≤ Real.exp (D * (1 + ‖z‖) ^ β) := by
      apply Real.exp_le_exp.mpr
      have habs := le_max_left (-Real.log ‖F a‖) 0
      have hm := mul_le_mul_of_nonneg_left hr
        (le_max_right (-Real.log ‖F a‖) 0)
      dsimp [D]
      nlinarith

private theorem normalized_count {F : ℂ → ℂ} {β D r : ℝ}
    (hF : Differentiable ℂ F) (hF0 : F 0 = 1) (hβ : 0 ≤ β)
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (D * (1 + ‖z‖) ^ β)) (hr : 1 ≤ r)
    (t : Finset ℂ) (ht : ∀ ρ ∈ t, ‖ρ‖ ≤ r ∧ F ρ = 0) :
    ∑ ρ ∈ t, (analyticOrderNatAt F ρ : ℝ) ≤
      (1 / Real.log (3 / 2) * D * (5 / 2 : ℝ) ^ β) * r ^ β := by
  classical
  have hD : 0 ≤ D := Real.one_le_exp_iff.mp (by simpa [hF0] using hg 0)
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hc : (2 * r : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * r ≠ 0)
  let G : ℂ → ℂ := fun w => F ((2 * r : ℂ) * w)
  have hGa : AnalyticOnNhd ℂ G (Metric.closedBall 0 1) :=
    fun w _ => (hF.analyticAt _).comp (by fun_prop)
  have hG0 : G 0 = 1 := by simpa [G] using hF0
  have hfin := Zeta23.WeilEF.finite_SetOfZeros hGa (by rw [hG0]; exact one_ne_zero)
  have hB (w : ℂ) (hw : ‖w‖ ≤ 3 / 4) :
      ‖G w‖ ≤ Real.exp (D * ((5 / 2) * r) ^ β) := by
    apply (hg _).trans
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hD
    apply Real.rpow_le_rpow (by positivity) _ hβ
    have hh : ‖(2 * r : ℂ) * w‖ ≤ (3 / 2) * r := by
      rw [norm_mul, show (2 * r : ℂ) = ((2 * r : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_of_nonneg (by positivity)]
      nlinarith [norm_nonneg w]
    linarith
  have hj := ZerosBound (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 / 2 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) hGa hG0 hfin hB
  let T := (finiteSetOfZeros_mono (by norm_num : (1 / 2 : ℝ) < 1) hfin).toFinset
  have horder (ρ : ℂ) : analyticOrderNatAt G (ρ / (2 * r : ℂ)) =
      analyticOrderNatAt F ρ := by
    have ho := analyticOrderAt_comp_of_deriv_ne_zero (f := F)
      (g := fun w : ℂ => (2 * r : ℂ) * w) (z₀ := ρ / (2 * r : ℂ))
      (by fun_prop) (by simpa using hc)
    simpa [G, analyticOrderNatAt, Function.comp_def, mul_div_cancel₀ _ hc] using
      congrArg ENat.toNat ho
  have he : ∑ ρ ∈ t, (analyticOrderNatAt F ρ : ℝ) =
      ∑ w ∈ t.image (fun ρ => ρ / (2 * r : ℂ)), (analyticOrderNatAt G w : ℝ) := by
    rw [Finset.sum_image]
    · exact Finset.sum_congr rfl (fun ρ _ => by rw [horder])
    · intro ρ _ σ _ h
      exact (div_left_inj' hc).mp h
  have hsub : t.image (fun ρ => ρ / (2 * r : ℂ)) ⊆ T := by
    intro w hw
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · rw [norm_div,
        show (2 * r : ℂ) = ((2 * r : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity : 0 < 2 * r)]
      linarith [(ht ρ hρ).1]
    · simpa [G, mul_div_cancel₀ _ hc] using (ht ρ hρ).2
  calc
    _ = ∑ w ∈ t.image (fun ρ => ρ / (2 * r : ℂ)),
        (analyticOrderNatAt G w : ℝ) := he
    _ ≤ ∑ w ∈ T, (analyticOrderNatAt G w : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ (1 / Real.log (3 / 2) * D * (5 / 2 : ℝ) ^ β) * r ^ β := by
      have hh : ((∑ w ∈ T, analyticOrderNatAt G w : ℕ) : ℝ) ≤
          1 / Real.log ((3 / 4 : ℝ) / (1 / 2)) *
            Real.log (Real.exp (D * ((5 / 2) * r) ^ β)) := hj
      rw [Real.log_exp, Real.mul_rpow (by norm_num) hr0.le] at hh
      norm_num at hh
      simpa only [Nat.cast_sum, mul_assoc, one_div] using hh

private theorem normalized_summable {F : ℂ → ℂ} {β D : ℝ}
    (hF : Differentiable ℂ F) (hF0 : F 0 = 1) (hβ : 0 ≤ β) (hβ2 : β < 2)
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (D * (1 + ‖z‖) ^ β)) :
    Summable (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1‖ ^ 2)) ∧
      (∑' ρ : {z : ℂ // F z = 0},
        (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1‖ ^ 2)) ≤
        2 * D * (5 / 2 : ℝ) ^ β / ((2 - β) * Real.log (3 / 2)) := by
  classical
  have hD : 0 ≤ D := Real.one_le_exp_iff.mp (by simpa [hF0] using hg 0)
  let K : ℝ := D * (5 / 2 : ℝ) ^ β / Real.log (3 / 2)
  let g : {z : ℂ // F z = 0} → ℝ := fun ρ => Real.sqrt (1 + ‖ρ.1‖ ^ 2)
  have hg1 (ρ : {z : ℂ // F z = 0}) : 1 ≤ g ρ := by
    dsimp [g]
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hcount (u : ℝ) (hu : 1 ≤ u) (s : Finset {z : ℂ // F z = 0})
      (hs : ∀ ρ ∈ s, g ρ < u) :
      ∑ ρ ∈ s, (analyticOrderNatAt F ρ.1 : ℝ) ≤ K * u ^ β := by
    have hh := normalized_count hF hF0 hβ hg hu (s.image Subtype.val) ?_
    · rw [Finset.sum_image] at hh
      · simpa [K, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
      · exact fun _ _ _ _ h => Subtype.ext h
    · intro z hz
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
      refine ⟨?_, ρ.2⟩
      have hn : ‖ρ.1‖ ≤ g ρ := by
        dsimp [g]
        exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by nlinarith)
      exact hn.trans (hs ρ hρ).le
  have hh := D5.S3.Weil.ZetaTail.PowerCountTail.inverse_power_tail_of_raw_count
    g (fun ρ => (analyticOrderNatAt F ρ.1 : ℝ))
    (Y := 1) (C := K) (p := 2) (a := β) (by norm_num)
    (by dsimp [K]; exact div_nonneg (by positivity) (Real.log_pos (by norm_num)).le)
    (by norm_num) hβ2 (fun _ => by positivity) hcount
  have he (ρ : {z : ℂ // F z = 0}) :
      (if 1 ≤ g ρ then (analyticOrderNatAt F ρ.1 : ℝ) * (g ρ) ^ (-(2 : ℝ)) else 0) =
        (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1‖ ^ 2) := by
    rw [ite_eq_left (hg1 ρ), Real.rpow_neg (by linarith [hg1 ρ]), Real.rpow_two]
    dsimp [g]
    rw [Real.sq_sqrt (by positivity)]
    rfl
  refine ⟨hh.1.congr he, ?_⟩
  rw [← tsum_congr he]
  exact hh.2.trans_eq (by
    simp only [Real.one_rpow, mul_one]
    dsimp [K]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring)

private theorem entire_zero_summable_at_base {F : ℂ → ℂ} {a : ℂ} {α C : ℝ}
    (hF : Differentiable ℂ F) (ha : F a ≠ 0) (hα : α < 2)
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α)) :
    Summable (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2)) ∧
      (∑' ρ : {z : ℂ // F z = 0},
        (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2)) ≤
        2 * ((max C 0) * (1 + ‖a‖) ^ (max α 0) + max (-Real.log ‖F a‖) 0) *
          (5 / 2 : ℝ) ^ (max α 0) / ((2 - max α 0) * Real.log (3 / 2)) := by
  have hG := (normalized_growth (a := a) hg).2
  let G : ℂ → ℂ := fun w => (F a)⁻¹ * F (a + w)
  have hGa : Differentiable ℂ G := by dsimp [G]; fun_prop
  have hG0 : G 0 = 1 := by simp [G, ha]
  have hcomp (w : ℂ) : analyticOrderAt (fun z => F (a + z)) w =
      analyticOrderAt F (a + w) := by
    have hh := analyticOrderAt_comp_of_deriv_ne_zero (f := F)
      (g := fun z : ℂ => a + z) (z₀ := w) (by fun_prop) (by simp)
    simpa only [Function.comp_def] using hh
  have horder (w : ℂ) : analyticOrderNatAt G w = analyticOrderNatAt F (a + w) := by
    have hs := (nonzero_scalar_dressing_preserves_zero_and_analytic_order
      (f := fun z : ℂ => F (a + z)) (g := fun _ : ℂ => (F a)⁻¹) (s := w)
      ((hF.analyticAt _).comp (by fun_prop)) analyticAt_const (inv_ne_zero ha)).2
    exact congrArg ENat.toNat (hs.trans (hcomp w))
  let e : {z : ℂ // F z = 0} ≃ {z : ℂ // G z = 0} :=
    { toFun := fun ρ => ⟨ρ.1 - a, by
        have he : a + (ρ.1 - a) = ρ.1 := by ring
        simp [G, he, ρ.2]⟩
      invFun := fun ρ => ⟨a + ρ.1, by
        have hz := ρ.2
        change (F a)⁻¹ * F (a + ρ.1) = 0 at hz
        exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero ha)⟩
      left_inv := by intro ρ; apply Subtype.ext; dsimp; ring
      right_inv := by intro ρ; apply Subtype.ext; dsimp; ring }
  have hh := normalized_summable hGa hG0 (le_max_right α 0)
    (max_lt_iff.mpr ⟨hα, by norm_num⟩) hG
  have he (ρ : {z : ℂ // F z = 0}) :
      (analyticOrderNatAt G (e ρ).1 : ℝ) / (1 + ‖(e ρ).1‖ ^ 2) =
        (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2) := by
    dsimp [e]
    rw [horder, show a + (ρ.1 - a) = ρ.1 by ring]
  refine ⟨?_, ?_⟩
  · exact (e.summable_iff.mpr hh.1).congr he
  · rw [← tsum_congr he]
    exact (e.tsum_eq (fun ρ =>
      (analyticOrderNatAt G ρ.1 : ℝ) / (1 + ‖ρ.1‖ ^ 2))).le.trans hh.2

/-- Inverse-square zero summability, explicit growth bounds, and comparison of all centers. -/
theorem entire_zero_summable {F : ℂ → ℂ} {a : ℂ} {α C : ℝ}
    (hF : Differentiable ℂ F) (hα : α < 2)
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α)) :
    Summable (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2)) ∧
    ∀ b : ℂ,
      (∑' ρ : {z : ℂ // F z = 0},
        (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2)) ≤
        (1 + ‖a - b‖ + ‖a - b‖ ^ 2) * (∑' ρ : {z : ℂ // F z = 0},
          (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - b‖ ^ 2)) ∧
      (F b ≠ 0 →
        let H := 2 * ((max C 0) * (1 + ‖b‖) ^ (max α 0) + max (-Real.log ‖F b‖) 0) *
          (5 / 2 : ℝ) ^ (max α 0) / ((2 - max α 0) * Real.log (3 / 2))
        (∑' ρ : {z : ℂ // F z = 0},
          (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - b‖ ^ 2)) ≤ H ∧
        (∑' ρ : {z : ℂ // F z = 0},
          (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2)) ≤
          (1 + ‖a - b‖ + ‖a - b‖ ^ 2) * H) := by
  by_cases hzero : F = 0
  · subst F
    simp [analyticOrderNatAt]
  have hnonzero : ∃ b : ℂ, F b ≠ 0 := by
    by_contra! h
    exact hzero (funext h)
  obtain ⟨b₀, hb₀⟩ := hnonzero
  have hpoint (a b : ℂ) (ρ : {z : ℂ // F z = 0}) :
      (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2) ≤
        (1 + ‖a - b‖ + ‖a - b‖ ^ 2) *
          ((analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - b‖ ^ 2)) := by
    let K : ℝ := (1 + ‖a - b‖ + ‖a - b‖ ^ 2)
    have hn : ‖ρ.1 - b‖ ≤ ‖ρ.1 - a‖ + ‖a - b‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (ρ.1 - a) (a - b)
    have hsq := pow_le_pow_left₀ (norm_nonneg (ρ.1 - b)) hn 2
    have hd : 1 + ‖ρ.1 - b‖ ^ 2 ≤ K * (1 + ‖ρ.1 - a‖ ^ 2) := by
      dsimp [K]
      nlinarith [mul_nonneg (norm_nonneg (a - b)) (sq_nonneg (‖ρ.1 - a‖ - 1)),
        mul_nonneg (sq_nonneg ‖a - b‖) (sq_nonneg ‖ρ.1 - a‖)]
    have hi : 1 / (1 + ‖ρ.1 - a‖ ^ 2) ≤ K / (1 + ‖ρ.1 - b‖ ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      simpa only [one_mul] using hd
    calc
      _ = (analyticOrderNatAt F ρ.1 : ℝ) * (1 / (1 + ‖ρ.1 - a‖ ^ 2)) := by ring
      _ ≤ (analyticOrderNatAt F ρ.1 : ℝ) * (K / (1 + ‖ρ.1 - b‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by dsimp [K]; ring
  have hsall (a : ℂ) : Summable (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2)) := by
    apply ((entire_zero_summable_at_base hF hb₀ hα hg).1.mul_left
      ((1 + ‖a - b₀‖ + ‖a - b₀‖ ^ 2))).of_norm_bounded
    intro ρ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpoint a b₀ ρ
  refine ⟨hsall a, fun b => ?_⟩
  have hcmp := (hsall a).tsum_le_tsum (hpoint a b)
    ((hsall b).mul_left ((1 + ‖a - b‖ + ‖a - b‖ ^ 2)))
  rw [tsum_mul_left] at hcmp
  refine ⟨hcmp, fun hb => ?_⟩
  have hbound := (entire_zero_summable_at_base hF hb hα hg).2
  exact ⟨hbound, hcmp.trans (mul_le_mul_of_nonneg_left hbound (by positivity))⟩


/-- Removing the zeros leaves a logarithmic derivative whose centered value
has a linear Schwarz bound. -/
theorem centered_cf {f : ℂ → ℂ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) (hf0 : f 0 = 1)
    {B : ℝ} (hB : 2 ≤ B) (hfB : ∀ w, ‖w‖ ≤ 24 / 25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83 / 100) :
    ‖logDeriv (Cf (22 / 25) f) z - logDeriv (Cf (22 / 25) f) 0‖ ≤
      ((44795000 * Real.log B + ‖logDeriv (Cf (22 / 25) f) 0‖) /
        (83 / 100 : ℝ)) * ‖z‖ := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hfin := finite_SetOfZeros hfa hf0'
  have hc := CfAnalytic (by norm_num : (22 / 25 : ℝ) < 9 / 10) (by norm_num) hfa hf0'
  have hd : DifferentiableOn ℂ (logDeriv (Cf (22 / 25) f)) (Metric.ball 0 (83 / 100)) := by
    intro w hw
    have hw' : ‖w‖ < 83 / 100 := by simpa using hw
    have ha := hc w (by simpa using (show ‖w‖ ≤ 9 / 10 by linarith))
    exact (ha.deriv.div ha (Cf_ne_zero hfa hf0' (by norm_num) hfin
      (by linarith))).differentiableAt.differentiableWithinAt
  have hb (w : ℂ) (hw : ‖w‖ ≤ 83 / 100) := norm_logDeriv_Cf_le hfa hf0 hfin hB hfB hw
  have hm : MapsTo (logDeriv (Cf (22 / 25) f)) (Metric.ball 0 (83 / 100))
      (Metric.closedBall (logDeriv (Cf (22 / 25) f) 0)
        (44795000 * Real.log B + ‖logDeriv (Cf (22 / 25) f) 0‖)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hw' : ‖w‖ ≤ 83 / 100 := le_of_lt (by simpa using hw)
    exact (norm_sub_le _ _).trans (add_le_add (hb w hw') le_rfl)
  rcases hz.lt_or_eq with hz | hz
  · simpa [dist_eq_norm] using Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm
      (show z ∈ Metric.ball 0 (83 / 100) by simpa using hz)
  · calc
      _ ≤ ‖logDeriv (Cf (22 / 25) f) z‖ + ‖logDeriv (Cf (22 / 25) f) 0‖ :=
        norm_sub_le _ _
      _ ≤ 44795000 * Real.log B + ‖logDeriv (Cf (22 / 25) f) 0‖ :=
        add_le_add (hb z hz.le) le_rfl
      _ = _ := by rw [hz]; ring


private theorem finite_zeros {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a : ℂ} (ha : F a ≠ 0) (r : ℝ) :
    {ρ : {z : ℂ // F z = 0} | ‖ρ.1 - a‖ ≤ r}.Finite := by
  have hFA : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hc := hFA.preimage_zero_mem_codiscrete ha
  have hc' := Filter.codiscreteWithin_mono
    (Set.subset_univ (Metric.closedBall a r)) hc
  have hf := (isCompact_closedBall a r).finite_sdiff_of_mem_codiscreteWithin hc'
  apply Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  apply hf.subset
  rintro z ⟨ρ, hρ, rfl⟩
  exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ,
    by simpa using ρ.2⟩

private def cutoff {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a : ℂ}
    (ha : F a ≠ 0) (R : ℝ) : Finset {z : ℂ // F z = 0} :=
  (finite_zeros hF ha ((22 / 25) * R)).toFinset

private theorem mem_cutoff {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a : ℂ}
    (ha : F a ≠ 0) (R : ℝ) (ρ : {z : ℂ // F z = 0}) :
    ρ ∈ cutoff hF ha R ↔ ‖ρ.1 - a‖ ≤ (22 / 25) * R := by
  classical
  simp [cutoff]

private theorem cutoff_tendsto {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a : ℂ}
    (ha : F a ≠ 0) : Tendsto (cutoff hF ha) atTop atTop := by
  classical
  rw [tendsto_atTop]
  intro t
  filter_upwards [eventually_ge_atTop ((25 / 22 : ℝ) * ∑ ρ ∈ t, ‖ρ.1 - a‖)] with R hR
  intro ρ hρ
  rw [mem_cutoff]
  have := Finset.single_le_sum (fun ρ _ => norm_nonneg (ρ.1 - a)) hρ
  nlinarith

private def scaled (F : ℂ → ℂ) (a : ℂ) (R : ℝ) (w : ℂ) :=
  (F a)⁻¹ * F (a + (R : ℂ) * w)

private theorem scaled_analytic {F : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall a R)) (hR : 0 ≤ R) :
    AnalyticOnNhd ℂ (scaled F a R) (Metric.closedBall 0 1) := by
  intro w hw
  have hw1 : ‖w‖ ≤ 1 := by simpa using hw
  have hp : a + (R : ℂ) * w ∈ Metric.closedBall a R := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_of_nonneg hR]
    nlinarith [norm_nonneg w]
  exact analyticAt_const.mul ((hF _ hp).comp
    (f := fun z : ℂ => a + (R : ℂ) * z) (by fun_prop))

private theorem scaled_zero {F : ℂ → ℂ} {a : ℂ} (ha : F a ≠ 0) (R : ℝ) :
    scaled F a R 0 = 1 := by simp [scaled, ha]

private theorem scaled_order {F : ℂ → ℂ}
    {a : ℂ} (ha : F a ≠ 0) {R : ℝ} (hR : R ≠ 0) (ρ : ℂ)
    (hF : AnalyticAt ℂ F ρ) :
    analyticOrderNatAt (scaled F a R) ((ρ - a) / (R : ℂ)) =
      analyticOrderNatAt F ρ := by
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  have hpoint : a + (R : ℂ) * ((ρ - a) / (R : ℂ)) = ρ := by
    rw [mul_div_cancel₀ _ hR']; ring
  have hg : AnalyticAt ℂ (fun w : ℂ => a + (R : ℂ) * w) ((ρ - a) / (R : ℂ)) :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hd : deriv (fun w : ℂ => a + (R : ℂ) * w) ((ρ - a) / (R : ℂ)) = R := by
    simp
  have hc := analyticOrderAt_comp_of_deriv_ne_zero (f := F) hg
    (by rw [hd]; exact hR')
  have hcomp : AnalyticAt ℂ (fun w : ℂ => F (a + (R : ℂ) * w))
      ((ρ - a) / (R : ℂ)) :=
    (show AnalyticAt ℂ F (a + (R : ℂ) * ((ρ - a) / (R : ℂ))) by
      simpa only [hpoint] using hF).comp (f := fun w : ℂ => a + (R : ℂ) * w) hg
  have hs := (nonzero_scalar_dressing_preserves_zero_and_analytic_order
    hcomp analyticAt_const (inv_ne_zero ha)).2
  unfold scaled analyticOrderNatAt
  rw [hs]
  change (analyticOrderAt (F ∘ (fun w : ℂ => a + (R : ℂ) * w)) _).toNat = _
  rw [hc, hpoint]

private theorem scaled_logDeriv {F : ℂ → ℂ}
    {a : ℂ} (ha : F a ≠ 0) (R : ℝ) (w : ℂ)
    (hF : DifferentiableAt ℂ F (a + (R : ℂ) * w)) :
    logDeriv (scaled F a R) w = (R : ℂ) * logDeriv F (a + (R : ℂ) * w) := by
  unfold scaled
  rw [logDeriv_const_mul _ _ (inv_ne_zero ha)]
  have hd := logDeriv_comp (f := F) (g := fun z : ℂ => a + (R : ℂ) * z)
    hF
    (show DifferentiableAt ℂ (fun z : ℂ => a + (R : ℂ) * z) w by fun_prop)
  simpa [Function.comp_def, mul_comm] using hd

private theorem finite_split {F : ℂ → ℂ} {a s : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall a R))
    (ha : F a ≠ 0) (hs : F s ≠ 0) (hR : 0 < R)
    (hsR : ‖(s - a) / (R : ℂ)‖ < 22 / 25)
    (t : Finset {z : ℂ // F z = 0})
    (ht : ∀ ρ : {z : ℂ // F z = 0}, ρ ∈ t ↔ ‖ρ.1 - a‖ ≤ (22 / 25) * R) :
    logDeriv F s - logDeriv F a =
      (∑ ρ ∈ t, (analyticOrderNatAt F ρ.1 : ℂ) *
        ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹)) +
      (logDeriv (Cf (22 / 25) (scaled F a R)) ((s - a) / (R : ℂ)) -
        logDeriv (Cf (22 / 25) (scaled F a R)) 0) / (R : ℂ) := by
  classical
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hpoint (z : ℂ) : a + (R : ℂ) * ((z - a) / (R : ℂ)) = z := by
    rw [mul_div_cancel₀ _ hR']; ring
  have hlocal (z : ℂ) (hz : ‖z - a‖ ≤ R) : AnalyticAt ℂ F z :=
    hF z (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
  have hsball : ‖s - a‖ ≤ R := by
    rw [norm_div, Complex.norm_of_nonneg hR.le, div_lt_iff₀ hR] at hsR
    linarith
  have hfA := scaled_analytic hF hR.le
  have hf0 : scaled F a R 0 ≠ 0 := by rw [scaled_zero ha]; exact one_ne_zero
  have hfin := finite_SetOfZeros hfA hf0
  let T := (finiteSetOfZeros_mono (by norm_num : (22 / 25 : ℝ) < 1) hfin).toFinset
  have he : (∑ ρ ∈ t, (analyticOrderNatAt F ρ.1 : ℂ) *
      ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹)) =
      ∑ z ∈ T, ((analyticOrderNatAt (scaled F a R) z : ℂ) /
        ((s - a) / (R : ℂ) - z) -
        (analyticOrderNatAt (scaled F a R) z : ℂ) / (0 - z)) / (R : ℂ) := by
    apply Finset.sum_bij (fun ρ _ => (ρ.1 - a) / (R : ℂ))
    · intro ρ hρ
      rw [Set.Finite.mem_toFinset]
      refine ⟨?_, ?_⟩
      · rw [norm_div, Complex.norm_of_nonneg hR.le, div_le_iff₀ hR]
        simpa [mul_comm] using (ht ρ).mp hρ
      · simp [scaled, hpoint, ρ.2]
    · intro ρ _ σ _ h
      apply Subtype.ext
      exact sub_left_injective (div_left_inj' hR' |>.mp h)
    · intro z hz
      have hp : z ∈ SetOfZeros (22 / 25) (scaled F a R) := by
        simpa only [T, Set.Finite.mem_toFinset] using hz
      have hx : F (a + (R : ℂ) * z) = 0 :=
        (mul_eq_zero.mp hp.2).resolve_left (inv_ne_zero ha)
      refine ⟨⟨a + (R : ℂ) * z, hx⟩, ?_, ?_⟩
      · rw [ht]
        simp only [add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hR.le]
        nlinarith [mul_le_mul_of_nonneg_left hp.1 hR.le]
      · dsimp; field_simp; ring
    · intro ρ hρ
      rw [scaled_order ha hR.ne' ρ (hlocal ρ.1 (by
        have := (ht ρ).mp hρ; linarith))]
      have hsa : s - ρ.1 ≠ 0 := by
        intro h; exact hs ((sub_eq_zero.mp h).symm ▸ ρ.2)
      have haa : a - ρ.1 ≠ 0 := by
        intro h; exact ha ((sub_eq_zero.mp h).symm ▸ ρ.2)
      have hd : (s - a) / (R : ℂ) - (ρ.1 - a) / (R : ℂ) ≠ 0 := by
        rw [← sub_div, sub_sub_sub_cancel_right]; exact div_ne_zero hsa hR'
      have hz : (ρ.1 - a) / (R : ℂ) ≠ 0 :=
        div_ne_zero (sub_ne_zero.mpr (sub_ne_zero.mp haa).symm) hR'
      field_simp [hR', hsa, haa, hd, hz]; ring
  have hs' : scaled F a R ((s - a) / (R : ℂ)) ≠ 0 := by
    simpa [scaled, hpoint] using mul_ne_zero (inv_ne_zero ha) hs
  have h1 := logDeriv_split hfA hf0 (by norm_num : (22 / 25 : ℝ) < 1)
    hfin hsR hs'
  have h0 := logDeriv_split hfA hf0 (by norm_num : (22 / 25 : ℝ) < 1)
    hfin (by norm_num : ‖(0 : ℂ)‖ < 22 / 25) hf0
  rw [scaled_logDeriv ha R _ (by
    rw [hpoint]; exact (hlocal s hsball).differentiableAt), hpoint] at h1
  rw [scaled_logDeriv ha R 0 (by
    simpa using (hlocal a (by simpa using hR.le)).differentiableAt),
    mul_zero, add_zero] at h0
  rw [he, ← Finset.sum_div, Finset.sum_sub_distrib]
  change _ = ((∑ z ∈ T, _) - (∑ z ∈ T, _)) / (R : ℂ) + _
  change (R : ℂ) * logDeriv F s = (∑ z ∈ T, _) + _ at h1
  change (R : ℂ) * logDeriv F a = (∑ z ∈ T, _) + _ at h0
  apply mul_right_cancel₀ hR'
  rw [add_mul, div_mul_cancel₀ _ hR', div_mul_cancel₀ _ hR']
  linear_combination h1 - h0


private theorem rational_tail (a s ρ : ℂ) (m : ℕ)
    (hr : max 1 (2 * ‖s - a‖) ≤ ‖ρ - a‖) :
    ‖(m : ℂ) * ((s - ρ)⁻¹ - (a - ρ)⁻¹)‖ ≤
      4 * ‖s - a‖ * (m : ℝ) / (1 + ‖ρ - a‖ ^ 2) := by
  have hr1 : 1 ≤ ‖ρ - a‖ := (le_max_left _ _).trans hr
  have hrM : 2 * ‖s - a‖ ≤ ‖ρ - a‖ := (le_max_right _ _).trans hr
  have hr0 : 0 < ‖ρ - a‖ := by linarith
  have hd : ‖ρ - a‖ / 2 ≤ ‖s - ρ‖ := by
    have h := norm_sub_norm_le (ρ - a) (s - a)
    rw [sub_sub_sub_cancel_right, norm_sub_rev ρ s] at h
    linarith
  have hd0 : 0 < ‖s - ρ‖ := by linarith
  have ha0 : a - ρ ≠ 0 := sub_ne_zero.mpr (norm_pos_iff.mp hr0 |> sub_ne_zero.mp).symm
  have he : (s - ρ)⁻¹ - (a - ρ)⁻¹ = (a - s) / ((s - ρ) * (a - ρ)) := by
    field_simp [ha0, norm_pos_iff.mp hd0]; ring
  have hfirst : ‖(m : ℂ) * ((s - ρ)⁻¹ - (a - ρ)⁻¹)‖ ≤
      2 * ‖s - a‖ * (m : ℝ) / ‖ρ - a‖ ^ 2 := by
    rw [he, norm_mul, norm_div, norm_mul, Complex.norm_natCast,
      norm_sub_rev a s, norm_sub_rev a ρ]
    calc
      _ ≤ (m : ℝ) * (‖s - a‖ / ((‖ρ - a‖ / 2) * ‖ρ - a‖)) := by gcongr
      _ = _ := by ring
  apply hfirst.trans
  rw [div_le_div_iff₀ (sq_pos_of_pos hr0) (by positivity : 0 < 1 + ‖ρ - a‖ ^ 2)]
  have hden : 1 + ‖ρ - a‖ ^ 2 ≤ 2 * ‖ρ - a‖ ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hden
    (show 0 ≤ 2 * ‖s - a‖ * (m : ℝ) by positivity)]

private theorem rational_summable {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a : ℂ} (ha : F a ≠ 0) (s : ℂ)
    (hw : Summable (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℝ) / (1 + ‖ρ.1 - a‖ ^ 2))) :
    Summable (fun ρ : {z : ℂ // F z = 0} => (analyticOrderNatAt F ρ.1 : ℂ) *
      ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹)) := by
  apply (hw.mul_left (4 * ‖s - a‖)).of_norm_bounded_eventually
  have he : ∀ᶠ ρ : {z : ℂ // F z = 0} in cofinite,
      max 1 (2 * ‖s - a‖) ≤ ‖ρ.1 - a‖ := by
    apply Filter.mem_cofinite.mpr
    apply (finite_zeros hF ha (max 1 (2 * ‖s - a‖))).subset
    intro ρ hρ
    exact (not_le.mp (show ¬max 1 (2 * ‖s - a‖) ≤ ‖ρ.1 - a‖ from hρ)).le
  filter_upwards [he] with ρ hρ
  simpa [mul_div_assoc] using rational_tail a s ρ.1 (analyticOrderNatAt F ρ.1) hρ

private theorem physical_error {F : ℂ → ℂ} {a s : ℂ} {β D R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall a R))
    (ha : F a ≠ 0) (hβ : 0 ≤ β)
    (hg : ∀ z : ℂ, ‖z‖ ≤ (24 / 25 : ℝ) * R →
      ‖(F a)⁻¹ * F (a + z)‖ ≤ Real.exp (D * (1 + ‖z‖) ^ β))
    (hsR : ‖s - a‖ ≤ (83 / 100) * R) :
    ‖(logDeriv (Cf (22 / 25) (scaled F a R)) ((s - a) / (R : ℂ)) -
      logDeriv (Cf (22 / 25) (scaled F a R)) 0) / (R : ℂ)‖ ≤
      (2 * 44795000 / (83 / 100 : ℝ)) *
        Real.log (max 2 (Real.exp (D * (1 + (24 / 25 : ℝ) * R) ^ β))) * ‖s - a‖ / R ^ 2 := by
  have hR : 0 ≤ R := by nlinarith [norm_nonneg (s - a)]
  have hD : 0 ≤ D := Real.one_le_exp_iff.mp (by
    simpa [ha] using hg 0 (by simpa using (show 0 ≤ (24 / 25 : ℝ) * R by positivity)))
  rcases hR.eq_or_lt with hR | hR0
  · subst R; simp
  have hz : ‖(s - a) / (R : ℂ)‖ ≤ 83 / 100 := by
    rw [norm_div, Complex.norm_of_nonneg hR0.le, div_le_iff₀ hR0]
    exact hsR
  have hB : 2 ≤ max 2 (Real.exp (D * (1 + (24 / 25 : ℝ) * R) ^ β)) :=
    le_max_left _ _
  have hfB : ∀ w, ‖w‖ ≤ 24 / 25 →
      ‖scaled F a R w‖ ≤ max 2 (Real.exp (D * (1 + (24 / 25 : ℝ) * R) ^ β)) := by
    intro w hw
    have hwlocal : ‖(R : ℂ) * w‖ ≤ (24 / 25 : ℝ) * R := by
      rw [norm_mul, Complex.norm_of_nonneg hR0.le]
      nlinarith
    calc
      _ ≤ Real.exp (D * (1 + ‖(R : ℂ) * w‖) ^ β) := hg _ hwlocal
      _ ≤ Real.exp (D * (1 + (24 / 25 : ℝ) * R) ^ β) := by gcongr
      _ ≤ _ := le_max_right _ _
  rw [norm_div, Complex.norm_of_nonneg hR0.le]
  have hc := centered_cf (scaled_analytic hF hR0.le) (scaled_zero ha R) hB hfB hz
  have hc0 := norm_logDeriv_Cf_le (scaled_analytic hF hR0.le) (scaled_zero ha R)
    (finite_SetOfZeros (scaled_analytic hF hR0.le) (by rw [scaled_zero ha R]; norm_num))
    hB hfB (z := 0) (by norm_num)
  calc
    _ ≤ ((2 * (44795000 * Real.log (max 2 (Real.exp (D * (1 + (24 / 25 : ℝ) * R) ^ β))))) /
      (83 / 100 : ℝ) * ‖(s - a) / (R : ℂ)‖) / R :=
      div_le_div_of_nonneg_right (hc.trans (by gcongr; linarith)) hR0.le
    _ = _ := by rw [norm_div, Complex.norm_of_nonneg hR0.le]; ring

/-- A finite zero cutoff has an explicit inverse-square logarithmic derivative error.
The normalized growth exponent need not be below two for this finite-radius estimate. -/
theorem entire_logDeriv_difference_truncation {F : ℂ → ℂ} {a s : ℂ} {β D R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall a R))
    (ha : F a ≠ 0) (hs : F s ≠ 0)
    (hβ : 0 ≤ β)
    (hg : ∀ z : ℂ, ‖z‖ ≤ (24 / 25 : ℝ) * R →
      ‖(F a)⁻¹ * F (a + z)‖ ≤ Real.exp (D * (1 + ‖z‖) ^ β))
    (hsR : ‖s - a‖ ≤ (83 / 100) * R)
    (t : Finset {z : ℂ // F z = 0})
    (ht : ∀ ρ : {z : ℂ // F z = 0}, ρ ∈ t ↔ ‖ρ.1 - a‖ ≤ (22 / 25) * R) :
    ‖logDeriv F s - logDeriv F a -
      ∑ ρ ∈ t, (analyticOrderNatAt F ρ.1 : ℂ) *
        ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹)‖ ≤
      (2 * 44795000 / (83 / 100 : ℝ)) *
        Real.log (max 2 (Real.exp (D * (1 + (24 / 25 : ℝ) * R) ^ β))) * ‖s - a‖ / R ^ 2 := by
  classical
  have hR : 0 ≤ R := by nlinarith [norm_nonneg (s - a)]
  rcases hR.eq_or_lt with hR | hR0
  · subst R
    have hsa : s = a := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hsR))
    subst s
    simp
  have hsplit := finite_split hF ha hs hR0 (by
    rw [norm_div, Complex.norm_of_nonneg hR0.le, div_lt_iff₀ hR0]; linarith) t ht
  rw [hsplit, add_sub_cancel_left]
  exact physical_error hF ha hβ hg hsR

private theorem growth_decay {β D : ℝ} (hβ : 0 ≤ β) (hβ2 : β < 2) (hD : 0 ≤ D) :
    Tendsto (fun R : ℝ => Real.log (2 * Real.exp (D * (1 + R) ^ β)) / R ^ 2)
      atTop (𝓝 0) := by
  have hn : ∀ᶠ R : ℝ in atTop,
      0 ≤ Real.log (2 * Real.exp (D * (1 + R) ^ β)) / R ^ 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    positivity
  apply squeeze_zero' hn ?_
    (show Tendsto (fun R : ℝ => (Real.log 2 + D * 2 ^ β) * R ^ (-(2 - β)))
      atTop (𝓝 0) by
      simpa using (tendsto_rpow_neg_atTop (sub_pos.mpr hβ2)).const_mul
        (Real.log 2 + D * 2 ^ β))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hR0 : 0 < R := by linarith
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp,
    add_div, mul_div_assoc]
  have hp : (1 + R) ^ β ≤ 2 ^ β * R ^ β := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR0.le]
    apply Real.rpow_le_rpow (by positivity) (by linarith) hβ
  have hpow : R ^ β / R ^ 2 = R ^ (-(2 - β)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hR0]; congr 1 <;> push_cast <;> ring
  have hsmall : 1 / R ^ 2 ≤ R ^ (-(2 - β)) := by
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hR0.le]
    apply Real.rpow_le_rpow_of_exponent_le hR
    norm_num; linarith
  have hdiv := div_le_div_of_nonneg_right hp (sq_nonneg R)
  rw [mul_div_assoc, hpow] at hdiv
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsmall' : Real.log 2 / R ^ 2 ≤ Real.log 2 * R ^ (-(2 - β)) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hsmall hlog
  nlinarith [mul_le_mul_of_nonneg_left hdiv hD]


/-- An entire function of growth strictly below quadratic has a two-point
logarithmic derivative difference equal to its multiplicity-weighted zero sum. -/
theorem entire_logDeriv_difference_hasSum {a s : ℂ} {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {α C : ℝ} (hα : α < 2)
    (hg : ∀ z, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ α))
    (ha : F a ≠ 0) (hs : F s ≠ 0) :
    HasSum (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℂ) * ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹))
      (logDeriv F s - logDeriv F a) := by
  let D := (max C 0) * (1 + ‖a‖) ^ (max α 0) + max (-Real.log ‖F a‖) 0
  obtain ⟨hD, hnorm⟩ :=
    normalized_growth (a := a) hg
  have hβ : 0 ≤ max α 0 := le_max_right _ _
  have hβ2 : max α 0 < 2 := max_lt hα (by norm_num)
  let b := fun ρ : {z : ℂ // F z = 0} =>
    (analyticOrderNatAt F ρ.1 : ℂ) * ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹)
  let e := fun R : ℝ => logDeriv F s - logDeriv F a -
    ∑ ρ ∈ cutoff hF ha R, b ρ
  have he : Tendsto e atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun R : ℝ =>
      (Real.log (2 * Real.exp (D * (1 + R) ^ (max α 0))) / R ^ 2) *
        ((2 * 44795000 / (83 / 100 : ℝ)) * ‖s - a‖))
    · filter_upwards [eventually_ge_atTop (max 1 (2 * ‖s - a‖))] with R hR
      have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
      have hRM : 2 * ‖s - a‖ ≤ R := (le_max_right _ _).trans hR
      apply (entire_logDeriv_difference_truncation (fun z _ => hF.analyticAt z) ha hs hβ
        (fun z _ => hnorm z) (by linarith)
        (cutoff hF ha R) (mem_cutoff hF ha R)).trans
      calc
        _ ≤ (2 * 44795000 / (83 / 100 : ℝ)) *
            Real.log (2 * Real.exp (D * (1 + R) ^ (max α 0))) * ‖s - a‖ / R ^ 2 := by
          have hE : 0 ≤ D * (1 + R) ^ (max α 0) := by positivity
          have hmax : max 2 (Real.exp (D * (1 + (24 / 25 : ℝ) * R) ^
              (max α 0))) ≤ 2 * Real.exp (D * (1 + R) ^ (max α 0)) := by
            apply max_le
            · nlinarith [Real.one_le_exp hE]
            · have hh : Real.exp (D * (1 + (24 / 25 : ℝ) * R) ^ (max α 0)) ≤
                  Real.exp (D * (1 + R) ^ (max α 0)) := by gcongr <;> linarith
              linarith [Real.exp_pos (D * (1 + R) ^ (max α 0))]
          gcongr
        _ = _ := by ring
    · simpa using (growth_decay hβ hβ2 hD).mul_const
        ((2 * 44795000 / (83 / 100 : ℝ)) * ‖s - a‖)
  have hb : Summable b := rational_summable hF ha s
    (entire_zero_summable hF hα hg).1
  have hl := (hb.hasSum.comp (cutoff_tendsto hF ha)).add he
  simp only [add_zero] at hl
  have hv : Tendsto (fun R : ℝ => (∑ ρ ∈ cutoff hF ha R, b ρ) + e R) atTop
      (𝓝 (logDeriv F s - logDeriv F a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [] with R
    dsimp [e]
    abel
  have hval := tendsto_nhds_unique hl hv
  exact hval ▸ hb.hasSum

end D5.S3.Analytic.Resolvent.EntireLogDerivDifference
