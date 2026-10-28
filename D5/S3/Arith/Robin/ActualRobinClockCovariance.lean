/- GID: D5/S3/Arith/Robin/ActualRobinClockCovariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ActualRobinClockCovariance
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual activation gives the logarithmic range and finite covariance budget. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
The kernels below are the literal clipped finite kernels, including noninteger
clocks. No covariance, range, monotonicity or convexity envelope is a premise.
The activation integral and its exact logarithmic range estimate are consumed
by the quantitative centered covariance theorem. The original compiled sign
and support calculation is preserved as a private helper. This is an analytic
component for arbitrary clocks, not a realization theorem for the largest
equality-inclusive CA sample. The ordinary quantitative calculation is from
Library/Analytic/mantovanelli2026primeworkload.md at immutable source
cd554e98a13551899994b718e7cdbd35d81624ab (U-int, U-size, U-var, G-size, G-var, J). The harmonic
shell variation is consumed in the importing finite coefficient-mass module.
The Corr supplier, CA clock realization and full Robin result remain unpaid;
no convexity of U is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators Interval Topology

namespace D5.S3.Arith.Robin.ActualRobinClockCovariance

/-- The exact reciprocal logarithmic kernel. -/
def g (t : ℝ) : ℝ := 1 / (t * Real.log t)

/-- The positive activation density, equal to `-g'` on `(1,∞)`. -/
def activationDensity (t : ℝ) : ℝ :=
  (Real.log t + 1) / (t^2 * (Real.log t)^2)

/-- Exact logarithmic range budget; no clock-realization hypothesis enters it. -/
def rangeBudget (a b : ℝ) : ℝ :=
  Real.log (b/a) + Real.log (Real.log b / Real.log a)

/-- Literal finite definition: all integer layers from 2 through floor A. -/
def W (A x : ℝ) : ℝ :=
  ∑ k ∈ Icc 2 ⌊A⌋₊, Real.log (k : ℝ) * max (g ((k : ℝ) * x) - g A) 0

private def ambientW (b A x : ℝ) : ℝ :=
  ∑ k ∈ Icc 2 ⌊b⌋₊, Real.log (k : ℝ) * max (g ((k : ℝ) * x) - g A) 0

private theorem g_antitone {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : g t ≤ g s := by
  have hs0 : 0 < s := by linarith
  have hl : 0 < Real.log s := Real.log_pos hs
  have hlog : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst
  exact one_div_le_one_div_of_le (mul_pos hs0 hl)
    (mul_le_mul hst hlog hl.le (by linarith))

private theorem layer_zero {A x : ℝ} {k : ℕ}
    (hA : 1 < A) (hx : 1 ≤ x) (hk : A ≤ (k : ℝ)) :
    max (g ((k : ℝ) * x) - g A) 0 = 0 := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hAx : A ≤ (k : ℝ) * x := hk.trans (by nlinarith)
  exact max_eq_right (sub_nonpos.mpr (g_antitone hA hAx))

private theorem ambient_eq {b A x : ℝ} (hA : 1 < A) (hAb : A ≤ b)
    (hx : 1 ≤ x) : ambientW b A x = W A x := by
  unfold ambientW W
  symm
  apply sum_subset
  · intro k hk
    exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1,
      (mem_Icc.mp hk).2.trans (Nat.floor_mono hAb)⟩
  · intro k hk hnot
    have hfloor : ⌊A⌋₊ < k := by
      have hk2 := (mem_Icc.mp hk).1
      simp only [mem_Icc, not_and, not_le] at hnot
      exact hnot hk2
    rw [layer_zero hA hx (Nat.lt_of_floor_lt hfloor).le, mul_zero]

private theorem clipped_difference {p u v : ℝ} (hvu : v ≤ u) :
    max (p-v) 0 - max (p-u) 0 = min (max (p-v) 0) (u-v) := by
  by_cases hpv : p ≤ v
  · rw [max_eq_right (by linarith : p-v ≤ 0),
      max_eq_right (by linarith : p-u ≤ 0), min_eq_left (by linarith)]
    ring
  · by_cases hpu : p ≤ u
    · rw [max_eq_left (by linarith : 0 ≤ p-v),
        max_eq_right (by linarith : p-u ≤ 0), min_eq_left (by linarith)]
      ring
    · rw [max_eq_left (by linarith : 0 ≤ p-v),
        max_eq_left (by linarith : 0 ≤ p-u), min_eq_right (by linarith)]
      ring

/-- The exact relative activation, in a common finite ambient family. -/
private theorem relative_activation {b A A' x : ℝ}
    (hA' : 1 < A') (horder : A' ≤ A) (hAb : A ≤ b) (hx : 1 ≤ x) :
    W A x - W A' x =
      ∑ k ∈ Icc 2 ⌊b⌋₊, Real.log (k : ℝ) *
        min (max (g ((k : ℝ)*x) - g A) 0) (g A' - g A) := by
  rw [← ambient_eq (hA'.trans_le horder) hAb hx,
    ← ambient_eq hA' (horder.trans hAb) hx]
  unfold ambientW
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  rw [← mul_sub, clipped_difference (g_antitone hA' horder)]

theorem g_has_deriv_at {t : ℝ} (ht : 1 < t) :
    HasDerivAt g (-activationDensity t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have h := (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)) (mul_ne_zero ht0 hl0)
  exact h.congr_deriv (by
    dsimp [activationDensity]
    field_simp [ht0, hl0] <;> ring)

theorem density_integrable {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    IntervalIntegrable activationDensity MeasureTheory.volume s t := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hst]
  have hp : ∀ u ∈ Set.Icc s t, 1 < u := fun u hu => hs.trans_le hu.1
  have h0 : ∀ u ∈ Set.Icc s t, u ≠ 0 := fun u hu => ne_of_gt (by linarith [hp u hu])
  have hl : ContinuousOn Real.log (Set.Icc s t) := continuousOn_id.log h0
  unfold activationDensity
  exact (hl.add continuousOn_const).div
    ((continuousOn_id.pow 2).mul (hl.pow 2)) (fun u hu =>
      mul_ne_zero (pow_ne_zero 2 (h0 u hu))
        (pow_ne_zero 2 (ne_of_gt (Real.log_pos (hp u hu)))))

theorem density_integral {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    (∫ u in s..t, activationDensity u) = g s - g t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => -g u) (f' := activationDensity)
    (fun u hu => by
      rw [Set.uIcc_of_le hst] at hu
      change HasDerivAt (-g) (activationDensity u) u
      simpa only [neg_neg] using (g_has_deriv_at (hs.trans_le hu.1)).neg)
    (density_integrable hs hst)
  simpa only [neg_sub_neg] using h

private def layerDensity (p t : ℝ) : ℝ :=
  (Set.Ioi p).indicator activationDensity t

private theorem layer_integrable {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) (p : ℝ) :
    IntervalIntegrable (layerDensity p) MeasureTheory.volume s t := by
  have h := density_integrable hs hst
  exact ⟨h.1.indicator measurableSet_Ioi, h.2.indicator measurableSet_Ioi⟩

/-- Clamping is evaluated before integration. Original positive-part layers
vanish at their own activation threshold; singleton intervals have zero
integral. The three cases include empty and singleton clock shells. -/
private theorem layer_integral {s t p : ℝ} (hs : 1 < s) (hst : s ≤ t)
    (hp : 1 < p) :
    min (max (g p-g t) 0) (g s-g t) = ∫ u in s..t, layerDensity p u := by
  have hstg := g_antitone hs hst
  by_cases hps : p ≤ s
  · have hpg := g_antitone hp hps
    rw [min_eq_right (by
      exact le_trans (by linarith : g s-g t ≤ g p-g t) (le_max_left _ _))]
    rw [← density_integral hs hst]
    apply intervalIntegral.integral_congr_Ioo_of_le hst
    intro u hu
    simp [layerDensity, Set.mem_Ioi, hps.trans_lt hu.1]
  · by_cases htp : t ≤ p
    · rw [max_eq_right (sub_nonpos.mpr (g_antitone (hs.trans_le hst) htp)),
        min_eq_left (by linarith)]
      symm
      calc
        (∫ u in s..t, layerDensity p u) = ∫ _ in s..t, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hst
          intro u hu
          simp [layerDensity, Set.mem_Ioi, not_lt.mpr (hu.2.le.trans htp)]
        _ = 0 := by simp
    · have hsp : s ≤ p := (le_of_not_ge hps)
      have hpt : p ≤ t := (le_of_not_ge htp)
      have hpg := g_antitone hs hsp
      have htpg := g_antitone hp hpt
      rw [max_eq_left (by linarith), min_eq_left (by linarith)]
      rw [← density_integral hp hpt]
      symm
      unfold layerDensity
      rw [intervalIntegral.integral_of_le hst,
        MeasureTheory.integral_indicator measurableSet_Ioi,
        MeasureTheory.Measure.restrict_restrict measurableSet_Ioi,
        Set.inter_comm, Set.Ioc_inter_Ioi, sup_eq_right.mpr hsp,
        ← intervalIntegral.integral_of_le hpt]

private def activationPrefix (b x t : ℝ) : ℝ :=
  ∑ k ∈ Icc 2 ⌊b⌋₊, if (k : ℝ)*x < t then Real.log (k : ℝ) else 0

private theorem relative_integral {b A A' x : ℝ}
    (hA' : 1 < A') (horder : A' ≤ A) (hAb : A ≤ b) (hx : 1 ≤ x) :
    W A x - W A' x =
      ∫ t in A'..A, activationDensity t * activationPrefix b x t := by
  rw [relative_activation hA' horder hAb hx]
  have hterm : ∀ k ∈ Icc 2 ⌊b⌋₊,
      IntervalIntegrable (fun t => Real.log (k : ℝ) * layerDensity ((k : ℝ)*x) t)
        MeasureTheory.volume A' A :=
    fun k _ => (layer_integrable hA' horder _).const_mul _
  calc
    _ = ∑ k ∈ Icc 2 ⌊b⌋₊,
        ∫ t in A'..A, Real.log (k : ℝ) * layerDensity ((k : ℝ)*x) t := by
      apply sum_congr rfl
      intro k hk
      have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
      rw [layer_integral hA' horder (by nlinarith), intervalIntegral.integral_const_mul]
    _ = ∫ t in A'..A, ∑ k ∈ Icc 2 ⌊b⌋₊,
        Real.log (k : ℝ) * layerDensity ((k : ℝ)*x) t :=
      (intervalIntegral.integral_finsetSum hterm).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      unfold activationPrefix
      dsimp only
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      by_cases hkt : (k : ℝ)*x < t <;>
        simp [layerDensity, Set.indicator, Set.mem_Ioi, hkt] <;> ring

private theorem prefix_le {b x t : ℝ} (hx : 1 ≤ x) (ht : 1 < t) :
    activationPrefix b x t ≤ (t/x)*Real.log t := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t := by linarith
  let s : Finset ℕ := (Icc 2 ⌊b⌋₊).filter (fun k => (k : ℝ)*x < t)
  have hsub : s ⊆ Icc 1 ⌊t/x⌋₊ := by
    intro k hk
    rcases mem_filter.mp hk with ⟨hk, hkt⟩
    have hk2 := (mem_Icc.mp hk).1
    refine mem_Icc.mpr ⟨by omega, ?_⟩
    apply (Nat.le_floor_iff' (by omega : k ≠ 0)).mpr
    exact (lt_div_iff₀ hx0).mpr hkt |>.le
  have hcard : (s.card : ℝ) ≤ t/x := by
    have hc : s.card ≤ ⌊t/x⌋₊ := by simpa using card_le_card hsub
    exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (by positivity))
  calc
    activationPrefix b x t = ∑ k ∈ s, Real.log (k : ℝ) := by
      simp [activationPrefix, s, sum_filter]
    _ ≤ ∑ _k ∈ s, Real.log t := by
      apply sum_le_sum
      intro k hk
      rcases mem_filter.mp hk with ⟨hk, hkt⟩
      have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
      exact Real.log_le_log (by linarith) (by nlinarith)
    _ = (s.card : ℝ)*Real.log t := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.log_pos ht).le

theorem price_terms_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1/t) MeasureTheory.volume a b ∧
    IntervalIntegrable (fun t : ℝ => t⁻¹/Real.log t) MeasureTheory.volume a b := by
  have h0 : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht => ne_of_gt (by linarith [ht.1])
  have hl0 : ∀ t ∈ Set.Icc a b, Real.log t ≠ 0 :=
    fun t ht => ne_of_gt (Real.log_pos (ha.trans_le ht.1))
  have hl : ContinuousOn Real.log (Set.Icc a b) := continuousOn_id.log h0
  constructor
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div continuousOn_id h0
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact (continuousOn_id.inv₀ h0).div hl hl0

private theorem relative_size {a b A A' x : ℝ}
    (ha : 1 < a) (haA' : a ≤ A') (horder : A' ≤ A) (hAb : A ≤ b) (hx : 1 ≤ x) :
    W A x - W A' x ≤ rangeBudget a b / x := by
  have hA' : 1 < A' := ha.trans_le haA'
  have hab : a ≤ b := haA'.trans (horder.trans hAb)
  have hx0 : 0 < x := by linarith
  let q : ℝ → ℝ := fun t => 1/t + t⁻¹/Real.log t
  have hparts := price_terms_integrable ha hab
  have hq : IntervalIntegrable q MeasureTheory.volume a b := by
    exact hparts.1.add hparts.2
  have hi : IntervalIntegrable (fun t => activationDensity t * activationPrefix b x t)
      MeasureTheory.volume A' A := by
    have hterm : ∀ k ∈ Icc 2 ⌊b⌋₊,
        IntervalIntegrable (fun t => Real.log (k : ℝ)*layerDensity ((k : ℝ)*x) t)
          MeasureTheory.volume A' A :=
      fun k _ => (layer_integrable hA' horder _).const_mul _
    have heq : (fun t => activationDensity t * activationPrefix b x t) =
        ∑ k ∈ Icc 2 ⌊b⌋₊,
          (fun t => Real.log (k : ℝ)*layerDensity ((k : ℝ)*x) t) := by
      funext t
      simp only [Finset.sum_apply]
      unfold activationPrefix
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      by_cases hkt : (k : ℝ)*x < t <;>
        simp [layerDensity, Set.indicator, Set.mem_Ioi, hkt] <;> ring
    rw [heq]
    exact IntervalIntegrable.sum (Icc 2 ⌊b⌋₊) hterm
  have hq' : IntervalIntegrable q MeasureTheory.volume A' A :=
    hq.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le horder]
      exact Set.Icc_subset_Icc haA' hAb)
  have hint : (∫ t in A'..A, q t) ≤ ∫ t in a..b, q t := by
    apply intervalIntegral.integral_mono_interval haA' horder hAb
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      intro t ht
      have ht1 := ha.trans_le ht.1.le
      exact add_nonneg (by positivity) (div_nonneg (by positivity) (Real.log_pos ht1).le)
    · exact hq
  have hcompute : (∫ t in a..b, q t) = rangeBudget a b := by
    rw [show q = fun t => 1/t + t⁻¹/Real.log t from rfl,
      intervalIntegral.integral_add hparts.1 hparts.2,
      integral_one_div_of_pos (by linarith) (by linarith),
      integral_inv_div_log ha (ha.trans_le hab)]
    unfold rangeBudget
    rw [Real.log_div (ne_of_gt (Real.log_pos (ha.trans_le hab)))
      (ne_of_gt (Real.log_pos ha))]
  rw [relative_integral hA' horder hAb hx]
  calc
    _ ≤ ∫ t in A'..A, q t / x := by
      apply intervalIntegral.integral_mono_on horder hi (hq'.div_const x)
      intro t ht
      have ht1 := hA'.trans_le ht.1
      have ht0 : t ≠ 0 := ne_of_gt (by linarith)
      have hl0 := ne_of_gt (Real.log_pos ht1)
      have hd : 0 ≤ activationDensity t := by
        unfold activationDensity
        exact div_nonneg (by linarith [Real.log_pos ht1])
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      calc
        _ ≤ activationDensity t * ((t/x)*Real.log t) :=
          mul_le_mul_of_nonneg_left (prefix_le hx ht1) hd
        _ = q t / x := by
          dsimp [q, activationDensity]
          field_simp [ht0, hl0, ne_of_gt hx0] <;> ring
    _ = (∫ t in A'..A, q t) / x := intervalIntegral.integral_div x q
    _ ≤ (∫ t in a..b, q t) / x := div_le_div_of_nonneg_right hint hx0.le
    _ = _ := by rw [hcompute]

private theorem W_clock_mono {A A' x : ℝ}
    (hA' : 1 < A') (horder : A' ≤ A) (hx : 1 ≤ x) : W A' x ≤ W A x := by
  rw [← sub_nonneg]
  rw [relative_activation hA' horder le_rfl hx]
  apply sum_nonneg
  intro k hk
  have hk1 : 1 ≤ (k : ℝ) := by
    have hk1n : 1 ≤ k := (by
      exact le_trans (by norm_num) (mem_Icc.mp hk).1)
    exact_mod_cast hk1n
  exact mul_nonneg (Real.log_nonneg hk1)
    (le_min (le_max_right _ _) (sub_nonneg.mpr (g_antitone hA' horder)))

private theorem relative_decreasing {A A' x y : ℝ}
    (hA' : 1 < A') (horder : A' ≤ A) (hx : 1 ≤ x) (hxy : x ≤ y) :
    W A y - W A' y ≤ W A x - W A' x := by
  rw [relative_activation hA' horder le_rfl hx,
    relative_activation hA' horder le_rfl (hx.trans hxy)]
  apply sum_le_sum
  intro k hk
  have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
  have hk1 : 1 ≤ (k : ℝ) := by linarith
  apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg hk1)
  apply min_le_min_right
  apply max_le_max_right
  apply sub_le_sub_right
  apply g_antitone
  · nlinarith
  · exact mul_le_mul_of_nonneg_left hxy (by positivity)

private theorem harmonic_interval {n N : ℕ} (hnN : n ≤ N) :
    (∑ k ∈ Icc n N, (k : ℝ)⁻¹) =
      (n : ℝ)⁻¹ + (harmonic N : ℝ) - (harmonic n : ℝ) := by
  induction N, hnN using Nat.le_induction with
  | base => simp
  | succ N hnN ih =>
    rw [sum_Icc_succ_top (hnN.trans (Nat.le_succ _)), harmonic_succ]
    simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
    rw [ih]
    ring

private theorem harmonic_interval_le {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    (∑ k ∈ Icc n N, (k : ℝ)⁻¹) ≤ 1/2 + Real.log ((N : ℝ)/n) := by
  have hn0 : n ≠ 0 := by omega
  have hN0 : N ≠ 0 := by omega
  have h := Real.strictAnti_eulerMascheroniSeq'.antitone hnN
  simp only [Real.eulerMascheroniSeq', hn0, hN0, if_false] at h
  have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hinv : (n : ℝ)⁻¹ ≤ 1/2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hnR
  rw [harmonic_interval hnN,
    Real.log_div (by exact_mod_cast hN0) (by exact_mod_cast hn0)]
  linarith

private theorem shell_harmonic_le {s : Finset ℕ} {A A' x : ℝ}
    (hA' : 0 < A') (horder : A' ≤ A) (hx : 0 < x)
    (hmem : ∀ k ∈ s, 2 ≤ k ∧ A' ≤ (k : ℝ)*x ∧ (k : ℝ)*x ≤ A) :
    (∑ k ∈ s, (k : ℝ)⁻¹) ≤ 1/2 + Real.log (A/A') := by
  by_cases hs : s.Nonempty
  · let n := s.min' hs
    let N := s.max' hs
    have hnmem : n ∈ s := min'_mem s hs
    have hNmem : N ∈ s := max'_mem s hs
    have hnN : n ≤ N := le_max' s n hnmem
    have hsub : s ⊆ Icc n N := fun k hk =>
      mem_Icc.mpr ⟨min'_le s k hk, le_max' s k hk⟩
    have hsum : (∑ k ∈ s, (k : ℝ)⁻¹) ≤ ∑ k ∈ Icc n N, (k : ℝ)⁻¹ := by
      exact sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    have hn2 := (hmem n hnmem).1
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hratio : (N : ℝ)/n ≤ A/A' := by
      apply (div_le_div_iff₀ hnR hA').mpr
      have hleft := mul_le_mul_of_nonneg_left (hmem n hnmem).2.1 hNR.le
      have hright := mul_le_mul_of_nonneg_left (hmem N hNmem).2.2 hnR.le
      nlinarith [hleft, hright]
    exact hsum.trans ((harmonic_interval_le hn2 hnN).trans
      (add_le_add le_rfl (Real.log_le_log (div_pos hNR hnR) hratio)))
  · have hlog : 0 ≤ Real.log (A/A') :=
      Real.log_nonneg ((one_le_div hA').mpr horder)
    simp only [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    linarith


private theorem g_strict_decrease {s t : ℝ} (hs : 1 < s) (hst : s < t) :
    g t < g s := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hls : 0 < Real.log s := Real.log_pos hs
  have hlog : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst.le
  have hden : s*Real.log s < t*Real.log t :=
    (mul_lt_mul_of_pos_right hst hls).trans_le
      (mul_le_mul_of_nonneg_left hlog ht0.le)
  exact one_div_lt_one_div_of_lt (mul_pos hs0 hls) hden

private theorem layer_right_deriv {A x : ℝ} {k : ℕ}
    (hA : 1 < A) (hk : 2 ≤ k) (hx : 1 ≤ x) :
    HasDerivWithinAt (fun u => max (g ((k : ℝ)*u)-g A) 0)
      (if (k : ℝ)*x < A then -(k : ℝ)*activationDensity ((k : ℝ)*x) else 0)
      (Set.Ioi x) x := by
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hp : 1 < (k : ℝ)*x := by nlinarith
  by_cases hpx : (k : ℝ)*x < A
  · rw [if_pos hpx]
    have hd := ((g_has_deriv_at hp).comp x ((hasDerivAt_id x).const_mul (k : ℝ))).sub_const (g A)
    have hpos : 0 < g ((k : ℝ)*x)-g A := sub_pos.mpr (g_strict_decrease hp hpx)
    have hev : ∀ᶠ u in 𝓝 x, 0 < g ((k : ℝ)*u)-g A :=
      continuousAt_const.eventually_lt hd.continuousAt hpos
    have heq : (fun u => max (g ((k : ℝ)*u)-g A) 0) =ᶠ[𝓝 x]
        (fun u => g ((k : ℝ)*u)-g A) := by
      filter_upwards [hev] with u hu
      exact max_eq_left hu.le
    have h := hd.congr_of_eventuallyEq heq
    exact h.hasDerivWithinAt.congr_deriv (by ring)
  · rw [if_neg hpx]
    have hAx : A ≤ (k : ℝ)*x := le_of_not_gt hpx
    have hz : max (g ((k : ℝ)*x)-g A) 0 = 0 :=
      max_eq_right (sub_nonpos.mpr (g_antitone hA hAx))
    exact (hasDerivWithinAt_const x (Set.Ioi x) (0 : ℝ)).congr
      (fun u hu => max_eq_right (sub_nonpos.mpr
        (g_antitone hA (hAx.trans (mul_le_mul_of_nonneg_left hu.le hk0))))) hz

private def shellDensity (b A A' x : ℝ) : ℝ :=
  ∑ k ∈ Icc 2 ⌊b⌋₊,
    if A' ≤ (k : ℝ)*x ∧ (k : ℝ)*x < A
    then Real.log (k : ℝ)*(k : ℝ)*activationDensity ((k : ℝ)*x) else 0

private theorem relative_right_deriv {b A A' x : ℝ}
    (hA' : 1 < A') (horder : A' ≤ A) (hAb : A ≤ b) (hx : 1 ≤ x) :
    HasDerivWithinAt (fun u => W A u-W A' u)
      (-shellDensity b A A' x) (Set.Ioi x) x := by
  have hd : HasDerivWithinAt (fun u => ambientW b A u-ambientW b A' u)
      (-shellDensity b A A' x) (Set.Ioi x) x := by
    unfold ambientW
    simp_rw [← sum_sub_distrib, ← mul_sub]
    have hsum := HasDerivWithinAt.fun_sum (u := Icc 2 ⌊b⌋₊) (fun k hk =>
      ((layer_right_deriv (hA'.trans_le horder) (mem_Icc.mp hk).1 hx).sub
        (layer_right_deriv hA' (mem_Icc.mp hk).1 hx)).const_mul (Real.log (k : ℝ)))
    apply hsum.congr_deriv
    unfold shellDensity
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k _
    by_cases hka : (k : ℝ)*x < A
    · by_cases hka' : (k : ℝ)*x < A'
      · simp [hka, hka', not_le.mpr hka']
      · simp [hka, hka', le_of_not_gt hka']
        ring
    · have hka' : ¬ (k : ℝ)*x < A' := by linarith
      simp [hka, hka']
  apply hd.congr
  · intro u hu
    rw [ambient_eq (hA'.trans_le horder) hAb (hx.trans hu.le),
      ambient_eq hA' (horder.trans hAb) (hx.trans hu.le)]
  · rw [ambient_eq (hA'.trans_le horder) hAb hx,
      ambient_eq hA' (horder.trans hAb) hx]

def variationBudget (a b : ℝ) : ℝ :=
  (1+1/Real.log a)*(Real.log (b/a)+1/2)

private theorem active_term_le {a x : ℝ} {k : ℕ}
    (ha : 1 < a) (hk : 2 ≤ k) (hx : 1 ≤ x) (hactive : a ≤ (k : ℝ)*x) :
    Real.log (k : ℝ)*(k : ℝ)*activationDensity ((k : ℝ)*x) ≤
      ((1+1/Real.log a)/x^2)*(k : ℝ)⁻¹ := by
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : 0 < (k : ℝ) := by linarith
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log ((k : ℝ)*x) := Real.log_pos (ha.trans_le hactive)
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlog : Real.log (k : ℝ) ≤ Real.log ((k : ℝ)*x) :=
    Real.log_le_log hk0 (by nlinarith)
  have hlogA : Real.log a ≤ Real.log ((k : ℝ)*x) :=
    Real.log_le_log (by linarith) hactive
  have hratio : Real.log (k : ℝ)/Real.log ((k : ℝ)*x) ≤ 1 :=
    (div_le_one hl0).mpr hlog
  have hD : 1+1/Real.log ((k : ℝ)*x) ≤ 1+1/Real.log a :=
    add_le_add le_rfl (one_div_le_one_div_of_le hla hlogA)
  have hprod := mul_le_mul hratio hD
    (by positivity : 0 ≤ 1+1/Real.log ((k : ℝ)*x)) (by norm_num : (0 : ℝ) ≤ 1)
  have heq : Real.log (k : ℝ)*(k : ℝ)*activationDensity ((k : ℝ)*x) =
      (Real.log (k : ℝ)/Real.log ((k : ℝ)*x)) *
        (1+1/Real.log ((k : ℝ)*x))*(k : ℝ)⁻¹/x^2 := by
    unfold activationDensity
    field_simp [ne_of_gt hk0, ne_of_gt hx0, ne_of_gt hl0] <;> ring
  rw [heq]
  calc
    _ ≤ (1*(1+1/Real.log a))*(k : ℝ)⁻¹/x^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hprod (inv_nonneg.mpr hk0.le)) (sq_nonneg _)
    _ = _ := by ring

-- The actual finite shell consumes the harmonic estimate without an envelope premise.
private theorem shell_le {a b A A' x : ℝ}
    (ha : 1 < a) (haA' : a ≤ A') (horder : A' ≤ A) (hAb : A ≤ b) (hx : 1 ≤ x) :
    shellDensity b A A' x ≤ variationBudget a b/x^2 := by
  let s : Finset ℕ := (Icc 2 ⌊b⌋₊).filter
    (fun k => A' ≤ (k : ℝ)*x ∧ (k : ℝ)*x < A)
  have hx0 : 0 < x := by linarith
  have hA' : 0 < A' := by linarith
  have hD : 0 ≤ (1+1/Real.log a)/x^2 := by
    have := Real.log_pos ha
    positivity
  have hmem : ∀ k ∈ s, 2 ≤ k ∧ A' ≤ (k : ℝ)*x ∧ (k : ℝ)*x ≤ A := by
    intro k hk
    rcases mem_filter.mp hk with ⟨hk, hact⟩
    exact ⟨(mem_Icc.mp hk).1, hact.1, hact.2.le⟩
  have hharm := shell_harmonic_le hA' horder hx0 hmem
  have hratio : A/A' ≤ b/a := by
    apply (div_le_div_iff₀ hA' (by linarith : 0 < a)).mpr
    have hb0 : 0 ≤ b := by linarith
    exact (mul_le_mul_of_nonneg_right hAb (by linarith : 0 ≤ a)).trans
      (mul_le_mul_of_nonneg_left haA' hb0)
  have hlog := Real.log_le_log (div_pos (by linarith : 0 < A) hA') hratio
  calc
    shellDensity b A A' x = ∑ k ∈ s,
        Real.log (k : ℝ)*(k : ℝ)*activationDensity ((k : ℝ)*x) := by
      simp [shellDensity, s, sum_filter]
    _ ≤ ∑ k ∈ s, ((1+1/Real.log a)/x^2)*(k : ℝ)⁻¹ := by
      apply sum_le_sum
      intro k hk
      exact active_term_le ha (hmem k hk).1 hx (haA'.trans (hmem k hk).2.1)
    _ = ((1+1/Real.log a)/x^2)*(∑ k ∈ s, (k : ℝ)⁻¹) := by rw [mul_sum]
    _ ≤ ((1+1/Real.log a)/x^2)*(1/2+Real.log (A/A')) :=
      mul_le_mul_of_nonneg_left hharm hD
    _ ≤ ((1+1/Real.log a)/x^2)*(1/2+Real.log (b/a)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog) hD
    _ = variationBudget a b/x^2 := by unfold variationBudget; ring

private theorem relative_continuous {A A' x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    ContinuousOn (fun u => W A u-W A' u) (Set.Icc x y) := by
  have hc : ∀ B : ℝ, ContinuousOn (fun u => W B u) (Set.Icc x y) := by
    intro B
    unfold W
    apply continuousOn_finsetSum
    intro k hk
    have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
    have hg : ContinuousOn (fun u => g ((k : ℝ)*u)) (Set.Icc x y) := by
      intro u hu
      have hp : 1 < (k : ℝ)*u := by nlinarith [hu.1]
      exact ((g_has_deriv_at hp).continuousAt.comp
        (continuousAt_const.mul continuousAt_id)).continuousWithinAt
    exact continuousOn_const.mul ((hg.sub continuousOn_const).sup continuousOn_const)
  exact (hc A).sub (hc A')

private theorem shell_integrable {b A A' x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (fun u => shellDensity b A A' u) MeasureTheory.volume x y := by
  have hterms : ∀ k ∈ Icc 2 ⌊b⌋₊,
      IntervalIntegrable (fun u => if A' ≤ (k : ℝ)*u ∧ (k : ℝ)*u < A
        then Real.log (k : ℝ)*(k : ℝ)*activationDensity ((k : ℝ)*u) else 0)
        MeasureTheory.volume x y := by
    intro k hk
    have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
    have hk0 : 0 < (k : ℝ) := by linarith
    have hp : 1 < (k : ℝ)*x := by nlinarith
    have hd := (density_integrable hp (mul_le_mul_of_nonneg_left hxy hk0.le)).comp_mul_left
      (c := (k : ℝ))
    have heqx : (k : ℝ)*x/(k : ℝ) = x := by field_simp [ne_of_gt hk0]
    have heqy : (k : ℝ)*y/(k : ℝ) = y := by field_simp [ne_of_gt hk0]
    rw [heqx, heqy] at hd
    have hm : MeasurableSet {u : ℝ | A' ≤ (k : ℝ)*u ∧ (k : ℝ)*u < A} :=
      measurableSet_Ico.preimage (measurable_const.mul measurable_id)
    have hd' := hd.const_mul (Real.log (k : ℝ)*(k : ℝ))
    have hi : IntervalIntegrable
        ({u : ℝ | A' ≤ (k : ℝ)*u ∧ (k : ℝ)*u < A}.indicator
          (fun u => Real.log (k : ℝ)*(k : ℝ)*activationDensity ((k : ℝ)*u)))
        MeasureTheory.volume x y :=
      ⟨hd'.1.indicator hm, hd'.2.indicator hm⟩
    have heq : ({u : ℝ | A' ≤ (k : ℝ)*u ∧ (k : ℝ)*u < A}.indicator
        (fun u => Real.log (k : ℝ)*(k : ℝ)*activationDensity ((k : ℝ)*u))) =
        (fun u => if A' ≤ (k : ℝ)*u ∧ (k : ℝ)*u < A
          then Real.log (k : ℝ)*(k : ℝ)*activationDensity ((k : ℝ)*u) else 0) := by
      funext u
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [← heq]
    exact hi
  have heq : (fun u => shellDensity b A A' u) =
      ∑ k ∈ Icc 2 ⌊b⌋₊, (fun u => if A' ≤ (k : ℝ)*u ∧ (k : ℝ)*u < A
        then Real.log (k : ℝ)*(k : ℝ)*activationDensity ((k : ℝ)*u) else 0) := by
    funext u
    simp only [shellDensity, Finset.sum_apply]
  rw [heq]
  exact IntervalIntegrable.sum _ hterms

private theorem relative_variation_integral {b A A' x y : ℝ}
    (hA' : 1 < A') (horder : A' ≤ A) (hAb : A ≤ b) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (W A x-W A' x)-(W A y-W A' y) =
      ∫ u in x..y, shellDensity b A A' u := by
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hxy
    (relative_continuous hx hxy)
    (fun u hu => relative_right_deriv hA' horder hAb (hx.trans hu.1.le))
    (shell_integrable hx hxy).neg
  rw [intervalIntegral.integral_neg] at h
  linarith

private theorem relative_variation {a b A A' x y : ℝ}
    (ha : 1 < a) (haA' : a ≤ A') (horder : A' ≤ A) (hAb : A ≤ b)
    (hx : 1 ≤ x) (hxy : x ≤ y) :
    0 ≤ (W A x-W A' x)-(W A y-W A' y) ∧
    (W A x-W A' x)-(W A y-W A' y) ≤ variationBudget a b*(1/x-1/y) := by
  refine ⟨sub_nonneg.mpr (relative_decreasing (ha.trans_le haA') horder hx hxy), ?_⟩
  have hi : IntervalIntegrable (fun u : ℝ => 1/u^2) MeasureTheory.volume x y := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxy]
    exact continuousOn_const.div (continuousOn_id.pow 2) (fun u hu =>
      pow_ne_zero 2 (ne_of_gt (by linarith [hu.1] : 0 < u)))
  have hC : IntervalIntegrable (fun u => variationBudget a b/u^2)
      MeasureTheory.volume x y := by
    simpa only [mul_one_div] using hi.const_mul (variationBudget a b)
  have hzero : (0 : ℝ) ∉ Set.uIcc x y := by
    rw [Set.uIcc_of_le hxy]
    intro h
    linarith [h.1]
  have hcompute : (∫ u in x..y, (1 : ℝ)/u^2) = 1/x-1/y := by
    have h := integral_zpow (a := x) (b := y) (n := (-2 : ℤ))
      (Or.inr ⟨by norm_num, hzero⟩)
    norm_num [one_div, zpow_neg] at h ⊢
    rw [h]
    ring
  rw [relative_variation_integral (ha.trans_le haA') horder hAb hx hxy]
  calc
    _ ≤ ∫ u in x..y, variationBudget a b/u^2 := by
      apply intervalIntegral.integral_mono_on hxy (shell_integrable hx hxy) hC
      intro u hu
      exact shell_le ha haA' horder hAb (hx.trans hu.1)
    _ = variationBudget a b*(∫ u in x..y, (1 : ℝ)/u^2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      ring
    _ = _ := by rw [hcompute]


private theorem W_support {A x : ℝ} (hA : 1 < A) (_hx : 1 ≤ x)
    (hAx : A ≤ 2 * x) : W A x = 0 := by
  unfold W
  apply sum_eq_zero
  intro k hk
  have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
  have hAx' : A ≤ (k : ℝ)*x := by nlinarith
  rw [max_eq_right (sub_nonpos.mpr (g_antitone hA hAx')), mul_zero]

/-- Unnormalized centered covariance; the empty sample has covariance zero. -/
def centeredCovariance {m : ℕ} (f h : Fin m → ℝ) : ℝ :=
  ∑ i, (f i - (∑ j, f j)/(m : ℝ)) * (h i - (∑ j, h j)/(m : ℝ))

/-- Covariance of the literal clock kernels, without external normalization. -/
def Gamma {m : ℕ} (A : Fin m → ℝ) (x y : ℝ) : ℝ :=
  centeredCovariance (fun i => W (A i) x) (fun i => W (A i) y)

private theorem cov_formula {m : ℕ} (f h : Fin m → ℝ) :
    centeredCovariance f h = (∑ i, f i*h i) - (∑ i, f i)*(∑ i, h i)/(m : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simp [centeredCovariance]
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    unfold centeredCovariance
    simp_rw [sub_mul, mul_sub]
    simp only [sum_sub_distrib, sum_mul, mul_sum, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hr : (∑ x, ∑ i, f i * h x) =
        (∑ i, f i) * (∑ x, h x) := by
      simp_rw [← Finset.sum_mul]
      rw [Finset.mul_sum]
    have hleft : (∑ x, f x * ((∑ j, h j) / (m : ℝ))) =
        (∑ x, f x) * ((∑ j, h j) / (m : ℝ)) := by
      rw [← Finset.sum_mul]
    have hright : (∑ x, ((∑ j, f j) / (m : ℝ)) * h x) =
        ((∑ j, f j) / (m : ℝ)) * (∑ x, h x) := by
      rw [← Finset.mul_sum]
    rw [hr, hleft, hright]
    field_simp
    <;> ring

private theorem cov_nonneg {m : ℕ} (f h : Fin m → ℝ) (hmono : Monovary f h) :
    0 ≤ centeredCovariance f h := by
  by_cases hm : m = 0
  · subst m
    simp [centeredCovariance]
  · have hm' : 0 < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    rw [cov_formula, sub_nonneg, div_le_iff₀ hm']
    simpa only [Fintype.card_fin, mul_comm] using hmono.sum_mul_sum_le_card_mul_sum

private theorem cov_sub_left {m : ℕ} (f f' h : Fin m → ℝ) :
    centeredCovariance (fun i => f i-f' i) h =
      centeredCovariance f h - centeredCovariance f' h := by
  simp only [cov_formula, sub_mul, sum_sub_distrib]
  ring

private theorem cov_sub_right {m : ℕ} (f h h' : Fin m → ℝ) :
    centeredCovariance f (fun i => h i-h' i) =
      centeredCovariance f h - centeredCovariance f h' := by
  simp only [cov_formula, mul_sub, sum_sub_distrib]
  ring

private theorem clock_monovary {m : ℕ} (A : Fin m → ℝ)
    (hA : ∀ i, 1 < A i) {f h : ℝ → ℝ}
    (hf : ∀ s t, 1 < s → s ≤ t → f s ≤ f t)
    (hh : ∀ s t, 1 < s → s ≤ t → h s ≤ h t) :
    Monovary (fun i => f (A i)) (fun i => h (A i)) := by
  intro i j hij
  by_cases hle : A i ≤ A j
  · exact hf _ _ (hA i) hle
  · have hji : A j ≤ A i := le_of_not_ge hle
    exact False.elim ((not_lt_of_ge (hh _ _ (hA j) hji)) hij)

private theorem gamma_nonneg {m : ℕ} (A : Fin m → ℝ) (hA : ∀ i, 1 < A i)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 0 ≤ Gamma A x y := by
  apply cov_nonneg
  exact clock_monovary A hA
    (fun _ _ hs hst => W_clock_mono hs hst hx)
    (fun _ _ hs hst => W_clock_mono hs hst hy)

private theorem gamma_decreasing {m : ℕ} (A : Fin m → ℝ) (hA : ∀ i, 1 < A i)
    {x y z : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    Gamma A y (y+z) ≤ Gamma A x (x+z) := by
  have hxz : 1 ≤ x+z := by linarith
  have hy : 1 ≤ y := hx.trans hxy
  have hyz : 1 ≤ y+z := by linarith
  have h1 : 0 ≤ centeredCovariance (fun i => W (A i) x-W (A i) y)
      (fun i => W (A i) (x+z)) := by
    apply cov_nonneg
    refine clock_monovary A hA
      (f := fun s => W s x - W s y)
      (h := fun s => W s (x+z)) ?_ ?_
    · intro s t hs hst
      have h := relative_decreasing hs hst hx hxy
      linarith
    · exact fun _ _ hs hst => W_clock_mono hs hst hxz
  have h2 : 0 ≤ centeredCovariance (fun i => W (A i) y)
      (fun i => W (A i) (x+z)-W (A i) (y+z)) := by
    apply cov_nonneg
    refine clock_monovary A hA
      (f := fun s => W s y)
      (h := fun s => W s (x+z) - W s (y+z)) ?_ ?_
    · exact fun _ _ hs hst => W_clock_mono hs hst hy
    · intro s t hs hst
      have h := relative_decreasing hs hst hxz (by linarith : x+z ≤ y+z)
      linarith
  rw [cov_sub_left] at h1
  rw [cov_sub_right] at h2
  unfold Gamma
  linarith

/-- Actual covariance signs and variation, and literal support, including m=0.
The decreasing differences follow from relative activation, not convexity of U. -/
private theorem actual_clock_covariance {m : ℕ} (A : Fin m → ℝ)
    (hA : ∀ i, 1 < A i) {b x y z : ℝ} (hAb : ∀ i, A i ≤ b)
    (hx : 1 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    0 ≤ Gamma A x (x+z) ∧
    0 ≤ Gamma A x (x+z) - Gamma A y (y+z) ∧
    (b ≤ 2*y → Gamma A y (y+z) = 0) := by
  refine ⟨gamma_nonneg A hA hx (by linarith),
    sub_nonneg.mpr (gamma_decreasing A hA hx hxy hz), ?_⟩
  intro hby
  unfold Gamma centeredCovariance
  have hzero : ∀ i, W (A i) y = 0 :=
    fun i => W_support (hA i) (hx.trans hxy) ((hAb i).trans hby)
  simp only [hzero, sum_const_zero, zero_div, sub_self, zero_mul, sum_const_zero]

/- The next three lemmas are finite-sum adapters of range variance and
Cauchy--Schwarz, consumed below. The analytic content is `relative_size`. -/
private theorem cov_translate {m : ℕ} (f h : Fin m → ℝ) (c d : ℝ) :
    centeredCovariance (fun i => f i-c) (fun i => h i-d) = centeredCovariance f h := by
  by_cases hm : m = 0
  · subst m; simp [centeredCovariance]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  unfold centeredCovariance
  apply sum_congr rfl
  intro i _
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring

private theorem finite_variance_le {m : ℕ} (f : Fin m → ℝ) {F : ℝ}
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ F) :
    centeredCovariance f f ≤ (m : ℝ)*F^2/4 := by
  by_cases hm : m = 0
  · subst m; simp [centeredCovariance]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hs : (∑ i, f i*f i) ≤ F*(∑ i, f i) := by
    rw [mul_sum]
    exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hf i).2 (hf i).1)
  have hs' := mul_le_mul_of_nonneg_left hs hmpos.le
  have heq : (m : ℝ)*centeredCovariance f f =
      (m : ℝ)*(∑ i, f i*f i) - (∑ i, f i)^2 := by
    rw [cov_formula]
    field_simp
    <;> ring
  have hsquare := sq_nonneg ((∑ i, f i)-(m : ℝ)*F/2)
  apply (mul_le_mul_iff_right₀ hmpos).mp
  nlinarith [heq]

private theorem finite_covariance_le {m : ℕ} (f h : Fin m → ℝ) {F H : ℝ}
    (hF : 0 ≤ F) (hH : 0 ≤ H)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ F) (hh : ∀ i, 0 ≤ h i ∧ h i ≤ H) :
    centeredCovariance f h ≤ (m : ℝ)*F*H/4 := by
  have hvf := finite_variance_le f hf
  have hvh := finite_variance_le h hh
  have hfv : 0 ≤ centeredCovariance f f := by
    unfold centeredCovariance
    exact sum_nonneg (fun i _ => mul_self_nonneg _)
  have hhv : 0 ≤ centeredCovariance h h := by
    unfold centeredCovariance
    exact sum_nonneg (fun i _ => mul_self_nonneg _)
  have hcs : (centeredCovariance f h)^2 ≤
      centeredCovariance f f * centeredCovariance h h := by
    simpa only [centeredCovariance, pow_two] using
      sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin m))
        (fun i => f i-(∑ j, f j)/(m : ℝ))
        (fun i => h i-(∑ j, h j)/(m : ℝ))
  have hp := mul_le_mul hvf hvh hhv (by positivity : 0 ≤ (m : ℝ)*F^2/4)
  have hr : 0 ≤ (m : ℝ)*F*H/4 := by positivity
  nlinarith [hcs.trans hp]

private theorem gamma_size {m : ℕ} (A : Fin m → ℝ) {a b x y : ℝ}
    (ha : 1 < a) (hAa : ∀ i, a ≤ A i) (hAb : ∀ i, A i ≤ b)
    (hab : a ≤ b) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Gamma A x y ≤ (m : ℝ)*(rangeBudget a b)^2/(4*x*y) := by
  have hK : 0 ≤ rangeBudget a b := by
    have h := relative_size (a := a) (b := b) ha le_rfl le_rfl hab (x := 1) le_rfl
    simpa using h
  have hf : ∀ i, 0 ≤ W (A i) x-W a x ∧
      W (A i) x-W a x ≤ rangeBudget a b/x := fun i =>
    ⟨sub_nonneg.mpr (W_clock_mono ha (hAa i) hx),
      relative_size ha le_rfl (hAa i) (hAb i) hx⟩
  have hh : ∀ i, 0 ≤ W (A i) y-W a y ∧
      W (A i) y-W a y ≤ rangeBudget a b/y := fun i =>
    ⟨sub_nonneg.mpr (W_clock_mono ha (hAa i) hy),
      relative_size ha le_rfl (hAa i) (hAb i) hy⟩
  have h := finite_covariance_le (fun i => W (A i) x-W a x)
    (fun i => W (A i) y-W a y) (div_nonneg hK (by linarith))
    (div_nonneg hK (by linarith)) hf hh
  rw [cov_translate] at h
  unfold Gamma
  convert h using 1
  field_simp
  <;> ring

private theorem actual_difference_range {a b B x y : ℝ}
    (ha : 1 < a) (haB : a ≤ B) (hBb : B ≤ b) (hx : 1 ≤ x) (hxy : x ≤ y) :
    0 ≤ (W B x-W B y)-(W a x-W a y) ∧
    (W B x-W B y)-(W a x-W a y) ≤ variationBudget a b*(1/x-1/y) := by
  have h := relative_variation (a := a) (A' := a) ha le_rfl haB hBb hx hxy
  constructor
  · linarith [h.1]
  · linarith [h.2]

private theorem gamma_variation {m : ℕ} (A : Fin m → ℝ) {a b x y z : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hAa : ∀ i, a ≤ A i) (hAb : ∀ i, A i ≤ b)
    (hx : 1 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    0 ≤ Gamma A x (x+z)-Gamma A y (y+z) ∧
    Gamma A x (x+z)-Gamma A y (y+z) ≤
      (m : ℝ)*rangeBudget a b*variationBudget a b/4 *
        (1/(x*(x+z))-1/(y*(y+z))) := by
  refine ⟨sub_nonneg.mpr (gamma_decreasing A (fun i => ha.trans_le (hAa i)) hx hxy hz), ?_⟩
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxz : 1 ≤ x+z := by linarith
  have hyz : 1 ≤ y+z := by linarith
  have hxz0 : 0 < x+z := by linarith
  have hyz0 : 0 < y+z := by linarith
  have hK : 0 ≤ rangeBudget a b := by
    have h := relative_size (a := a) (b := b) ha le_rfl le_rfl hab (x := 1) le_rfl
    simpa using h
  have hC : 0 ≤ variationBudget a b := by
    unfold variationBudget
    have hlog := Real.log_nonneg ((one_le_div (by linarith : 0 < a)).mpr hab)
    have hla := Real.log_pos ha
    exact mul_nonneg (by positivity) (by linarith)
  let u := 1/x-1/y
  let v := 1/(x+z)-1/(y+z)
  have hu : 0 ≤ u := sub_nonneg.mpr (one_div_le_one_div_of_le hx0 hxy)
  have hv : 0 ≤ v := sub_nonneg.mpr
    (one_div_le_one_div_of_le hxz0 (by linarith : x+z ≤ y+z))
  have hfirst : centeredCovariance (fun i => W (A i) x-W (A i) y)
      (fun i => W (A i) (x+z)) ≤
      (m : ℝ)*(variationBudget a b*u)*(rangeBudget a b/(x+z))/4 := by
    have h := finite_covariance_le
      (fun i => (W (A i) x-W (A i) y)-(W a x-W a y))
      (fun i => W (A i) (x+z)-W a (x+z))
      (mul_nonneg hC hu) (div_nonneg hK hxz0.le)
      (fun i => actual_difference_range ha (hAa i) (hAb i) hx hxy)
      (fun i => ⟨sub_nonneg.mpr (W_clock_mono ha (hAa i) hxz),
        relative_size ha le_rfl (hAa i) (hAb i) hxz⟩)
    rw [cov_translate] at h
    exact h
  have hsecond : centeredCovariance (fun i => W (A i) y)
      (fun i => W (A i) (x+z)-W (A i) (y+z)) ≤
      (m : ℝ)*(rangeBudget a b/y)*(variationBudget a b*v)/4 := by
    have h := finite_covariance_le
      (fun i => W (A i) y-W a y)
      (fun i => (W (A i) (x+z)-W (A i) (y+z))-(W a (x+z)-W a (y+z)))
      (div_nonneg hK hy0.le) (mul_nonneg hC hv)
      (fun i => ⟨sub_nonneg.mpr (W_clock_mono ha (hAa i) (hx.trans hxy)),
        relative_size ha le_rfl (hAa i) (hAb i) (hx.trans hxy)⟩)
      (fun i => actual_difference_range ha (hAa i) (hAb i) hxz
        (by linarith : x+z ≤ y+z))
    rw [cov_translate] at h
    exact h
  rw [cov_sub_left] at hfirst
  rw [cov_sub_right] at hsecond
  change Gamma A x (x+z)-Gamma A y (x+z) ≤ _ at hfirst
  change Gamma A y (x+z)-Gamma A y (y+z) ≤ _ at hsecond
  calc
    _ = (Gamma A x (x+z)-Gamma A y (x+z))+
        (Gamma A y (x+z)-Gamma A y (y+z)) := by ring
    _ ≤ (m : ℝ)*(variationBudget a b*u)*(rangeBudget a b/(x+z))/4+
        (m : ℝ)*(rangeBudget a b/y)*(variationBudget a b*v)/4 :=
      add_le_add hfirst hsecond
    _ = _ := by
      dsimp [u, v]
      field_simp [ne_of_gt hx0, ne_of_gt hy0, ne_of_gt hxz0, ne_of_gt hyz0] <;> ring


/-- The actual finite kernel's quantitative covariance envelope. Its range
bound is derived from the activation integral, not assumed as a premise.
The original sign, simultaneous decrease and support calculation is consumed
as a helper, with its full domain retained. -/
theorem actual_clock_quantitative {m : ℕ} (A : Fin m → ℝ)
    {a b x y z : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hAa : ∀ i, a ≤ A i) (hAb : ∀ i, A i ≤ b)
    (hx : 1 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    0 ≤ Gamma A x (x+z) ∧
    Gamma A x (x+z) ≤ (m : ℝ)*(rangeBudget a b)^2/(4*x*(x+z)) ∧
    0 ≤ Gamma A x (x+z)-Gamma A y (y+z) ∧
    Gamma A x (x+z)-Gamma A y (y+z) ≤
      (m : ℝ)*rangeBudget a b*variationBudget a b/4 *
        (1/(x*(x+z))-1/(y*(y+z))) ∧
    (b ≤ 2*y → Gamma A y (y+z) = 0) := by
  have hold := actual_clock_covariance A (fun i => ha.trans_le (hAa i)) hAb hx hxy hz
  exact ⟨hold.1, gamma_size A ha hAa hAb hab hx (by linarith), hold.2.1,
    (gamma_variation A ha hab hAa hAb hx hxy hz).2, hold.2.2⟩

end D5.S3.Arith.Robin.ActualRobinClockCovariance

#print axioms D5.S3.Arith.Robin.ActualRobinClockCovariance.actual_clock_quantitative
