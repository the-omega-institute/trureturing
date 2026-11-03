/- GID: D5/S3/Arith/Robin/OriginalMovingCutAggregate
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalMovingCutAggregate
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal moving-cut kernel retains its complete signed rows and measurable selection. -/

import D5.S3.Arith.Robin.OriginalMovingWindowMoment
import D5.S3.Arith.Robin.OriginalMovingCutRow
import D5.S3.Arith.Robin.OriginalMovingCutBudget
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open D5.S3.Arith.Robin.MellinWeightedVariation (weight)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g activationDensity)
open D5.S3.Arith.Robin.OriginalMovingWindowMoment
open D5.S3.Arith.Robin.OriginalMovingCutRow
open D5.S3.Arith.Robin.OriginalMovingCutBudget

-- Resolve the existing compiled private supplier without adding a theorem wrapper.
local macro "rowSupplier%" name:ident : term =>
  pure (Lean.mkIdent (((Lean.Name.num `_private.D5.S3.Arith.Robin.OriginalMovingCutRow 0).append
    `D5.S3.Arith.Robin.OriginalMovingCutRow).append name.getId))
-- Resolve the existing compiled private supplier without adding a theorem wrapper.
local macro "budgetSupplier%" name:ident : term =>
  pure (Lean.mkIdent (((Lean.Name.num `_private.D5.S3.Arith.Robin.OriginalMovingCutBudget 0).append
    `D5.S3.Arith.Robin.OriginalMovingCutBudget).append name.getId))

namespace D5.S3.Arith.Robin.OriginalMovingCutAggregate

private def cutLatticeTerm (ell R t : ℝ) (d m : ℕ) : ℝ :=
  if 1 ≤ d ∧ 1 ≤ m then
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
        ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
          beforeRatio ell R d ((d : ℝ) * m)))
  else 0

/-- The literal signed moving-cut contribution over every positive integer pair.
    Its finite support is derived from the original kernel. -/
def cutLattice (ell R : ℝ) (S : Set ℝ) : ℝ :=
  ∫ t in S, ∑' d : ℕ, ∑' m : ℕ, cutLatticeTerm ell R t d m

/-- The original time-dependent continuous divisor sum. -/
def divisorPosterior (t x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊t ^ (151 / 500 : ℝ)⌋₊,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (x / d) / d

/-- The kernel-weighted posterior on the complete reference interval;
    division at zero mass is the real zero convention. -/
def averagedPosterior (ell R x : ℝ) : ℝ :=
  (∫ s in Icc ell R, kernel s x * divisorPosterior s x) / windowMass ell R x

/-- The literal posterior correction, integrated on the original moving windows. -/
def cutPosterior (ell R : ℝ) (S : Set ℝ) : ℝ :=
  ∫ t in S, ∫ x in t..endpoint t,
    kernel t x * (divisorPosterior t x - averagedPosterior ell R x)

lemma measurable_kernel_joint : Measurable (fun p : ℝ × ℝ => kernel p.1 p.2) := by
  unfold kernel g weight endpoint width
  apply Measurable.ite
  · exact (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd
        (show Measurable (fun p : ℝ × ℝ => p.1 + p.1 ^ (4 / 5 : ℝ)) by fun_prop))
  · fun_prop
  · exact measurable_const

private lemma measurable_windowMass (ell R : ℝ) : Measurable (windowMass ell R) :=
  (measurable_kernel_joint.stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Icc ell R))).measurable

private lemma measurable_beforeMass (ell R : ℝ) (d : ℕ) :
    Measurable (beforeMass ell R d) :=
  (measurable_kernel_joint.stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Icc ell R ∩ Iio ((d : ℝ) ^ (500 / 151 : ℝ))))).measurable

private lemma measurable_beforeRatio (ell R : ℝ) (d : ℕ) :
    Measurable (beforeRatio ell R d) :=
  (measurable_beforeMass ell R d).div (measurable_windowMass ell R)

private lemma measurable_cutRow_joint (ell R : ℝ) (d : ℕ) :
    Measurable (fun p : ℝ × ℝ => cutRow ell R p.1 d p.2) := by
  unfold cutRow
  exact ((measurable_snd.div_const (d : ℝ)).log.mul measurable_kernel_joint).mul
    ((measurable_const.ite (measurableSet_lt measurable_fst measurable_const)
      measurable_const).sub ((measurable_beforeRatio ell R d).comp measurable_snd))

private lemma beforeRatio_bounds_all {ell R x : ℝ} (hell : 4 ≤ ell) (d : ℕ) :
    beforeRatio ell R d x ∈ Icc 0 1 := by
  have hK : 0 ≤ windowMass ell R x := by
    apply setIntegral_nonneg measurableSet_Icc
    intro s hs
    exact OriginalMovingCutRow.kernel_nonneg (hell.trans hs.1)
  rcases hK.eq_or_lt with hz | hp
  · simp [beforeRatio, ← hz]
  · exact (rowSupplier% beforeRatio_bounds) hell d hp

private lemma cutoff_indicator {t : ℝ} (ht : 0 ≤ t) {d : ℕ} (hd : 1 ≤ d) :
    d ≤ ⌊t ^ (151 / 500 : ℝ)⌋₊ ↔ ¬t < (d : ℝ) ^ (500 / 151 : ℝ) := by
  rw [Nat.le_floor_iff (Real.rpow_nonneg ht _), not_lt]
  constructor
  · intro h
    calc
      (d : ℝ) ^ (500 / 151 : ℝ) ≤
          (t ^ (151 / 500 : ℝ)) ^ (500 / 151 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg d) h (by norm_num)
      _ = t := by rw [← Real.rpow_mul ht]; norm_num
  · intro h
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg d) _) h
      (by norm_num : (0 : ℝ) ≤ 151 / 500)
    simpa only [← Real.rpow_mul (Nat.cast_nonneg d),
      show (500 / 151 : ℝ) * (151 / 500 : ℝ) = 1 by norm_num,
      Real.rpow_one] using hh

private lemma posterior_fixed_sum {R t x : ℝ} (ht : 256 ≤ t) (htR : t ≤ R) :
    divisorPosterior t x = ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (x / d) / d *
        (1 - if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) := by
  have hsmall : t ^ (151 / 500 : ℝ) ≤ 2 * R :=
    (Real.rpow_le_self_of_one_le (by linarith) (by norm_num)).trans (by linarith)
  have hsub : Finset.Icc 1 ⌊t ^ (151 / 500 : ℝ)⌋₊ ⊆ Finset.Icc 1 ⌊2 * R⌋₊ := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (Nat.floor_mono hsmall)⟩
  unfold divisorPosterior
  calc
    _ = ∑ d ∈ Finset.Icc 1 ⌊t ^ (151 / 500 : ℝ)⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (x / d) / d *
          (1 - if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' := Finset.mem_Icc.mp hd
      simp [(cutoff_indicator (by linarith) hd'.1).mp hd'.2]
    _ = _ := Finset.sum_subset hsub (by
      intro d hd hnot
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hcut : t < (d : ℝ) ^ (500 / 151 : ℝ) := by
        by_contra h
        exact hnot (Finset.mem_Icc.mpr ⟨hd1,
          (cutoff_indicator (by linarith) hd1).mpr h⟩)
      simp [hcut])

private lemma cutRow_integral_fixed {ell R t : ℝ}
    (hell : 256 ≤ ell) (ht : t ∈ Icc ell R) (d : ℕ) :
    (∫ x in t..endpoint t, cutRow ell R t d x) =
      ∫ x in Icc 0 (2 * R), cutRow ell R t d x := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg ht0 _)
  have hb : endpoint t ≤ 2 * R := ((rowSupplier% endpoint_le_twice) (by linarith [ht.1])).trans (by linarith [ht.2])
  rw [intervalIntegral.integral_of_le htb]
  symm
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Icc.nullMeasurableSet
  · intro x hx
    exact ⟨ht0.trans hx.1.le, hx.2.trans hb⟩
  · filter_upwards [] with x hx
    apply (budgetSupplier% cutRow_zero_of_outside) d
    by_cases hxt : x ≤ t
    · exact Or.inl hxt
    · exact Or.inr (le_of_lt (lt_of_not_ge (by
        intro hxb
        exact hx.2 ⟨not_le.mp hxt, hxb⟩)))

private lemma averagedPosterior_fixed_sum {ell R x : ℝ} (hell : 256 ≤ ell)
    (hK : windowMass ell R x ≠ 0) :
    averagedPosterior ell R x = ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (x / d) / d *
        (1 - beforeRatio ell R d x) := by
  let A : ℕ → ℝ := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    Real.log (x / d) / d
  have hi : IntegrableOn (fun s => kernel s x) (Icc ell R) :=
    OriginalMovingCutRow.kernel_integrableOn (by linarith)
  have hj : ∀ d : ℕ, IntegrableOn (fun s => kernel s x *
      (if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) (Icc ell R) := by
    intro d
    have heq : (fun s => kernel s x *
        (if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) =
        (Iio ((d : ℝ) ^ (500 / 151 : ℝ))).indicator (fun s => kernel s x) := by
      funext s
      simp only [Set.indicator, mem_Iio]
      split_ifs <;> simp
    rw [heq]
    exact hi.indicator measurableSet_Iio
  have hrow : ∀ d : ℕ, IntegrableOn (fun s => kernel s x *
      (1 - if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) (Icc ell R) := by
    intro d
    simp_rw [mul_sub, mul_one]
    exact hi.sub (hj d)
  have hbefore : ∀ d : ℕ, (∫ s in Icc ell R, kernel s x *
      (if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) = beforeMass ell R d x := by
    intro d
    unfold beforeMass
    rw [← setIntegral_indicator measurableSet_Iio]
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [Set.indicator, mem_Iio]
    split_ifs <;> simp
  have hsplit : ∀ d : ℕ, (∫ s in Icc ell R, kernel s x *
      (1 - if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) =
        windowMass ell R x - beforeMass ell R d x := by
    intro d
    simp_rw [mul_sub, mul_one]
    rw [integral_sub hi (hj d), hbefore]
    rfl
  unfold averagedPosterior
  have hexpand : (∫ s in Icc ell R, kernel s x * divisorPosterior s x) =
      ∫ s in Icc ell R, ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        A d * (kernel s x * (1 - if s < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    rw [posterior_fixed_sum (hell.trans hs.1) hs.2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    dsimp [A]
    ring
  rw [hexpand, integral_finsetSum _ (fun d _ => (hrow d).const_mul (A d))]
  simp_rw [integral_const_mul, hsplit, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  dsimp [A, beforeRatio]
  field_simp [hK]

private lemma posterior_weighted_identity {ell R t : ℝ}
    (hell : 256 ≤ ell) (horder : ell < R) (ht : t ∈ Icc ell R) (x : ℝ) :
    kernel t x * (divisorPosterior t x - averagedPosterior ell R x) =
      -∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * cutRow ell R t d x / d := by
  by_cases hz : kernel t x = 0
  · simp [hz, cutRow]
  have hk : 0 < kernel t x := lt_of_le_of_ne (OriginalMovingCutRow.kernel_nonneg (by linarith [ht.1]))
    (Ne.symm hz)
  have hK := (rowSupplier% windowMass_pos_of_kernel_pos) (by linarith) horder ht hk
  rw [posterior_fixed_sum (hell.trans ht.1) ht.2,
    averagedPosterior_fixed_sum hell hK.ne', ← Finset.sum_sub_distrib,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold cutRow
  ring

private lemma cutRow_uniform_bound {ell R t : ℝ} (hell : 256 ≤ ell)
    (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d) (x : ℝ) :
    ‖cutRow ell R t d x‖ ≤ Real.log (2 * R) + Real.log d := by
  have ht4 : 4 ≤ t := by linarith [ht.1]
  have hR : 1 ≤ 2 * R := by linarith [ht.1, ht.2]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hC : 0 ≤ Real.log (2 * R) + Real.log d :=
    add_nonneg (Real.log_nonneg hR) hlogd
  by_cases hz : kernel t x = 0
  · simpa [cutRow, hz] using hC
  have hk := ((rowSupplier% kernel_pos_iff) ht4).mp
    (lt_of_le_of_ne (OriginalMovingCutRow.kernel_nonneg ht4) (Ne.symm hz))
  have hx0 : 0 < x := by linarith [ht.1, hk.1]
  have hxR : x ≤ 2 * R := hk.2.le.trans
    (((rowSupplier% endpoint_le_twice) (by linarith)).trans (by linarith [ht.2]))
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith [ht.1, hk.1])
  have hlogupper := Real.log_le_log hx0 hxR
  have hl : |Real.log (x / d)| ≤ Real.log (2 * R) + Real.log d := by
    rw [Real.log_div hx0.ne' hd0.ne', abs_le]
    constructor <;> linarith
  have hr := beforeRatio_bounds_all (ell := ell) (R := R) (x := x) (by linarith) d
  have hc : |(if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
      beforeRatio ell R d x| ≤ 1 := by
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith [hr.1, hr.2]
  rw [Real.norm_eq_abs, cutRow, abs_mul, abs_mul,
    abs_of_nonneg (OriginalMovingCutRow.kernel_nonneg ht4)]
  calc
    _ ≤ (Real.log (2 * R) + Real.log d) * 1 * 1 := by
      gcongr <;> first | exact OriginalMovingCutRow.kernel_le_one ht4 | exact OriginalMovingCutRow.kernel_nonneg ht4
    _ = _ := by ring

private lemma cutRow_integrable_fixed {ell R t : ℝ} (hell : 256 ≤ ell)
    (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d) :
    IntegrableOn (cutRow ell R t d) (Icc 0 (2 * R)) := by
  apply (integrableOn_const (C := Real.log (2 * R) + Real.log d) isCompact_Icc.measure_ne_top).mono'
    (((measurable_cutRow_joint ell R d).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [] with x
  exact cutRow_uniform_bound hell ht hd x

private lemma cutRow_intervalIntegrable {ell R t : ℝ} (hell : 256 ≤ ell)
    (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d) :
    IntervalIntegrable (cutRow ell R t d) volume t (endpoint t) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show t ≤ endpoint t from
      le_add_of_nonneg_right (Real.rpow_nonneg (by linarith [ht.1]) _))).2
  apply (cutRow_integrable_fixed hell ht hd).mono_set
  intro x hx
  exact ⟨le_trans (by linarith [ht.1]) hx.1.le, hx.2.trans
    (((rowSupplier% endpoint_le_twice) (by linarith [ht.1])).trans (by linarith [ht.2]))⟩

private lemma cutRow_integral_integrableOn {ell R : ℝ} (hell : 256 ≤ ell)
    {d : ℕ} (hd : 1 ≤ d) :
    IntegrableOn (fun t => ∫ x in t..endpoint t, cutRow ell R t d x) (Icc ell R) := by
  have hm : Measurable (fun t => ∫ x in Icc 0 (2 * R), cutRow ell R t d x) :=
    ((measurable_cutRow_joint ell R d).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Icc 0 (2 * R)))).measurable
  have hi : IntegrableOn (fun t => ∫ x in Icc 0 (2 * R), cutRow ell R t d x)
      (Icc ell R) := by
    apply (integrableOn_const
      (C := (Real.log (2 * R) + Real.log d) * (volume (Icc 0 (2 * R))).toReal)
      (by simp)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
      (fun x _ => cutRow_uniform_bound hell ht hd x)
  apply hi.congr_fun (fun t ht => (cutRow_integral_fixed hell ht d).symm)
    measurableSet_Icc

private def latticePart (ell R t : ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
    Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
      ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
        beforeRatio ell R d ((d : ℝ) * m))

private lemma latticePart_eq {ell R t : ℝ} {d : ℕ} (hd : 1 ≤ d) :
    latticePart ell R t d = ∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
      cutRow ell R t d ((d : ℝ) * m) := by
  apply Finset.sum_congr rfl
  intro m _
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  simp only [cutRow, mul_div_cancel_left₀ _ hd0]

private lemma cutLatticeTerm_zero_past_support {ell R t : ℝ} (hell : 256 ≤ ell)
    (ht : t ∈ Icc ell R) {d m : ℕ} (hN : ⌊2 * R⌋₊ < d * m) :
    cutLatticeTerm ell R t d m = 0 := by
  have hx : 2 * R < (d : ℝ) * m := by
    simpa only [Nat.cast_mul] using
      (Nat.floor_lt (show (0 : ℝ) ≤ 2 * R by linarith [ht.1, ht.2])).mp hN
  have hb : endpoint t ≤ (d : ℝ) * m :=
    (((rowSupplier% endpoint_le_twice) (by linarith [ht.1])).trans (by linarith [ht.2])).trans hx.le
  simp [cutLatticeTerm, (rowSupplier% kernel_zero_of_outside) (Or.inr hb)]

private lemma cutLattice_full_sum {ell R t : ℝ} (hell : 256 ≤ ell)
    (ht : t ∈ Icc ell R) :
    (∑' d : ℕ, ∑' m : ℕ, cutLatticeTerm ell R t d m) =
      ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticePart ell R t d := by
  have hout : ∀ d ∉ Finset.Icc 1 ⌊2 * R⌋₊,
      (∑' m : ℕ, cutLatticeTerm ell R t d m) = 0 := by
    intro d hd
    have hz : (fun m : ℕ => cutLatticeTerm ell R t d m) = fun _ => 0 := by
      funext m
      by_cases hd1 : 1 ≤ d
      · by_cases hm1 : 1 ≤ m
        · apply cutLatticeTerm_zero_past_support hell ht
          have hNd : ⌊2 * R⌋₊ < d := by
            by_contra h
            exact hd (Finset.mem_Icc.mpr ⟨hd1, not_lt.mp h⟩)
          exact hNd.trans_le (by nlinarith)
        · simp [cutLatticeTerm, hm1]
      · simp [cutLatticeTerm, hd1]
    rw [hz, tsum_zero]
  rw [tsum_eq_sum hout]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hinner : (∑' m : ℕ, cutLatticeTerm ell R t d m) =
      ∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d), cutLatticeTerm ell R t d m := by
    apply tsum_eq_sum
    intro m hm
    by_cases hm1 : 1 ≤ m
    · apply cutLatticeTerm_zero_past_support hell ht
      have hmN : ¬m ≤ ⌊2 * R⌋₊ / d := by
        intro h
        exact hm (Finset.mem_Icc.mpr ⟨hm1, h⟩)
      have hmul : ¬m * d ≤ ⌊2 * R⌋₊ := by
        intro h
        exact hmN ((Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr h)
      simpa only [Nat.mul_comm] using lt_of_not_ge hmul
    · simp [cutLatticeTerm, hm1]
  rw [hinner]
  unfold latticePart
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [cutLatticeTerm, if_pos ⟨hd1, (Finset.mem_Icc.mp hm).1⟩]

private lemma latticePart_integrableOn {ell R : ℝ} (hell : 256 ≤ ell)
    {d : ℕ} (hd : 1 ≤ d) : IntegrableOn (fun t => latticePart ell R t d) (Icc ell R) := by
  simp_rw [latticePart_eq hd]
  apply integrable_finsetSum
  intro m _
  apply (integrableOn_const (C := Real.log (2 * R) + Real.log d)
    isCompact_Icc.measure_ne_top).mono'
    (((measurable_cutRow_joint ell R d).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact cutRow_uniform_bound hell ht hd _

private lemma posterior_integral_identity {ell R t : ℝ}
    (hell : 256 ≤ ell) (horder : ell < R) (ht : t ∈ Icc ell R) :
    (∫ x in t..endpoint t,
      kernel t x * (divisorPosterior t x - averagedPosterior ell R x)) =
        -(∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            (∫ x in t..endpoint t, cutRow ell R t d x) / d) := by
  have heq : (fun x => kernel t x *
      (divisorPosterior t x - averagedPosterior ell R x)) =
      fun x => -(∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * cutRow ell R t d x / d) := by
    funext x
    exact posterior_weighted_identity hell horder ht x
  rw [heq, intervalIntegral.integral_neg, intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  · intro d hd
    exact ((cutRow_intervalIntegrable hell ht (Finset.mem_Icc.mp hd).1).const_mul _).div_const _

private lemma cut_aggregate_identity {ell R : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    {S : Set ℝ} (hS : MeasurableSet S) (hSJ : S ⊆ Icc ell R) :
    cutLattice ell R S + cutPosterior ell R S =
      ∫ t in S, ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d := by
  let A : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticePart ell R t d
  let B : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (∫ x in t..endpoint t, cutRow ell R t d x) / d
  have hAJ : IntegrableOn A (Icc ell R) := by
    dsimp [A]
    exact integrable_finsetSum _ (fun d hd =>
      (latticePart_integrableOn hell (Finset.mem_Icc.mp hd).1).const_mul _)
  have hBJ : IntegrableOn B (Icc ell R) := by
    dsimp [B]
    exact integrable_finsetSum _ (fun d hd =>
      ((cutRow_integral_integrableOn hell (Finset.mem_Icc.mp hd).1).const_mul _).div_const _)
  have hA : IntegrableOn A S := hAJ.mono_set hSJ
  have hB : IntegrableOn B S := hBJ.mono_set hSJ
  have hP : cutPosterior ell R S = -(∫ t in S, B t) := by
    unfold cutPosterior
    rw [← integral_neg]
    apply setIntegral_congr_fun hS
    intro t ht
    dsimp [B]
    exact posterior_integral_identity hell horder (hSJ ht)
  have hC : cutLattice ell R S = ∫ t in S, A t := by
    unfold cutLattice
    apply setIntegral_congr_fun hS
    intro t ht
    dsimp [A]
    exact cutLattice_full_sum hell (hSJ ht)
  rw [hC, hP, ← sub_eq_add_neg, ← integral_sub hA hB]
  apply setIntegral_congr_fun hS
  intro t _
  dsimp [A, B]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  change _ = _ * (latticePart ell R t d - _)
  ring

private lemma row_zero_past_cutoff {ell R t : ℝ} (hell : 256 ≤ ell)
    (horder : ell < R) (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d)
    (hcut : ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊ < d) :
    latticeRowRemainder ell R t d = 0 := by
  apply (budgetSupplier% latticeRowRemainder_zero_of_cutRow) hd
  funext x
  apply (budgetSupplier% cutRow_zero_above) hell horder ht _ x
  have hB : 0 ≤ endpoint t := by
    have hw := Real.rpow_nonneg (by linarith [ht.1] : 0 ≤ t) (4 / 5 : ℝ)
    dsimp [endpoint, width]
    linarith [ht.1]
  exact ((Nat.floor_lt (Real.rpow_nonneg hB _)).mp hcut).le

private lemma signed_cut_bound {ell R t : ℝ} (hell : 256 ≤ ell)
    (horder : ell < R) (ht : t ∈ Icc ell R) :
    |∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d| ≤
        6 * t ^ (-99 / 500 : ℝ) * Real.log (2 * t) := by
  have hB : 1 ≤ endpoint t := by
    have hw := Real.rpow_nonneg (by linarith [ht.1] : 0 ≤ t) (4 / 5 : ℝ)
    dsimp [endpoint, width]
    linarith [ht.1]
  have hsmall : endpoint t ^ (151 / 500 : ℝ) ≤ 2 * R :=
    (Real.rpow_le_self_of_one_le hB (by norm_num)).trans
      (((rowSupplier% endpoint_le_twice) (by linarith [ht.1])).trans (by linarith [ht.2]))
  have hsub : Finset.Icc 1 ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊ ⊆
      Finset.Icc 1 ⌊2 * R⌋₊ := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (Nat.floor_mono hsmall)⟩
  have heq : (∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |latticeRowRemainder ell R t d|) =
      ∑ d ∈ Finset.Icc 1 ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |latticeRowRemainder ell R t d| := by
    symm
    apply Finset.sum_subset hsub
    intro d hd hnot
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hcut : ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊ < d := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨hd1, not_lt.mp h⟩)
    rw [row_zero_past_cutoff hell horder ht hd1 hcut, abs_zero, mul_zero]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          |latticeRowRemainder ell R t d| := by simp_rw [abs_mul]
    _ ≤ _ := by rw [heq]; exact original_cut_row_pointwise_budget hell horder ht

private lemma log_power_antitone :
    AntitoneOn (fun t : ℝ => t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) (Ici 256) := by
  have hbase : 500 / 99 < Real.log (512 : ℝ) := by
    have heq := Real.log_pow (2 : ℝ) 9
    norm_num at heq
    linarith [Real.log_two_gt_d9]
  have hD : ∀ x ∈ Ici (256 : ℝ), HasDerivAt
      (fun t : ℝ => t ^ (-99 / 500 : ℝ) * Real.log (2 * t))
      (x ^ (-99 / 500 - 1 : ℝ) * (1 - 99 / 500 * Real.log (2 * x))) x := by
    intro x hx
    change 256 ≤ x at hx
    have hx0 : 0 < x := by linarith
    have hp : x ^ (-99 / 500 : ℝ) = x ^ (-99 / 500 - 1 : ℝ) * x := by
      calc
        _ = x ^ ((-99 / 500 - 1 : ℝ) + 1) := by congr 1; norm_num
        _ = _ := by rw [Real.rpow_add hx0, Real.rpow_one]
    convert ((Real.hasDerivAt_rpow_const (p := (-99 / 500 : ℝ)) (Or.inl hx0.ne')).mul
      ((Real.hasDerivAt_log (by positivity : 2 * x ≠ 0)).comp x
        ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)))) using 1
    <;> first | rfl | (rw [hp]; field_simp; ring_nf; simp only [Function.comp_apply, mul_comm])
  have hn : ∀ x ∈ Ici (256 : ℝ),
      x ^ (-99 / 500 - 1 : ℝ) * (1 - 99 / 500 * Real.log (2 * x)) ≤ 0 := by
    intro x hx
    change 256 ≤ x at hx
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 512)
      (show (512 : ℝ) ≤ 2 * x by linarith [hx])
    apply mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith [hx]) _)
    linarith
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (HasDerivAt.continuousOn hD)
    (fun x hx => (hD x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hn x (interior_subset hx))

/-- The original lattice cut and posterior cut have the complete finite-Fubini
    identity and an arbitrary-measurable-set bound with the original volume. -/
theorem original_cut_aggregate_estimate {ell R : ℝ} (hell : 256 ≤ ell)
    (horder : ell < R) {S : Set ℝ} (hS : MeasurableSet S) (hSJ : S ⊆ Icc ell R)
    (hM : 0 < (volume S).toReal) :
    cutLattice ell R S + cutPosterior ell R S =
        (∫ t in S, ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d) ∧
    |cutLattice ell R S + cutPosterior ell R S| ≤
        6 * (∫ t in S, t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) ∧
    6 * (∫ t in S, t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) ≤
        6 * (volume S).toReal * ell ^ (-99 / 500 : ℝ) * Real.log (2 * ell) := by
  have hid := cut_aggregate_identity hell horder hS hSJ
  have hfin : volume S ≠ ⊤ := ne_top_of_le_ne_top isCompact_Icc.measure_ne_top
    (measure_mono hSJ)
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-99 / 500 : ℝ) * Real.log (2 * t))
      (Icc ell R) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun t ht => Or.inl (by
        change t ≠ 0
        linarith [ht.1]))
    · exact (continuousOn_const.mul continuousOn_id).log
        (fun t ht => by change 2 * t ≠ 0; linarith [ht.1])
  have hi : IntegrableOn (fun t : ℝ => t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) S :=
    (hcont.integrableOn_Icc).mono_set hSJ
  refine ⟨hid, ?_, ?_⟩
  · rw [hid]
    have hb := norm_integral_le_of_norm_le
      (f := fun t => ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d)
      (hi.const_mul 6) (by
      filter_upwards [ae_restrict_mem hS] with t ht
      rw [Real.norm_eq_abs]
      simpa only [mul_assoc] using signed_cut_bound hell horder (hSJ ht))
    simpa only [Real.norm_eq_abs, integral_const_mul] using hb
  · have hle : (∫ t in S, t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) ≤
        (volume S).toReal * (ell ^ (-99 / 500 : ℝ) * Real.log (2 * ell)) := by
      calc
        _ ≤ ∫ _t in S, ell ^ (-99 / 500 : ℝ) * Real.log (2 * ell) :=
          setIntegral_mono_on hi (integrableOn_const hfin) hS (fun t ht =>
            log_power_antitone hell (hell.trans (hSJ ht).1) (hSJ ht).1)
        _ = _ := by rw [setIntegral_const, smul_eq_mul]; rfl
    nlinarith


end D5.S3.Arith.Robin.OriginalMovingCutAggregate
