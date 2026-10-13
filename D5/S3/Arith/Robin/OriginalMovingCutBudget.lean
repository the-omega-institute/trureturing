/- GID: D5/S3/Arith/Robin/OriginalMovingCutBudget
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalMovingCutBudget
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal moving-cut kernel retains its complete signed rows and measurable selection. -/

import D5.S3.Arith.Robin.OriginalMovingWindowMoment
import D5.S3.Arith.Robin.OriginalMovingCutRow
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

-- Resolve the existing compiled private supplier without adding a theorem wrapper.
local macro "rowSupplier%" name:ident : term =>
  pure (Lean.mkIdent (((Lean.Name.num `_private.D5.S3.Arith.Robin.OriginalMovingCutRow 0).append
    `D5.S3.Arith.Robin.OriginalMovingCutRow).append name.getId))

namespace D5.S3.Arith.Robin.OriginalMovingCutBudget

/-- The complete positive cofactor row with its signed continuum compensation. -/
def latticeRowRemainder (ell R t : ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
    Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
      ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
        beforeRatio ell R d ((d : ℝ) * m))) -
      (∫ x in t..endpoint t, cutRow ell R t d x) / d

private lemma cutRow_zero_of_outside {ell R t x : ℝ} (d : ℕ)
    (hx : x ≤ t ∨ endpoint t ≤ x) : cutRow ell R t d x = 0 := by
  simp only [cutRow, (rowSupplier% kernel_zero_of_outside) hx, mul_zero, zero_mul]

private lemma cutRow_integral_full_grid {ell R t L : ℝ} {d : ℕ}
    (ht0 : 0 ≤ t) (hL : endpoint t ≤ L)
    (hf : BoundedVariationOn (cutRow ell R t d) univ) :
    (∫ x in 0..L, cutRow ell R t d x) = ∫ x in t..endpoint t, cutRow ell R t d x := by
  have hleft : (∫ x in 0..t, cutRow ell R t d x) = 0 := by
    rw [intervalIntegral.integral_of_le ht0]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact cutRow_zero_of_outside d (Or.inl hx.2)
  have hright : (∫ x in endpoint t..L, cutRow ell R t d x) = 0 := by
    rw [intervalIntegral.integral_of_le hL]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact cutRow_zero_of_outside d (Or.inr hx.1.le)
  rw [← intervalIntegral.integral_add_adjacent_intervals
      ((rowSupplier% boundedVariation_intervalIntegrable) hf 0 t) ((rowSupplier% boundedVariation_intervalIntegrable) hf t L),
    ← intervalIntegral.integral_add_adjacent_intervals
      ((rowSupplier% boundedVariation_intervalIntegrable) hf t (endpoint t))
      ((rowSupplier% boundedVariation_intervalIntegrable) hf (endpoint t) L), hleft, hright]
  simp


private lemma cutRow_zero_above {ell R t : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    (ht : t ∈ Icc ell R) {d : ℕ}
    (hd : endpoint t ^ (151 / 500 : ℝ) ≤ (d : ℝ)) (x : ℝ) :
    cutRow ell R t d x = 0 := by
  have ht4 : 4 ≤ t := by linarith [ht.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hB : 0 < endpoint t := ht0.trans_le
    (le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _))
  have hclock : endpoint t ≤ (d : ℝ) ^ (500 / 151 : ℝ) := by
    calc
      endpoint t = (endpoint t ^ (151 / 500 : ℝ)) ^ (500 / 151 : ℝ) := by
        rw [← Real.rpow_mul hB.le]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hB.le _) hd (by norm_num)
  by_cases hz : kernel t x = 0
  · simp [cutRow, hz]
  have hk : 0 < kernel t x := lt_of_le_of_ne ((rowSupplier% kernel_nonneg) ht4) (Ne.symm hz)
  have hx := ((rowSupplier% kernel_pos_iff) ht4).mp hk
  have hK := (rowSupplier% windowMass_pos_of_kernel_pos) (by linarith : 4 ≤ ell) horder ht hk
  have hlate : (rowSupplier% afterMass) ell R d x = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    exact (rowSupplier% kernel_zero_of_outside) (Or.inl
      (hx.2.le.trans (hclock.trans (not_lt.mp hs.2))))
  have hratio : beforeRatio ell R d x = 1 := by
    have hN : beforeMass ell R d x = windowMass ell R x := by
      have hsplit : beforeMass ell R d x + (rowSupplier% afterMass) ell R d x =
          windowMass ell R x := (rowSupplier% mass_split) (by linarith : 4 ≤ ell) d
      linarith [hsplit]
    unfold beforeRatio
    rw [hN, div_self hK.ne']
  have hactive : t < (d : ℝ) ^ (500 / 151 : ℝ) :=
    (lt_add_of_pos_right t (Real.rpow_pos_of_pos ht0 (4 / 5 : ℝ))).trans_le hclock
  simp [cutRow, hratio, hactive]

/- The lower crossing clock is used only as a support cutoff.  It is deliberately
   defined by the explicit inequality `u+u^(4/5)≤t`; no inverse selection is
   introduced into the original family. -/
private def lowerClock (t : ℝ) : ℝ := t - width t

private lemma width_le_third {t : ℝ} (ht : 256 ≤ t) : width t ≤ t / 3 := by
  have ht0 : 0 < t := by linarith
  have ht243 : (243 : ℝ) ≤ t := by linarith
  have hpow := Real.rpow_le_rpow (show 0 ≤ (243 : ℝ) by norm_num) ht243
    (show 0 ≤ (1 / 5 : ℝ) by norm_num)
  have hthree : (3 : ℝ) ≤ t ^ (1 / 5 : ℝ) := by
    convert hpow using 1
    · rw [show (243 : ℝ) = 3 ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
  have hdecomp : t = t ^ (4 / 5 : ℝ) * t ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_add ht0]
    norm_num
  unfold width
  have hmul := mul_le_mul_of_nonneg_left hthree
    (Real.rpow_nonneg ht0.le (4 / 5 : ℝ))
  rw [← hdecomp] at hmul
  nlinarith

private lemma lowerClock_bounds {t : ℝ} (ht : 256 ≤ t) :
    0 < lowerClock t ∧ 2 * t / 3 ≤ lowerClock t ∧ lowerClock t ≤ t := by
  have ht0 : 0 < t := by linarith
  have hw := width_le_third ht
  have hwn : 0 ≤ width t := by
    unfold width
    positivity
  unfold lowerClock
  constructor
  · linarith
  constructor
  · linarith
  · linarith

private lemma lowerClock_endpoint_le {t : ℝ} (ht : 256 ≤ t) :
    endpoint (lowerClock t) ≤ t := by
  have hu := lowerClock_bounds ht
  have hw := width_le_third ht
  have hpow : width (lowerClock t) ≤ width t := by
    unfold width
    exact Real.rpow_le_rpow hu.1.le hu.2.2 (by norm_num)
  unfold endpoint
  dsimp [lowerClock] at *
  linarith

private lemma lowerClock_rpow_cutoff {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ lowerClock t ^ (151 / 500 : ℝ)) :
    (d : ℝ) ^ (500 / 151 : ℝ) ≤ lowerClock t := by
  have hu := lowerClock_bounds ht
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hpow := Real.rpow_le_rpow (show 0 ≤ (d : ℝ) by linarith)
    hcut (show 0 ≤ (500 / 151 : ℝ) by norm_num)
  have hright : (lowerClock t ^ (151 / 500 : ℝ)) ^ (500 / 151 : ℝ) = lowerClock t := by
    rw [← Real.rpow_mul hu.1.le]
    norm_num
  rw [hright] at hpow
  exact hpow

private lemma cutRow_zero_below {ell R t : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d)
    (hcut : (d : ℝ) ≤ lowerClock t ^ (151 / 500 : ℝ)) (x : ℝ) :
    cutRow ell R t d x = 0 := by
  have ht4 : 4 ≤ t := by linarith [hell, ht.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hτ := lowerClock_rpow_cutoff (hell.trans ht.1) hd hcut
  have hu := lowerClock_bounds (hell.trans ht.1)
  have hclock : endpoint ((d : ℝ) ^ (500 / 151 : ℝ)) ≤ t := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hτ1 : (1 : ℝ) ≤ (d : ℝ) ^ (500 / 151 : ℝ) :=
      Real.one_le_rpow hd1 (by norm_num)
    have hu1 : (1 : ℝ) ≤ lowerClock t := by linarith [hu.2.1]
    exact ((rowSupplier% endpoint_strictMonoOn).monotoneOn hτ1 hu1 hτ).trans
      (lowerClock_endpoint_le (hell.trans ht.1))
  by_cases hz : kernel t x = 0
  · simp [cutRow, hz]
  have hk : 0 < kernel t x := lt_of_le_of_ne ((rowSupplier% kernel_nonneg) ht4) (Ne.symm hz)
  have hx := ((rowSupplier% kernel_pos_iff) ht4).mp hk
  have hlate : beforeMass ell R d x = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    apply (rowSupplier% kernel_zero_of_outside)
    right
    have hsτ : s < (d : ℝ) ^ (500 / 151 : ℝ) := hs.2
    have hs1 : (1 : ℝ) ≤ s := by linarith [hell, hs.1.1]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hτ1 : (1 : ℝ) ≤ (d : ℝ) ^ (500 / 151 : ℝ) :=
      Real.one_le_rpow hd1 (by norm_num)
    have hse : endpoint s ≤ endpoint ((d : ℝ) ^ (500 / 151 : ℝ)) :=
      (rowSupplier% endpoint_strictMonoOn).monotoneOn hs1 hτ1 (le_of_lt hsτ)
    exact (hse.trans_lt (hclock.trans_lt hx.1)).le
  have hratio : beforeRatio ell R d x = 0 := by
    unfold beforeRatio
    rw [hlate, zero_div]
  have hactive : ¬ t < (d : ℝ) ^ (500 / 151 : ℝ) := by
    exact not_lt_of_ge (hτ.trans hu.2.2)
  simp [cutRow, hratio, hactive]

private lemma crossing_width_bound {t : ℝ} (ht : 256 ≤ t) :
    endpoint t ^ (151 / 500 : ℝ) - lowerClock t ^ (151 / 500 : ℝ) ≤
      (151 / 125 : ℝ) * t ^ (51 / 500 : ℝ) := by
  let a : ℝ := 151 / 500
  have ht0 : 0 < t := by linarith
  have hu := lowerClock_bounds ht
  have hlow0 : 0 < lowerClock t := hu.1
  have hB0 : 0 < endpoint t := by
    dsimp [endpoint, width]
    positivity
  have hdelta : 0 ≤ endpoint t - lowerClock t := by
    dsimp [endpoint, lowerClock, width]
    ring_nf
    positivity
  have hq : 0 ≤ (endpoint t - lowerClock t) / lowerClock t :=
    div_nonneg hdelta hlow0.le
  have hrepr : endpoint t = lowerClock t *
      (1 + (endpoint t - lowerClock t) / lowerClock t) := by
    field_simp [hlow0.ne']
    ring
  have hbern := rpow_one_add_le_one_add_mul_self (s :=
      (endpoint t - lowerClock t) / lowerClock t) (by linarith) (by norm_num : 0 ≤ a)
      (by norm_num : a ≤ 1)
  have hBpow : endpoint t ^ a = lowerClock t ^ a *
      (1 + (endpoint t - lowerClock t) / lowerClock t) ^ a := by
    calc
      _ = (lowerClock t *
          (1 + (endpoint t - lowerClock t) / lowerClock t)) ^ a :=
        congrArg (fun z : ℝ => z ^ a) hrepr
      _ = _ := by rw [Real.mul_rpow hlow0.le (by positivity)]
  have hstep : endpoint t ^ a - lowerClock t ^ a ≤
      a * lowerClock t ^ (a - 1) * (endpoint t - lowerClock t) := by
    have hnonneg : 0 ≤ lowerClock t ^ a := Real.rpow_nonneg hlow0.le _
    have hmain : endpoint t ^ a - lowerClock t ^ a ≤
        lowerClock t ^ a * (a *
          ((endpoint t - lowerClock t) / lowerClock t)) := by
      rw [hBpow]
      nlinarith
    calc
      _ ≤ _ := hmain
      _ = _ := by
        rw [Real.rpow_sub hlow0]
        field_simp [hlow0.ne']
        simp only [Real.rpow_one]
        ring
  have hfac : lowerClock t ^ (a - 1) ≤ 2 * t ^ (a - 1) := by
    have hbase : (2 * t / 3 : ℝ) ≤ lowerClock t := hu.2.1
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 2 * t / 3) hbase
      (by norm_num : 0 ≤ 1 - a)
    have hneg : lowerClock t ^ (a - 1) ≤ (2 * t / 3) ^ (a - 1) := by
      have hlneg : lowerClock t ^ (a - 1) =
          1 / lowerClock t ^ (1 - a) := by
        rw [show a - 1 = -(1 - a) by ring]
        simpa only [one_div] using
          (Real.rpow_neg (show 0 ≤ lowerClock t by linarith) (1 - a))
      have htneg : (2 * t / 3) ^ (a - 1) =
          1 / (2 * t / 3) ^ (1 - a) := by
        rw [show a - 1 = -(1 - a) by ring]
        simpa only [one_div] using
          (Real.rpow_neg (show 0 ≤ 2 * t / 3 by positivity) (1 - a))
      rw [hlneg, htneg]
      exact one_div_le_one_div_of_le (by positivity) hpow
    have hconst : (2 / 3 : ℝ) ^ (a - 1) ≤ 2 := by
      rw [show a - 1 = -(1 - a) by ring, Real.rpow_neg (by norm_num)]
      have hsmall := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 2 / 3)
        (by norm_num : (2 / 3 : ℝ) ≤ 1) (by norm_num : 1 - a ≤ 1)
      have hqpos : 0 < (2 / 3 : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos (by norm_num) _
      have hsmall' : (2 / 3 : ℝ) ≤ (2 / 3 : ℝ) ^ (1 - a) := by
        simpa only [Real.rpow_one] using hsmall
      have hrec := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 / 3) hsmall'
      have hrec' : 1 / ((2 / 3 : ℝ) ^ (1 - a)) ≤ 2 := by
        calc
          _ ≤ 1 / (2 / 3 : ℝ) := hrec
          _ ≤ 2 := by norm_num
      simpa [one_div] using hrec'
    calc
      _ ≤ (2 * t / 3) ^ (a - 1) := hneg
      _ = (2 / 3 : ℝ) ^ (a - 1) * t ^ (a - 1) := by
        rw [show 2 * t / 3 = (2 / 3 : ℝ) * t by ring,
          Real.mul_rpow (by norm_num) ht0.le]
      _ ≤ 2 * t ^ (a - 1) := by
        gcongr
  have hdelta_le : endpoint t - lowerClock t ≤ 2 * t ^ (4 / 5 : ℝ) := by
    dsimp [endpoint, lowerClock, width]
    nlinarith
  have hpowadd : t ^ (a - 1) * t ^ (4 / 5 : ℝ) = t ^ (51 / 500 : ℝ) := by
    rw [← Real.rpow_add ht0]
    norm_num [a]
  have hprod := mul_le_mul hfac hdelta_le (by positivity) (by positivity)
  have hmain_bound : a * lowerClock t ^ (a - 1) * (endpoint t - lowerClock t) ≤
      a * (2 * t ^ (a - 1)) * (2 * t ^ (4 / 5 : ℝ)) := by
    calc
      _ = a * (lowerClock t ^ (a - 1) * (endpoint t - lowerClock t)) := by ring
      _ ≤ a * ((2 * t ^ (a - 1)) * (2 * t ^ (4 / 5 : ℝ))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  have hmain := hstep.trans hmain_bound
  calc
    _ ≤ a * (2 * t ^ (a - 1)) * (2 * t ^ (4 / 5 : ℝ)) := hmain
    _ = (4 * a) * t ^ (a - 1) * t ^ (4 / 5 : ℝ) := by ring
    _ = (4 * a) * (t ^ (a - 1) * t ^ (4 / 5 : ℝ)) := by ring
    _ = (151 / 125 : ℝ) * t ^ (51 / 500 : ℝ) := by
      rw [hpowadd]
      norm_num [a]

private lemma crossing_count {t : ℝ} (ht : 256 ≤ t) :
    ((Finset.Icc (⌊lowerClock t ^ (151 / 500 : ℝ)⌋₊ + 1)
      (⌊endpoint t ^ (151 / 500 : ℝ)⌋₊)).card : ℝ) ≤ 2 * t ^ (51 / 500 : ℝ) := by
  let a : ℝ := 151 / 500
  have hu := lowerClock_bounds ht
  have hlow : 0 ≤ lowerClock t ^ a := Real.rpow_nonneg hu.1.le _
  have hupper : 0 ≤ endpoint t ^ a := by
    have : 0 ≤ endpoint t := by
      dsimp [endpoint, width]
      positivity
    exact Real.rpow_nonneg this _
  have horder : lowerClock t ^ a ≤ endpoint t ^ a := by
    have hbase : 0 ≤ lowerClock t := hu.1.le
    have hle : lowerClock t ≤ endpoint t := by
      dsimp [endpoint, width]
      linarith [Real.rpow_nonneg (by linarith [hu.2.2] : 0 ≤ t) (4 / 5 : ℝ)]
    exact Real.rpow_le_rpow hbase hle (by norm_num)
  have hfloor : ⌊lowerClock t ^ a⌋₊ ≤ ⌊endpoint t ^ a⌋₊ :=
    Nat.le_floor ((Nat.floor_le hlow).trans horder)
  have hcard := Nat.card_Icc (⌊lowerClock t ^ a⌋₊ + 1)
    (⌊endpoint t ^ a⌋₊)
  have hcast : ((Finset.Icc (⌊lowerClock t ^ a⌋₊ + 1)
      (⌊endpoint t ^ a⌋₊)).card : ℝ) =
      (⌊endpoint t ^ a⌋₊ : ℝ) - (⌊lowerClock t ^ a⌋₊ : ℝ) := by
    rw [hcard]
    have hnat : ⌊endpoint t ^ a⌋₊ + 1 - (⌊lowerClock t ^ a⌋₊ + 1) =
        ⌊endpoint t ^ a⌋₊ - ⌊lowerClock t ^ a⌋₊ := by omega
    rw [hnat, Nat.cast_sub hfloor]
  have hupper_floor : (⌊endpoint t ^ a⌋₊ : ℝ) ≤ endpoint t ^ a := Nat.floor_le hupper
  have hlower_floor : lowerClock t ^ a - 1 < (⌊lowerClock t ^ a⌋₊ : ℝ) := by
    have h := (Nat.floor_lt hlow (n := ⌊lowerClock t ^ a⌋₊ + 1)).mp
      (by omega : ⌊lowerClock t ^ a⌋₊ < ⌊lowerClock t ^ a⌋₊ + 1)
    norm_num at h ⊢
    linarith
  rw [hcast]
  have hw := crossing_width_bound ht
  have hpow1 : (1 : ℝ) ≤ t ^ (51 / 500 : ℝ) := by
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hpow15 : (3 / 2 : ℝ) ≤ t ^ (51 / 500 : ℝ) := by
    have ht243 : (243 : ℝ) ≤ t := by linarith
    have hfive := Real.rpow_le_rpow (show 0 ≤ (243 : ℝ) by norm_num) ht243
      (show 0 ≤ (1 / 5 : ℝ) by norm_num)
    have hthree : (3 : ℝ) ≤ t ^ (1 / 5 : ℝ) := by
      convert hfive using 1
      · rw [show (243 : ℝ) = 3 ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
    have hten : (3 / 2 : ℝ) ≤ t ^ (1 / 10 : ℝ) := by
      have hsq : (t ^ (1 / 10 : ℝ)) ^ (2 : ℕ) = t ^ (1 / 5 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ t)]
        norm_num
      have hpos : 0 ≤ t ^ (1 / 10 : ℝ) := Real.rpow_nonneg (by linarith) _
      nlinarith [hsq]
    exact hten.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  have hw' : endpoint t ^ a - lowerClock t ^ a ≤
      (151 / 125 : ℝ) * t ^ (51 / 500 : ℝ) := by
    simpa [a] using hw
  nlinarith [hw', hpow15]

/-- The actual moving-cut row pays every lattice cell, including both terminal cells. -/
theorem original_cut_row_lattice_estimate {ell R t : ℝ}
    (hell : 256 ≤ ell) (horder : ell < R) (ht : t ∈ Icc ell R) {d : ℕ}
    (hd : 1 ≤ d) :
    |latticeRowRemainder ell R t d| ≤ 3 * lowerHeight t * Real.log (2 * t) := by
  by_cases hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)
  ·
    have ht256 := hell.trans ht.1
    have ht0 : 0 < t := by linarith
    have hd0 : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hd0
    have hV := (rowSupplier% cutRow_single_variation) hell horder ht hd hcut
    have hf : BoundedVariationOn (cutRow ell R t d) univ := (hV.trans_lt ENNReal.ofReal_lt_top).ne
    let N : ℕ := ⌊2 * R⌋₊
    have hnat : N + 1 ≤ d * (N / d + 1) := by
      have hr := Nat.mod_lt N hd0
      have he := Nat.div_add_mod N d
      nlinarith
    have hL : endpoint t ≤ (d : ℝ) * ((N / d + 1 : ℕ) : ℝ) := by
      have hcast : (N : ℝ) + 1 ≤ (d : ℝ) * ((N / d + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      have hfloor : 2 * R < (N : ℝ) + 1 := Nat.lt_floor_add_one (2 * R)
      exact ((rowSupplier% endpoint_le_twice) (by linarith)).trans
        ((mul_le_mul_of_nonneg_left ht.2 (by norm_num)).trans (hfloor.le.trans hcast))
    have hgrid := (rowSupplier% lattice_error_variation) hf hdreal (N / d + 1)
    have hint := cutRow_integral_full_grid ht0.le hL hf
    rw [hint] at hgrid
    have hset : Finset.range (N / d + 1) = insert 0 (Finset.Icc 1 (N / d)) := by
      rw [Nat.range_succ_eq_Icc_zero]
      simpa using (Finset.insert_Icc_succ_left_eq_Icc (a := 0) (b := N / d)
        (Nat.zero_le _)).symm
    rw [hset, Finset.sum_insert (by simp)] at hgrid
    simp only [Nat.cast_zero, mul_zero, cutRow_zero_of_outside d (Or.inl ht0.le), zero_add] at hgrid
    have hrow : (∑ m ∈ Finset.Icc 1 (N / d), cutRow ell R t d ((d : ℝ) * m)) =
        ∑ m ∈ Finset.Icc 1 (N / d), Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
          ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
            beforeRatio ell R d ((d : ℝ) * m)) := by
      apply Finset.sum_congr rfl
      intro m _
      unfold cutRow
      rw [mul_div_cancel_left₀ (m : ℝ) hdreal.ne']
    rw [hrow] at hgrid
    exact hgrid.trans (ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (mul_nonneg (by norm_num)
        ((rowSupplier% height_bounds) (by linarith [ht.1] : 4 ≤ t)).1)
        (Real.log_nonneg (by linarith [ht.1]))) hV)
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
    have hz : cutRow ell R t d = fun _ => 0 := by
      funext x
      exact cutRow_zero_above hell horder ht (not_le.mp hcut).le x
    have hsum : (∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
        Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
          ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
            beforeRatio ell R d ((d : ℝ) * m))) = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      have h := congrFun hz ((d : ℝ) * m)
      simpa only [cutRow, mul_div_cancel_left₀ (m : ℝ) hd0.ne'] using h
    unfold latticeRowRemainder
    rw [hsum, hz]
    simp only [intervalIntegral.integral_zero, zero_div, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num)
      ((rowSupplier% height_bounds) (by linarith [ht.1] : 4 ≤ t)).1)
      (Real.log_nonneg (by linarith [ht.1]))

private lemma latticeRowRemainder_zero_of_cutRow {ell R t : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hzero : cutRow ell R t d = fun _ => 0) :
    latticeRowRemainder ell R t d = 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hsum : (∑ m ∈ Finset.Icc 1 (⌊2 * R⌋₊ / d),
      Real.log (m : ℝ) * kernel t ((d : ℝ) * m) *
        ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) -
          beforeRatio ell R d ((d : ℝ) * m))) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have h := congrFun hzero ((d : ℝ) * m)
    simpa only [cutRow, mul_div_cancel_left₀ (m : ℝ) hd0.ne'] using h
  unfold latticeRowRemainder
  rw [hsum, hzero]
  simp

/-- The source-specific crossing count consumes the complete row estimate: every
    noncrossing divisor row is literally zero, and all remaining integer rows are
    paid with the actual Möbius absolute value. -/
theorem original_cut_row_pointwise_budget {ell R t : ℝ}
    (hell : 256 ≤ ell) (horder : ell < R) (ht : t ∈ Icc ell R) :
    ∑ d ∈ Finset.Icc 1 (⌊endpoint t ^ (151 / 500 : ℝ)⌋₊),
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        |latticeRowRemainder ell R t d| ≤
      6 * t ^ (-99 / 500 : ℝ) * Real.log (2 * t) := by
  have ht256 : 256 ≤ t := hell.trans ht.1
  have ht4 : 4 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  let A : Finset ℕ := Finset.Icc 1 (⌊endpoint t ^ (151 / 500 : ℝ)⌋₊)
  let C : Finset ℕ := Finset.Icc
    (⌊lowerClock t ^ (151 / 500 : ℝ)⌋₊ + 1)
    (⌊endpoint t ^ (151 / 500 : ℝ)⌋₊)
  let f : ℕ → ℝ := fun d =>
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      |latticeRowRemainder ell R t d|
  have hCsub : C ⊆ A := by
    intro d hd
    simp only [C, A, Finset.mem_Icc] at hd ⊢
    exact ⟨by omega, hd.2⟩
  have hzero_out : ∀ d ∈ A, d ∉ C → f d = 0 := by
    intro d hdA hdC
    have hdA' : 1 ≤ d ∧ d ≤ ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊ :=
      Finset.mem_Icc.mp hdA
    have hd1 : 1 ≤ d := hdA'.1
    have hdupper : d ≤ ⌊endpoint t ^ (151 / 500 : ℝ)⌋₊ := hdA'.2
    have hdlower : d ≤ ⌊lowerClock t ^ (151 / 500 : ℝ)⌋₊ := by
      by_contra hnot
      have hge : ⌊lowerClock t ^ (151 / 500 : ℝ)⌋₊ + 1 ≤ d := by omega
      apply hdC
      exact Finset.mem_Icc.mpr ⟨hge, hdupper⟩
    have hcut : (d : ℝ) ≤ lowerClock t ^ (151 / 500 : ℝ) :=
      (Nat.cast_le.2 hdlower).trans
        (Nat.floor_le (Real.rpow_nonneg (lowerClock_bounds ht256).1.le _))
    have hzero : cutRow ell R t d = fun _ => 0 := by
      funext x
      exact cutRow_zero_below hell horder ht hd1 hcut x
    dsimp [f]
    rw [latticeRowRemainder_zero_of_cutRow hd1 hzero, abs_zero, mul_zero]
  have hsum_eq : (∑ d ∈ A, f d) = (∑ d ∈ C, f d) := by
    symm
    exact Finset.sum_subset hCsub hzero_out
  have hterm : ∀ d ∈ C, f d ≤
      3 * lowerHeight t * Real.log (2 * t) := by
    intro d hdC
    have hd1 : 1 ≤ d := by
      have hbounds := Finset.mem_Icc.mp hdC
      omega
    have hμZ := ArithmeticFunction.abs_moebius_le_one (n := d)
    have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast hμZ
    have hrow := original_cut_row_lattice_estimate hell horder ht hd1
    dsimp [f]
    calc
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          |latticeRowRemainder ell R t d| ≤
          1 * |latticeRowRemainder ell R t d| :=
        mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
      _ ≤ 1 * (3 * lowerHeight t * Real.log (2 * t)) :=
        mul_le_mul_of_nonneg_left hrow (by norm_num)
      _ = 3 * lowerHeight t * Real.log (2 * t) := by ring
  change (∑ d ∈ A, f d) ≤ _
  rw [hsum_eq]
  calc
    _ ≤ ∑ _d ∈ C, (3 * lowerHeight t * Real.log (2 * t)) :=
      Finset.sum_le_sum hterm
    _ = (C.card : ℝ) * (3 * lowerHeight t * Real.log (2 * t)) := by simp
    _ ≤ (2 * t ^ (51 / 500 : ℝ)) *
        (3 * lowerHeight t * Real.log (2 * t)) := by
      have hnonneg : 0 ≤ 3 * lowerHeight t * Real.log (2 * t) := by
        exact mul_nonneg (mul_nonneg (by norm_num) ((rowSupplier% height_bounds) ht4).1)
          (Real.log_nonneg (by linarith))
      apply mul_le_mul_of_nonneg_right _ hnonneg
      have hcard : (C.card : ℝ) ≤ 2 * t ^ (51 / 500 : ℝ) := by
        dsimp [C]
        exact_mod_cast crossing_count ht256
      exact hcard
    _ ≤ 6 * t ^ (-99 / 500 : ℝ) * Real.log (2 * t) := by
      have hb := ((rowSupplier% height_bounds) ht4).2
      have hlog : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
      have hpow : t ^ (51 / 500 : ℝ) * t ^ (-3 / 10 : ℝ) =
          t ^ (-99 / 500 : ℝ) := by
        rw [← Real.rpow_add ht0]
        norm_num
      have hbase : t ^ (51 / 500 : ℝ) * lowerHeight t ≤
          t ^ (-99 / 500 : ℝ) := by
        calc
          t ^ (51 / 500 : ℝ) * lowerHeight t ≤
              t ^ (51 / 500 : ℝ) * t ^ (-3 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht0.le _)
          _ = t ^ (-99 / 500 : ℝ) := hpow
      calc
        (2 * t ^ (51 / 500 : ℝ)) *
            (3 * lowerHeight t * Real.log (2 * t)) =
            6 * (t ^ (51 / 500 : ℝ) * lowerHeight t) * Real.log (2 * t) := by
          ring
        _ ≤ 6 * t ^ (-99 / 500 : ℝ) * Real.log (2 * t) := by
          gcongr


end D5.S3.Arith.Robin.OriginalMovingCutBudget
