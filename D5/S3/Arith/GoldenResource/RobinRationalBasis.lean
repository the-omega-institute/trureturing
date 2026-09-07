/- GID: D5/S3/Arith/GoldenResource/RobinRationalBasis
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/RobinRationalBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=atom:d248c270bab138d363ccd11787ff970080d2b4ef3399a00e53926183077355d5; instance=D5/S3/Arith/GoldenResource/RobinRationalBasis.robin_delta_10080_pos; result=D5/S3/Arith/GoldenResource/RobinRationalBasis.robinPositiveJudge_sound
   digest: Sharp rational logarithm bounds certify a Robin checker and its 10080 instance. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenResource.RobinRationalBasis

open Filter Topology
open scoped BigOperators

noncomputable def atanhPartial (t : ℝ) (K : ℕ) : ℝ :=
  2 * ∑ j ∈ Finset.range K, t ^ (2 * j + 1) / (2 * j + 1)

/-- The appendix parameter that reduces `y ∈ [1, 2)` to the atanh interval `[0, 1/3)`. -/
noncomputable def atanhParameter (y : ℝ) : ℝ :=
  (y - 1) / (y + 1)

/-- The appendix parameter lies in the interval required by the sharp atanh remainder bound. -/
theorem atanhParameter_lt_third {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y < 2) :
    0 ≤ atanhParameter y ∧ atanhParameter y < (1 / 3 : ℝ) := by
  have hyadd : 0 < y + 1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hy1) hyadd.le
  · rw [atanhParameter, div_lt_iff₀ hyadd]
    nlinarith

/-- The named remainder after truncating the appendix atanh expansion. -/
noncomputable def logRemainder (y : ℝ) (K : ℕ) : ℝ :=
  Real.log y - atanhPartial (atanhParameter y) K

private lemma atanh_remainder_sharp {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (K : ℕ) :
    0 ≤ Real.log ((1 + t) / (1 - t)) - atanhPartial t K ∧
      Real.log ((1 + t) / (1 - t)) - atanhPartial t K ≤
        2 * t ^ (2 * K + 1) / ((2 * K + 1) * (1 - t ^ 2)) := by
  let F : ℝ → ℝ := fun x ↦
    1 / 2 * Real.log ((1 + x) / (1 - x)) -
      (∑ j ∈ Finset.range K, x ^ (2 * j + 1) / (2 * j + 1))
  let F' : ℝ → ℝ := fun x ↦ (x ^ 2) ^ K / (1 - x ^ 2)
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt F (F' x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) t := by simpa [Set.uIcc_of_le ht0] using hx
    exact Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range K
      (by linarith [hxIcc.1]) (by linarith [hxIcc.2])
  have hF'cont : ContinuousOn F' (Set.Icc (0 : ℝ) t) := by
    apply ContinuousOn.div
    · exact (continuousOn_id.pow 2).pow K
    · exact continuousOn_const.sub (continuousOn_id.pow 2)
    · intro x hx
      have hxlt : x < 1 := hx.2.trans_lt ht1
      have hx2 : x ^ 2 < (1 : ℝ) ^ 2 := (sq_lt_sq₀ hx.1 zero_le_one).2 hxlt
      nlinarith
  have hFint : IntervalIntegrable F' MeasureTheory.volume 0 t :=
    hF'cont.intervalIntegrable_of_Icc ht0
  have hFTC : (∫ x in (0 : ℝ)..t, F' x) = F t := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hFint
    simpa [F] using h
  have hnonneg : 0 ≤ F t := by
    dsimp [F]
    exact sub_nonneg.mpr (Real.sum_range_le_log_div ht0 ht1 K)
  have hmajorCont : IntervalIntegrable
      (fun x : ℝ ↦ x ^ (2 * K) / (1 - t ^ 2)) MeasureTheory.volume 0 t :=
    (continuous_pow (2 * K) |>.div_const (1 - t ^ 2)).intervalIntegrable 0 t
  have hmono : (∫ x in (0 : ℝ)..t, F' x) ≤
      ∫ x in (0 : ℝ)..t, x ^ (2 * K) / (1 - t ^ 2) := by
    apply intervalIntegral.integral_mono_on ht0 hFint hmajorCont
    intro x hx
    have hxnonneg : 0 ≤ x := hx.1
    have hxt : x ≤ t := hx.2
    have hx2 : x ^ 2 < (1 : ℝ) ^ 2 := (sq_lt_sq₀ hxnonneg zero_le_one).2
      (hxt.trans_lt ht1)
    have ht2 : t ^ 2 < (1 : ℝ) ^ 2 := (sq_lt_sq₀ ht0 zero_le_one).2 ht1
    have hdenx : 0 < 1 - x ^ 2 := by nlinarith
    have hdent : 0 < 1 - t ^ 2 := by nlinarith
    have hsquares : x ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hxnonneg ht0).2 hxt
    dsimp [F']
    rw [← pow_mul]
    exact div_le_div_of_nonneg_left (pow_nonneg hxnonneg (2 * K)) hdent
      (by nlinarith)
  have hmajorEval :
      (∫ x in (0 : ℝ)..t, x ^ (2 * K) / (1 - t ^ 2)) =
        t ^ (2 * K + 1) / ((2 * K + 1) * (1 - t ^ 2)) := by
    rw [intervalIntegral.integral_div, integral_pow]
    have hpos : (2 * K + 1 : ℕ) ≠ 0 := by omega
    have hcastpos : (0 : ℝ) < (2 * K + 1 : ℕ) := by positivity
    have htden : (1 - t ^ 2) ≠ 0 := by
      have ht2 : t ^ 2 < (1 : ℝ) ^ 2 := (sq_lt_sq₀ ht0 zero_le_one).2 ht1
      nlinarith
    rw [zero_pow hpos, sub_zero]
    field_simp
    push_cast
    ring
  rw [hFTC, hmajorEval] at hmono
  dsimp [F, atanhPartial] at hnonneg hmono ⊢
  have hscale :
      Real.log ((1 + t) / (1 - t)) -
          2 * ∑ j ∈ Finset.range K, t ^ (2 * j + 1) / (2 * j + 1) =
        2 * (1 / 2 * Real.log ((1 + t) / (1 - t)) -
          ∑ j ∈ Finset.range K, t ^ (2 * j + 1) / (2 * j + 1)) := by
    ring
  rw [hscale]
  constructor
  · exact mul_nonneg (by norm_num) hnonneg
  · calc
      2 * (1 / 2 * Real.log ((1 + t) / (1 - t)) -
          ∑ j ∈ Finset.range K, t ^ (2 * j + 1) / (2 * j + 1)) ≤
          2 * (t ^ (2 * K + 1) / ((2 * K + 1) * (1 - t ^ 2))) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ = 2 * t ^ (2 * K + 1) / ((2 * K + 1) * (1 - t ^ 2)) := by ring

/-- The appendix atanh expansion, including its sharp `1 / (2K+1)` remainder factor. -/
theorem log_expansion_remainder_bound {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y < 2) (K : ℕ) :
    0 ≤ logRemainder y K ∧
      logRemainder y K ≤
        2 * atanhParameter y ^ (2 * K + 1) /
          ((2 * K + 1) * (1 - atanhParameter y ^ 2)) := by
  have ht := atanhParameter_lt_third hy1 hy2
  have ht1 : atanhParameter y < 1 := ht.2.trans (by norm_num)
  have hid : (1 + atanhParameter y) / (1 - atanhParameter y) = y := by
    rw [atanhParameter]
    field_simp
    ring
  simpa [logRemainder, hid] using atanh_remainder_sharp ht.1 ht1 K

#print axioms log_expansion_remainder_bound

private lemma log_one_add_inv_lt_trapezoid {x : ℝ} (hx : 0 < x) :
    Real.log ((x + 1) / x) < 1 / 2 * (1 / x + 1 / (x + 1)) := by
  let t : ℝ := 1 / (2 * x + 1)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one (by positivity)]
    linarith
  have hlog := Real.log_div_le_sum_range_add ht0 ht1 2
  have hid : (1 + t) / (1 - t) = (x + 1) / x := by
    dsimp [t]
    field_simp
    ring
  rw [hid] at hlog
  have hstrict :
      (∑ i ∈ Finset.range 2, t ^ (2 * i + 1) / (2 * i + 1)) +
          t ^ (2 * 2 + 1) / (1 - t ^ 2) < t / (1 - t ^ 2) := by
    norm_num [Finset.sum_range_succ]
    have hden : 0 < 1 - t ^ 2 := by
      have ht2 : t ^ 2 < (1 : ℝ) ^ 2 := (sq_lt_sq₀ ht0 zero_le_one).2 ht1
      nlinarith
    field_simp
    nlinarith [sq_pos_of_pos htpos]
  have htrap : t / (1 - t ^ 2) = 1 / 4 * (1 / x + 1 / (x + 1)) := by
    have htden : 1 - t ^ 2 ≠ 0 := by
      have ht2 : t ^ 2 < (1 : ℝ) ^ 2 := (sq_lt_sq₀ ht0 zero_le_one).2 ht1
      nlinarith
    rw [div_eq_iff htden]
    dsimp [t]
    have hx0 : x ≠ 0 := hx.ne'
    have hx10 : x + 1 ≠ 0 := by positivity
    have hlin0 : 2 * x + 1 ≠ 0 := by positivity
    field_simp [hx0, hx10, hlin0]
    ring
  rw [htrap] at hstrict
  have hhalf :
      1 / 2 * Real.log ((x + 1) / x) < 1 / 4 * (1 / x + 1 / (x + 1)) :=
    hlog.trans_lt hstrict
  calc
    Real.log ((x + 1) / x) = 2 * (1 / 2 * Real.log ((x + 1) / x)) := by ring
    _ < 2 * (1 / 4 * (1 / x + 1 / (x + 1))) :=
      mul_lt_mul_of_pos_left hhalf (by norm_num)
    _ = 1 / 2 * (1 / x + 1 / (x + 1)) := by ring

private lemma two_inv_le_log_one_add_inv {x : ℝ} (hx : 0 < x) :
    2 / (2 * x + 1) ≤ Real.log ((x + 1) / x) := by
  let t : ℝ := 1 / (2 * x + 1)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one (by positivity)]
    linarith
  have hlog := Real.sum_range_le_log_div ht0 ht1 1
  have hid : (1 + t) / (1 - t) = (x + 1) / x := by
    dsimp [t]
    field_simp
    ring
  rw [hid] at hlog
  norm_num [Finset.sum_range_succ] at hlog
  dsimp [t] at hlog
  calc
    2 / (2 * x + 1) = 2 * (1 / (2 * x + 1)) := by ring
    _ ≤ 2 * (1 / 2 * Real.log ((x + 1) / x)) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ = Real.log ((x + 1) / x) := by ring

/-- The termwise logarithmic estimate used in the appendix proof of (A.1). -/
theorem log_harmonic_term_bounds {x : ℝ} (hx : 0 < x) :
    1 / (2 * (x + 1) ^ 2) < Real.log ((x + 1) / x) - 1 / (x + 1) ∧
      Real.log ((x + 1) / x) - 1 / (x + 1) < 1 / (2 * x * (x + 1)) := by
  have hlower := two_inv_le_log_one_add_inv hx
  have hupper := log_one_add_inv_lt_trapezoid hx
  have hlowerRat :
      1 / (2 * (x + 1) ^ 2) < 2 / (2 * x + 1) - 1 / (x + 1) := by
    have hx10 : x + 1 ≠ 0 := by positivity
    have h2x0 : 2 * x + 1 ≠ 0 := by positivity
    field_simp [hx10, h2x0]
    nlinarith
  have hupperEq :
      1 / 2 * (1 / x + 1 / (x + 1)) - 1 / (x + 1) =
        1 / (2 * x * (x + 1)) := by
    have hx0 : x ≠ 0 := hx.ne'
    have hx10 : x + 1 ≠ 0 := by positivity
    field_simp [hx0, hx10]
    ring
  constructor
  · linarith
  · rw [← hupperEq]
    linarith

#print axioms log_harmonic_term_bounds

private noncomputable def lowerEulerSeq (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1))

private noncomputable def upperEulerSeq (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 2))

private lemma strictMono_lowerEulerSeq : StrictMono lowerEulerSeq := by
  apply strictMono_nat_of_lt_succ
  intro n
  let x : ℝ := n + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have hterm := log_harmonic_term_bounds hx
  have hharm :
      (harmonic (n + 2) : ℝ) = (harmonic (n + 1) : ℝ) + 1 / (x + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, harmonic_succ, Rat.cast_add,
      Rat.cast_inv, Rat.cast_natCast]
    push_cast
    dsimp [x]
    ring
  have hlogdiv :
      Real.log ((x + 1) / x) = Real.log (n + 2) - Real.log (n + 1) := by
    rw [Real.log_div (by positivity) (by positivity)]
    congr 1 <;> push_cast <;> dsimp [x] <;> ring
  have hdiff :
      lowerEulerSeq (n + 1) - lowerEulerSeq n =
        1 / (2 * x * (x + 1)) -
          (Real.log ((x + 1) / x) - 1 / (x + 1)) := by
    rw [lowerEulerSeq, lowerEulerSeq, hharm, hlogdiv]
    push_cast
    dsimp [x]
    field_simp <;> ring
  rw [← sub_pos, hdiff]
  exact sub_pos.mpr hterm.2

private lemma strictAnti_upperEulerSeq : StrictAnti upperEulerSeq := by
  apply strictAnti_nat_of_succ_lt
  intro n
  let x : ℝ := n + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have hterm := log_harmonic_term_bounds hx
  have hrat :
      1 / (2 * (x + 1) * (x + 2)) < 1 / (2 * (x + 1) ^ 2) := by
    have hx10 : x + 1 ≠ 0 := by positivity
    have hx20 : x + 2 ≠ 0 := by positivity
    field_simp [hx10, hx20]
    nlinarith
  have hharm :
      (harmonic (n + 2) : ℝ) = (harmonic (n + 1) : ℝ) + 1 / (x + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, harmonic_succ, Rat.cast_add,
      Rat.cast_inv, Rat.cast_natCast]
    push_cast
    dsimp [x]
    ring
  have hlogdiv :
      Real.log ((x + 1) / x) = Real.log (n + 2) - Real.log (n + 1) := by
    rw [Real.log_div (by positivity) (by positivity)]
    congr 1 <;> push_cast <;> dsimp [x] <;> ring
  have hdiff :
      upperEulerSeq n - upperEulerSeq (n + 1) =
        (Real.log ((x + 1) / x) - 1 / (x + 1)) -
          1 / (2 * (x + 1) * (x + 2)) := by
    rw [upperEulerSeq, upperEulerSeq, hharm, hlogdiv]
    push_cast
    dsimp [x]
    field_simp <;> ring
  rw [← sub_pos, hdiff]
  exact sub_pos.mpr (hrat.trans hterm.1)

private lemma tendsto_lowerEulerSeq :
    Tendsto lowerEulerSeq atTop (nhds Real.eulerMascheroniConstant) := by
  have hres : Tendsto
      (fun n : ℕ ↦ (harmonic (n + 1) : ℝ) - Real.log (n + 1)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (2 * (n + 1))) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hscaled := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hbase
    convert hscaled using 1 <;> simp <;> ring
  unfold lowerEulerSeq
  simpa only [sub_zero] using hres.sub hinv

private lemma tendsto_upperEulerSeq :
    Tendsto upperEulerSeq atTop (nhds Real.eulerMascheroniConstant) := by
  have hres : Tendsto
      (fun n : ℕ ↦ (harmonic (n + 1) : ℝ) - Real.log (n + 1)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hinv1 : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (2 * (n + 1))) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hscaled := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hbase
    convert hscaled using 1 <;> simp <;> ring
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (2 * (n + 2))) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      hinv1.comp (tendsto_add_atTop_nat 1)
  unfold upperEulerSeq
  simpa only [sub_zero] using hres.sub hinv

/-- The sharp appendix bracket (A.1), for every positive integer `N`. -/
theorem eulerMascheroni_remainder_bounds (N : ℕ) (hN : 1 ≤ N) :
    1 / (2 * (N + 1) : ℝ) <
        (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant ∧
      (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant <
        1 / (2 * N : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_comm 1 n]
  have hlower : lowerEulerSeq n < Real.eulerMascheroniConstant :=
    (strictMono_lowerEulerSeq (Nat.lt_succ_self n)).trans_le
      (strictMono_lowerEulerSeq.monotone.ge_of_tendsto tendsto_lowerEulerSeq (n + 1))
  have hupper : Real.eulerMascheroniConstant < upperEulerSeq n :=
    (strictAnti_upperEulerSeq.antitone.le_of_tendsto tendsto_upperEulerSeq (n + 1)).trans_lt
      (strictAnti_upperEulerSeq (Nat.lt_succ_self n))
  dsimp [lowerEulerSeq, upperEulerSeq] at hlower hupper
  push_cast at hlower hupper ⊢
  have hden : 1 / (2 * ((n : ℝ) + 1 + 1)) = 1 / (2 * ((n : ℝ) + 2)) := by
    congr 2
    ring
  constructor
  · rw [hden]
    linarith
  · linarith

#print axioms eulerMascheroni_remainder_bounds

/-- Pinned Mathlib's certified decimal bracket for `log 2`. -/
theorem log_two_decimal_bounds :
    (6931471803 / 10000000000 : ℝ) < Real.log 2 ∧
      Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
  constructor
  · convert Real.log_two_gt_d9 using 1 <;> norm_num
  · convert Real.log_two_lt_d9 using 1 <;> norm_num

#print axioms log_two_decimal_bounds

private lemma log_one_thousand_bounds :
    (690775527 / 100000000 : ℝ) < Real.log 1000 ∧
      Real.log 1000 < (690775529 / 100000000 : ℝ) := by
  have hseries := log_expansion_remainder_bound
    (y := (125 / 64 : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hseries
  have hlogid : Real.log 1000 = 9 * Real.log 2 + Real.log (125 / 64) := by
    rw [show (1000 : ℝ) = 2 ^ 9 * (125 / 64) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [hlogid]
  constructor
  · nlinarith [log_two_decimal_bounds.1]
  · nlinarith [log_two_decimal_bounds.2]

set_option maxRecDepth 100000

/-- A sub-micro rational enclosure for the Euler--Mascheroni constant, at the precision used by
the appendix's `N = 1000` certificate. -/
theorem eulerMascheroni_decimal_bounds :
    (5772155 / 10000000 : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (5772161 / 10000000 : ℝ) := by
  have hA := eulerMascheroni_remainder_bounds 1000 (by norm_num)
  have hlog := log_one_thousand_bounds
  norm_num [harmonic] at hA
  constructor <;> nlinarith

#print axioms eulerMascheroni_decimal_bounds

/-- Rational outward-rounded endpoints for a real quantity. -/
structure RationalBracket where
  lower : ℚ
  upper : ℚ

/-- Semantic validity of a rational bracket. -/
def RationalBracket.Contains (b : RationalBracket) (x : ℝ) : Prop :=
  (b.lower : ℝ) ≤ x ∧ x ≤ (b.upper : ℝ)

/-- The rational Taylor lower sum used to eliminate `exp` from the checker. -/
def expPartial (q : ℚ) (terms : ℕ) : ℚ :=
  (NormedSpace.expSeries ℚ ℚ).partialSum terms q

/-- Mathlib's exponential formal-series partial sum is the displayed rational Taylor sum. -/
theorem expPartial_eq_sum (q : ℚ) (terms : ℕ) :
    expPartial q terms = ∑ i ∈ Finset.range terms, q ^ i / i.factorial := by
  unfold expPartial FormalMultilinearSeries.partialSum
  apply Finset.sum_congr rfl
  intro i hi
  exact NormedSpace.expSeries_apply_eq_div q i

/-- The additive Robin gap `e^γ · n · log log n − σ(n)`, an auxiliary quantity of this module.
The volume's chapter-9 margin `Δ(n) = γ + log log log n − log(σ(n)/n)` is a different
(logarithmic) quantity, formalized in the companion module `GoldenCell5040Certificate`; only the
signs of the two agree, and no identity between them is claimed here. -/
noncomputable def robinDelta (n : ℕ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) -
    (ArithmeticFunction.sigma 1 n : ℝ)

/-- A fully rational sufficient condition for positivity of this module's auxiliary additive Robin
gap. The upper endpoints are checked for interval consistency and retained for downstream interval
composition; soundness uses the lower endpoints. -/
def RobinPositiveJudge (n terms : ℕ) (gamma logLog : RationalBracket) : Prop :=
  gamma.lower ≤ gamma.upper ∧
    logLog.lower ≤ logLog.upper ∧
    0 ≤ gamma.lower ∧
    0 ≤ logLog.lower ∧
    (ArithmeticFunction.sigma 1 n : ℚ) <
      expPartial gamma.lower terms * n * logLog.lower

instance robinPositiveJudgeDecidable (n terms : ℕ) (gamma logLog : RationalBracket) :
    Decidable (RobinPositiveJudge n terms gamma logLog) := by
  unfold RobinPositiveJudge
  infer_instance

/-- Soundness of this module's rational checker for the auxiliary additive Robin gap. -/
theorem robinPositiveJudge_sound (n terms : ℕ) (gamma logLog : RationalBracket)
    (hgamma : gamma.Contains Real.eulerMascheroniConstant)
    (hlogLog : logLog.Contains (Real.log (Real.log n)))
    (hjudge : RobinPositiveJudge n terms gamma logLog) :
    0 < robinDelta n := by
  rcases hjudge with ⟨_, _, hgamma0, hlogLog0, hcert⟩
  have hpartial0 : 0 ≤ expPartial gamma.lower terms := by
    rw [expPartial_eq_sum]
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (pow_nonneg hgamma0 i) (by positivity)
  have hpartialCast :
      ((expPartial gamma.lower terms : ℚ) : ℝ) =
        ∑ i ∈ Finset.range terms,
          (gamma.lower : ℝ) ^ i / (i.factorial : ℝ) := by
    rw [expPartial_eq_sum]
    simp [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  have hexpPartial :
      ((expPartial gamma.lower terms : ℚ) : ℝ) ≤
        Real.exp Real.eulerMascheroniConstant := by
    rw [hpartialCast]
    exact (Real.sum_le_exp_of_nonneg (by exact_mod_cast hgamma0) terms).trans
      (Real.exp_le_exp.mpr hgamma.1)
  have hcertReal :
      (ArithmeticFunction.sigma 1 n : ℝ) <
        ((expPartial gamma.lower terms : ℚ) : ℝ) * n * (logLog.lower : ℝ) := by
    exact_mod_cast hcert
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hpartialReal0 : (0 : ℝ) ≤ ((expPartial gamma.lower terms : ℚ) : ℝ) := by
    exact_mod_cast hpartial0
  have hlogLogReal0 : (0 : ℝ) ≤ (logLog.lower : ℝ) := by
    exact_mod_cast hlogLog0
  have hfirst :
      ((expPartial gamma.lower terms : ℚ) : ℝ) * n * (logLog.lower : ℝ) ≤
        Real.exp Real.eulerMascheroniConstant * n * (logLog.lower : ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexpPartial hn0) hlogLogReal0
  have hsecond :
      Real.exp Real.eulerMascheroniConstant * n * (logLog.lower : ℝ) ≤
        Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
    exact mul_le_mul_of_nonneg_left hlogLog.1
      (mul_nonneg (Real.exp_pos _).le hn0)
  unfold robinDelta
  linarith

/-- A certified logarithm bracket after reducing a positive input to `2^k * y`. -/
theorem log_pow_two_mul_bounds (y : ℝ) (k K : ℕ) (hk : 1 ≤ k)
    (hy1 : 1 ≤ y) (hy2 : y < 2) :
    (k : ℝ) * (6931471803 / 10000000000 : ℝ) +
          atanhPartial ((y - 1) / (y + 1)) K <
        Real.log ((2 : ℝ) ^ k * y) ∧
      Real.log ((2 : ℝ) ^ k * y) <
        (k : ℝ) * (6931471808 / 10000000000 : ℝ) +
          atanhPartial ((y - 1) / (y + 1)) K +
            2 * ((y - 1) / (y + 1)) ^ (2 * K + 1) /
              ((2 * K + 1) * (1 - ((y - 1) / (y + 1)) ^ 2)) := by
  have hseries := log_expansion_remainder_bound hy1 hy2 K
  simp only [logRemainder, atanhParameter] at hseries
  have htwo := log_two_decimal_bounds
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hlog : Real.log ((2 : ℝ) ^ k * y) =
      (k : ℝ) * Real.log 2 + Real.log y := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
  rw [hlog]
  constructor <;> nlinarith [hseries.1, hseries.2, htwo.1, htwo.2]

/-- Transfer a checked rational atanh calculation to a logarithm bracket. -/
theorem rational_log_bounds (x y lo hi : ℝ) (k K : ℕ)
    (hx : x = (2 : ℝ) ^ k * y) (hk : 1 ≤ k) (hy1 : 1 ≤ y) (hy2 : y < 2)
    (hcalc :
      lo < (k : ℝ) * (6931471803 / 10000000000 : ℝ) +
          atanhPartial ((y - 1) / (y + 1)) K ∧
      (k : ℝ) * (6931471808 / 10000000000 : ℝ) +
          atanhPartial ((y - 1) / (y + 1)) K +
            2 * ((y - 1) / (y + 1)) ^ (2 * K + 1) /
              ((2 * K + 1) * (1 - ((y - 1) / (y + 1)) ^ 2)) < hi) :
    lo < Real.log x ∧ Real.log x < hi := by
  rw [hx]
  have h := log_pow_two_mul_bounds y k K hk hy1 hy2
  exact ⟨hcalc.1.trans h.1, h.2.trans hcalc.2⟩

/-- Transfer endpoint logarithm bounds across a positive real interval. -/
theorem log_interval_bounds {x a b lo hi : ℝ}
    (ha0 : 0 < a) (hax : a < x) (hxb : x < b)
    (hlo : lo < Real.log a) (hhi : Real.log b < hi) :
    lo < Real.log x ∧ Real.log x < hi := by
  have hx0 : 0 < x := ha0.trans hax
  have hb0 : 0 < b := hx0.trans hxb
  exact ⟨hlo.trans (Real.strictMonoOn_log ha0 hx0 hax),
    (Real.strictMonoOn_log hx0 hb0 hxb).trans hhi⟩

/-- A rational bracket for `log 10080`, used by the first checker instance. -/
theorem log_10080_bounds :
    (921830853 / 100000000 : ℝ) < Real.log 10080 ∧
      Real.log 10080 < (184366171 / 20000000 : ℝ) := by
  refine rational_log_bounds 10080 (315 / 256) _ _ 13 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

/-- A rational bracket for `log (log 10080)`, used by the first checker instance. -/
theorem logLog_10080_bounds :
    (55529789 / 25000000 : ℝ) < Real.log (Real.log 10080) ∧
      Real.log (Real.log 10080) < (222119157 / 100000000 : ℝ) := by
  have hlo := rational_log_bounds (921830853 / 100000000) (921830853 / 800000000)
    (55529789 / 25000000) (222119157 / 100000000) 3 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (184366171 / 20000000) (184366171 / 160000000)
    (55529789 / 25000000) (222119157 / 100000000) 3 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) log_10080_bounds.1 log_10080_bounds.2 hlo.1 hhi.2

/-- The concrete Euler--Mascheroni interval supplied to the rational checker. -/
def gammaBracket : RationalBracket :=
  ⟨5772155 / 10000000, 5772161 / 10000000⟩

/-- The concrete `log (log 10080)` interval supplied to the rational checker. -/
def logLog10080Bracket : RationalBracket :=
  ⟨55529789 / 25000000, 222119157 / 100000000⟩

private theorem sigma_four_coprime {a b c d : ℕ}
    (hab : Nat.Coprime a b) (habc : Nat.Coprime (a * b) c)
    (habcd : Nat.Coprime (a * b * c) d) :
    ArithmeticFunction.sigma 1 (a * b * c * d) =
      ArithmeticFunction.sigma 1 a * ArithmeticFunction.sigma 1 b *
        ArithmeticFunction.sigma 1 c * ArithmeticFunction.sigma 1 d := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime habcd,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime habc,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab]

private theorem sigma_10080_value :
    ArithmeticFunction.sigma 1 10080 = 39312 := by
  have s25 : ArithmeticFunction.sigma 1 (2 ^ 5) = 63 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2)]
    norm_num
  have s32 : ArithmeticFunction.sigma 1 (3 ^ 2) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
    norm_num
  have s5 : ArithmeticFunction.sigma 1 5 = 6 := by
    rw [show (5 : ℕ) = 5 ^ 1 by norm_num,
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
    norm_num
  have s7 : ArithmeticFunction.sigma 1 7 = 8 := by
    rw [show (7 : ℕ) = 7 ^ 1 by norm_num,
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 7)]
    norm_num
  rw [show (10080 : ℕ) = 2 ^ 5 * 3 ^ 2 * 5 * 7 by norm_num,
    sigma_four_coprime (by decide) (by decide) (by decide), s25, s32, s5, s7]

/-- The first concrete checker computation: four exponential terms certify `n = 10080`. -/
theorem robin_positive_judge_10080 :
    RobinPositiveJudge 10080 4 gammaBracket logLog10080Bracket := by
  unfold RobinPositiveJudge
  rw [sigma_10080_value]
  norm_num [gammaBracket, logLog10080Bracket, expPartial_eq_sum, Finset.sum_range_succ]

/-- The rational checker proves that this module's auxiliary additive Robin gap is positive at
10080. -/
theorem robin_delta_10080_pos : 0 < robinDelta 10080 := by
  apply robinPositiveJudge_sound 10080 4 gammaBracket logLog10080Bracket
  · change ((5772155 / 10000000 : ℚ) : ℝ) ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ ((5772161 / 10000000 : ℚ) : ℝ)
    have h := eulerMascheroni_decimal_bounds
    constructor <;> linarith
  · change ((55529789 / 25000000 : ℚ) : ℝ) ≤ Real.log (Real.log 10080) ∧
      Real.log (Real.log 10080) ≤ ((222119157 / 100000000 : ℚ) : ℝ)
    constructor <;> linarith [logLog_10080_bounds.1, logLog_10080_bounds.2]
  · exact robin_positive_judge_10080

example : ∃ y : ℝ, 1 ≤ y ∧ y < 2 := ⟨3 / 2, by norm_num, by norm_num⟩

example : ∃ b : RationalBracket, b.Contains (0 : ℝ) :=
  ⟨⟨0, 1⟩, by norm_num [RationalBracket.Contains]⟩

#print axioms atanhPartial
#print axioms atanhParameter
#print axioms atanhParameter_lt_third
#print axioms logRemainder
#print axioms log_expansion_remainder_bound
#print axioms log_harmonic_term_bounds
#print axioms eulerMascheroni_remainder_bounds
#print axioms log_two_decimal_bounds
#print axioms eulerMascheroni_decimal_bounds
#print axioms RationalBracket
#print axioms RationalBracket.Contains
#print axioms expPartial
#print axioms expPartial_eq_sum
#print axioms robinDelta
#print axioms RobinPositiveJudge
#print axioms robinPositiveJudgeDecidable
#print axioms robinPositiveJudge_sound
#print axioms log_pow_two_mul_bounds
#print axioms rational_log_bounds
#print axioms log_interval_bounds
#print axioms log_10080_bounds
#print axioms logLog_10080_bounds
#print axioms gammaBracket
#print axioms logLog10080Bracket
#print axioms robin_positive_judge_10080
#print axioms robin_delta_10080_pos

end D5.S3.Arith.GoldenResource.RobinRationalBasis
