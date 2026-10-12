/- GID: D5/S3/Estimation/TimeArrow/NativeGrowthRounding
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeGrowthRounding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original decimal growth and integer rounding supply native finite-scale bounds. -/

import D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
import D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Filter
open scoped Topology
open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeGrowthRounding
noncomputable section

/-- Index zero corresponds to the first decimal exponent of the original sequence. -/
def decimalExponent : ℕ → ℕ
  | 0 => 1
  | n + 1 => 10 ^ (5 * decimalExponent n)

/-- The original decimal denominator. -/
def denominator (n : ℕ) : ℕ := 10 ^ decimalExponent n

/-- The original integer observation scale. -/
def scale (n : ℕ) : ℕ := denominator n ^ 3

/-- The lower-left signal cell retains the original floor. -/
def centralPositive (r : ℝ) (L : ℕ) : ℕ := ⌊((1 + r) / 2) * (L : ℝ)⌋₊

/-- The second coordinate retains the exact total count. -/
def centralNegative (r : ℝ) (L : ℕ) : ℕ := L - centralPositive r L

/-- The uncompensated score at the original lower-left cell. -/
def center (r : ℝ) (L : ℕ) : ℝ :=
  centralPositive r L * Real.log (1 + r) +
    centralNegative r L * Real.log (1 - r)

/-- Original population size, with its base-two floor. -/
def population (r β : ℝ) (L : ℕ) : ℕ :=
  2 ^ ⌊phi r * (L : ℝ) / (β * Real.log 2)⌋₊

/-- Original signal cardinality, with its final floor. -/
def signalSize (r β : ℝ) (L : ℕ) : ℕ :=
  ⌊(population r β L : ℝ) * Real.exp (-center r L)⌋₊

/-- The original A-cell logit uses the complete background population. -/
def cellLogit (r β : ℝ) (L : ℕ) : ℝ :=
  let M := population r β L
  let q := signalSize r β L
  centralPositive r L * Real.log ((1 + r) / (1 - compensation M q r)) +
    centralNegative r L * Real.log ((1 - r) / (1 + compensation M q r)) -
      Real.log (((M - q : ℕ) : ℝ) / q)

/-- Both central coordinates have a bounded rounding error. -/
theorem central_rounding (r : ℝ) (L : ℕ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    centralPositive r L ≤ L ∧
      0 ≤ ((1 + r) / 2) * (L : ℝ) - centralPositive r L ∧
      ((1 + r) / 2) * (L : ℝ) - centralPositive r L < 1 ∧
      (centralNegative r L : ℝ) = (L : ℝ) - centralPositive r L := by
  have ha : 0 ≤ ((1 + r) / 2) * (L : ℝ) := by positivity
  have hk : centralPositive r L ≤ L := by
    apply Nat.floor_le_of_le
    nlinarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
  refine ⟨hk, sub_nonneg.mpr (Nat.floor_le ha), ?_, ?_⟩
  · have h : ((1 + r) / 2) * (L : ℝ) <
        (⌊((1 + r) / 2) * (L : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    change ((1 + r) / 2) * (L : ℝ) - ⌊((1 + r) / 2) * (L : ℝ)⌋₊ < 1
    linarith
  · exact Nat.cast_sub hk

/-- The original score is the information rate times scale minus a bounded error. -/
theorem center_rounding (r : ℝ) (L : ℕ) (hr : 0 ≤ r) (hr1 : r < 1) :
    phi r * (L : ℝ) - Real.log ((1 + r) / (1 - r)) ≤ center r L ∧
      center r L ≤ phi r * (L : ℝ) := by
  obtain ⟨hk, hx0, hx1, hl⟩ := central_rounding r L hr hr1.le
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  have hc : 0 ≤ Real.log (1 + r) - Real.log (1 - r) :=
    sub_nonneg.mpr (Real.log_le_log hm (by linarith))
  have he : center r L = phi r * (L : ℝ) -
      (((1 + r) / 2) * (L : ℝ) - centralPositive r L) *
        (Real.log (1 + r) - Real.log (1 - r)) := by
    unfold center phi
    rw [hl]
    ring
  rw [he, Real.log_div hp.ne' hm.ne']
  constructor <;> nlinarith

/-- The base-two floor costs at most one factor of two. -/
theorem population_exponential_bounds (r β : ℝ) (L : ℕ)
    (hφ : 0 ≤ phi r) (hβ : 0 < β) :
    Real.exp (phi r / β * (L : ℝ)) / 2 ≤ (population r β L : ℝ) ∧
      (population r β L : ℝ) ≤ Real.exp (phi r / β * (L : ℝ)) := by
  let t := phi r * (L : ℝ) / (β * Real.log 2)
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hm : 0 < (population r β L : ℝ) := by unfold population; positivity
  have he : Real.log (population r β L : ℝ) = (⌊t⌋₊ : ℝ) * Real.log 2 := by
    simp [population, t, Real.log_pow]
  have hlo := mul_le_mul_of_nonneg_right (Nat.floor_le ht) hlog.le
  have hhi := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one t) hlog
  have hrate : t * Real.log 2 = phi r / β * (L : ℝ) := by
    dsimp [t]
    field_simp
  rw [← he, hrate] at hlo
  have hlower : phi r / β * (L : ℝ) - Real.log 2 ≤
      Real.log (population r β L : ℝ) := by
    rw [add_mul, one_mul, ← he, hrate] at hhi
    linarith
  constructor
  · have h := Real.exp_le_exp.mpr hlower
    simpa [Real.exp_sub, Real.exp_log hm, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  · simpa only [Real.exp_log hm] using Real.exp_le_exp.mpr hlo

/-- The fixed nonzero signal amplitude gives a strictly positive information rate. -/
theorem information_rate_bounds (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    0 < phi r ∧ phi r < Real.log 2 := by
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  have hstrict := Real.strictConvexOn_mul_log.2 hp.le hm.le
    (show 1 + r ≠ 1 - r by linarith) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  have he : (1/2 : ℝ) • (1+r) + (1/2 : ℝ) • (1-r) = 1 := by
    simp only [smul_eq_mul]; ring
  rw [he] at hstrict
  dsimp only at hstrict
  simp only [Real.log_one, mul_zero, smul_eq_mul] at hstrict
  have hlp : Real.log (1+r) < Real.log 2 := Real.log_lt_log hp (by linarith)
  have hlm : Real.log (1-r) < Real.log 2 := Real.log_lt_log hm (by linarith)
  have h1 := mul_lt_mul_of_pos_left hlp hp
  have h2 := mul_lt_mul_of_pos_left hlm hm
  unfold phi
  constructor <;> nlinarith

/-- The decimal tower dominates its index. -/
theorem decimalExponent_index (n : ℕ) : n + 1 ≤ decimalExponent n := by
  induction n with
  | zero => simp [decimalExponent]
  | succ n ih =>
    have h := Nat.mul_le_pow (a := 10) (by decide : 10 ≠ 1) (5 * decimalExponent n)
    rw [decimalExponent]
    omega

/-- The original integer scales tend to infinity. -/
theorem scale_tendsto : Tendsto (fun n => (scale n : ℝ)) atTop atTop := by
  have hd : Tendsto decimalExponent atTop atTop :=
    tendsto_atTop_mono (fun n => (Nat.le_succ n).trans (decimalExponent_index n)) tendsto_id
  have hQ : Tendsto denominator atTop atTop := by
    apply tendsto_atTop_mono _ hd
    intro n
    exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 10)).trans
      (Nat.mul_le_pow (a := 10) (by decide : 10 ≠ 1) (decimalExponent n))
  have hL : Tendsto scale atTop atTop := by
    apply tendsto_atTop_mono _ hQ
    intro n
    exact Nat.le_self_pow (by decide : 3 ≠ 0) (denominator n)
  exact tendsto_natCast_atTop_atTop.comp hL

/-- The second floor preserves the positive exponential signal rate. -/
theorem signal_exponential_bounds (r β : ℝ) (L : ℕ)
    (hr : 0 ≤ r) (hr1 : r < 1) (hφ : 0 ≤ phi r) (hβ : 0 < β)
    (hlarge : 4 ≤ Real.exp ((phi r / β - phi r) * (L : ℝ))) :
    Real.exp ((phi r / β - phi r) * (L : ℝ)) / 4 ≤ (signalSize r β L : ℝ) ∧
      (signalSize r β L : ℝ) ≤
        Real.exp ((phi r / β - phi r) * (L : ℝ) + Real.log ((1 + r) / (1 - r))) := by
  obtain ⟨hmlo, hmhi⟩ := population_exponential_bounds r β L hφ hβ
  obtain ⟨hzlo, hzhi⟩ := center_rounding r L hr hr1
  let X := (population r β L : ℝ) * Real.exp (-center r L)
  have hx : 0 < X := by dsimp [X]; unfold population; positivity
  have hlo : Real.exp ((phi r / β - phi r) * (L : ℝ)) / 2 ≤ X := by
    calc
      _ = Real.exp (phi r / β * (L : ℝ)) / 2 * Real.exp (-(phi r * (L : ℝ))) := by
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        congr 1 <;> ring
      _ ≤ X := mul_le_mul hmlo (Real.exp_le_exp.mpr (neg_le_neg hzhi))
        (Real.exp_pos _).le (by positivity)
  have hhi : X ≤ Real.exp ((phi r / β - phi r) * (L : ℝ) +
      Real.log ((1 + r) / (1 - r))) := by
    calc
      X ≤ Real.exp (phi r / β * (L : ℝ)) *
          Real.exp (-phi r * (L : ℝ) + Real.log ((1 + r) / (1 - r))) :=
        mul_le_mul hmhi (Real.exp_le_exp.mpr (by linarith only [hzlo]))
          (Real.exp_pos _).le (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hfloor : X < (signalSize r β L : ℝ) + 1 := Nat.lt_floor_add_one X
  exact ⟨by linarith only [hlarge, hlo, hfloor], (Nat.floor_le hx.le).trans hhi⟩

/-- The logarithmic error of the final floor is bounded by the reciprocal count. -/
theorem signal_log_rounding (r β : ℝ) (L : ℕ) (hq : 0 < signalSize r β L) :
    let X := (population r β L : ℝ) * Real.exp (-center r L)
    0 ≤ Real.log (X / signalSize r β L) ∧
      Real.log (X / signalSize r β L) ≤ 1 / signalSize r β L ∧
      Real.log (X / signalSize r β L) =
        Real.log (population r β L : ℝ) - center r L - Real.log (signalSize r β L : ℝ) := by
  dsimp only
  let X := (population r β L : ℝ) * Real.exp (-center r L)
  have hqR : (0 : ℝ) < signalSize r β L := by exact_mod_cast hq
  have hM : (0 : ℝ) < population r β L := by unfold population; positivity
  have hX : 0 < X := mul_pos hM (Real.exp_pos _)
  have hf : (signalSize r β L : ℝ) ≤ X := Nat.floor_le hX.le
  have hupper : X < (signalSize r β L : ℝ) + 1 := Nat.lt_floor_add_one X
  refine ⟨Real.log_nonneg ((le_div_iff₀ hqR).mpr (by simpa using hf)), ?_, ?_⟩
  · have hh := Real.log_le_sub_one_of_pos (div_pos hX hqR)
    apply hh.trans
    apply (le_div_iff₀ hqR).mpr
    field_simp at *
    linarith only [hupper]
  · rw [Real.log_div hX.ne' hqR.ne']
    dsimp [X]
    rw [Real.log_mul hM.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring

private theorem polynomial_ratio_zero (L : ℕ → ℝ) (D : ℕ → ℕ)
    (hL : Tendsto L atTop atTop) (hL0 : ∀ n, 0 ≤ L n)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) (p : ℕ)
    (hbound : ∀ᶠ n in atTop, Real.exp (c * L n) / C ≤ (D n : ℝ)) :
    Tendsto (fun n => L n ^ p / (D n : ℝ)) atTop (𝓝 0) := by
  have hz : Tendsto (fun n => C * L n ^ p * Real.exp (-c * L n)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p : ℝ) c hc).comp hL
    simpa only [Function.comp_apply, Real.rpow_natCast, mul_assoc, mul_zero] using h.const_mul C
  refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg
    (pow_nonneg (hL0 n) p) (Nat.cast_nonneg _)) ?_ hz
  filter_upwards [hbound] with n hn
  have hd : 0 < (D n : ℝ) := (div_pos (Real.exp_pos _) hC).trans_le hn
  calc
    L n ^ p / (D n : ℝ) = L n ^ p * (1 / (D n : ℝ)) := by ring
    _ ≤ L n ^ p * (1 / (Real.exp (c * L n) / C)) :=
      mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (div_pos (Real.exp_pos _) hC) hn)
        (pow_nonneg (hL0 n) p)
    _ = C * L n ^ p * Real.exp (-c * L n) := by
      rw [one_div_div, neg_mul, Real.exp_neg]
      ring

/-- Every fixed polynomial scale is negligible compared with both original integer populations. -/
theorem original_polynomial_scales (r β : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 0 < β) (hβ1 : β < 1) (p : ℕ) :
    Tendsto (fun n => (scale n : ℝ) ^ p / signalSize r β (scale n)) atTop (𝓝 0) ∧
      Tendsto (fun n => (scale n : ℝ) ^ p / population r β (scale n)) atTop (𝓝 0) := by
  have hφ := (information_rate_bounds r hr hr1).1
  have hcM : 0 < phi r / β := div_pos hφ hβ
  have hcq : 0 < phi r / β - phi r := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ hβ).mpr
    nlinarith only [hφ, hβ1]
  have hlarge : ∀ᶠ n in atTop,
      4 ≤ Real.exp ((phi r / β - phi r) * (scale n : ℝ)) :=
    (Real.tendsto_exp_atTop.comp (scale_tendsto.const_mul_atTop hcq)).eventually
      (eventually_ge_atTop 4)
  constructor
  · apply polynomial_ratio_zero (fun n => (scale n : ℝ))
      (fun n => signalSize r β (scale n)) scale_tendsto (fun _ => Nat.cast_nonneg _)
      (phi r / β - phi r) 4 hcq (by norm_num) p
    filter_upwards [hlarge] with n hn
    exact (signal_exponential_bounds r β (scale n) hr.le hr1 hφ.le hβ hn).1
  · exact polynomial_ratio_zero (fun n => (scale n : ℝ))
      (fun n => population r β (scale n)) scale_tendsto (fun _ => Nat.cast_nonneg _)
      (phi r / β) 2 hcM (by norm_num) p
      (Eventually.of_forall fun n => (population_exponential_bounds r β (scale n) hφ.le hβ).1)

/-- The original signal density decays faster than every fixed polynomial. -/
theorem original_density_scales (r β : ℝ) (hr : 0 < r) (hr1 : r < 1) (p : ℕ) :
    Tendsto (fun n => (scale n : ℝ) ^ p *
      ((signalSize r β (scale n) : ℝ) / population r β (scale n))) atTop (𝓝 0) := by
  have hφ := (information_rate_bounds r hr hr1).1
  let c := Real.log ((1+r)/(1-r))
  have hz : Tendsto (fun n => Real.exp c * (scale n : ℝ)^p *
      Real.exp (-phi r * (scale n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p : ℝ) (phi r) hφ).comp scale_tendsto
    simpa only [Function.comp_apply, Real.rpow_natCast, mul_assoc, mul_zero] using h.const_mul (Real.exp c)
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hz
  apply Eventually.of_forall
  intro n
  let L := scale n
  have hM : (0 : ℝ) < population r β L := by unfold population; positivity
  have hx : (signalSize r β L : ℝ) ≤ (population r β L : ℝ) * Real.exp (-center r L) :=
    Nat.floor_le (by positivity)
  have hd : (signalSize r β L : ℝ) / population r β L ≤ Real.exp (-center r L) :=
    (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hx)
  have hcenter := (center_rounding r L hr.le hr1).1
  calc
    (scale n : ℝ)^p * ((signalSize r β L : ℝ)/population r β L) ≤
        (scale n : ℝ)^p * Real.exp (-center r L) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ (scale n : ℝ)^p * Real.exp (c - phi r * (scale n : ℝ)) := by
      gcongr
      dsimp [c, L] at *
      linarith only [hcenter]
    _ = _ := by rw [Real.exp_sub, neg_mul, Real.exp_neg]; ring

private theorem small_log_bounds (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    |Real.log (1-u)| ≤ 2*u ∧ |Real.log (1+u)| ≤ u := by
  have hm : 0 < 1-u := by linarith
  have hp : 0 < 1+u := by linarith
  have hlo := Real.one_sub_inv_le_log_of_pos hm
  have hinv : (1-u)⁻¹ ≤ 1+2*u := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hm).mpr
    nlinarith only [hu, hu1]
  have hneg : Real.log (1-u) ≤ 0 := Real.log_nonpos hm.le (by linarith)
  have hpos : 0 ≤ Real.log (1+u) := Real.log_nonneg (by linarith)
  rw [abs_of_nonpos hneg, abs_of_nonneg hpos]
  exact ⟨by linarith only [hlo, hinv], by
    have h := Real.log_le_sub_one_of_pos hp
    linarith only [h]⟩

/-- The exact final-floor error and compensation determine the original A-logit. -/
theorem cell_logit_identity (r β : ℝ) (L : ℕ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hq : 0 < signalSize r β L) (hqm : signalSize r β L < population r β L)
    (hc : compensation (population r β L) (signalSize r β L) r < 1) :
    let M := population r β L
    let q := signalSize r β L
    let ε := compensation M q r
    let X := (M : ℝ) * Real.exp (-center r L)
    cellLogit r β L =
      -(centralPositive r L : ℝ) * Real.log (1-ε) -
        (centralNegative r L : ℝ) * Real.log (1+ε) -
        Real.log (X/q) - Real.log (1-(q : ℝ)/M) := by
  dsimp only
  let M := population r β L
  let q := signalSize r β L
  let ε := compensation M q r
  have hM : (0 : ℝ) < M := by dsimp [M]; unfold population; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsub : (0 : ℝ) < (M-q : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hqm
  have hsubeq : ((M-q : ℕ) : ℝ) = (M : ℝ) - q := Nat.cast_sub hqm.le
  have hε : 0 ≤ ε := by dsimp [ε, compensation]; positivity
  have hminus : 0 < 1-ε := by dsimp [ε, M, q] at *; linarith only [hc]
  have hplus : 0 < 1+ε := by linarith only [hε]
  have hpr : 0 < 1+r := by linarith only [hr]
  have hmr : 0 < 1-r := by linarith only [hr1]
  have hp : 0 < 1-(q : ℝ)/M := by
    apply sub_pos.mpr
    apply (div_lt_one hM).mpr
    exact_mod_cast hqm
  have he : 1-(q : ℝ)/M = ((M-q : ℕ) : ℝ)/M := by
    rw [hsubeq]
    field_simp
  have hlogp : Real.log (1-(q : ℝ)/M) = Real.log ((M-q : ℕ) : ℝ)-Real.log (M : ℝ) := by
    rw [he, Real.log_div hsub.ne' hM.ne']
  have hround := (signal_log_rounding r β L hq).2.2
  change cellLogit r β L = _
  unfold cellLogit
  dsimp only
  rw [hround, hlogp]
  rw [Real.log_div hpr.ne' hminus.ne', Real.log_div hmr.ne' hplus.ne',
    Real.log_div hsub.ne' hqR.ne']
  unfold center
  ring

/-- The exact original A-logit has a reciprocal-count and compensation error bound. -/
theorem cell_logit_bound (r β : ℝ) (L : ℕ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hq : 0 < signalSize r β L) (hqm : signalSize r β L < population r β L)
    (hc : compensation (population r β L) (signalSize r β L) r ≤ 1/2)
    (hp : (signalSize r β L : ℝ)/population r β L ≤ 1/2) :
    |cellLogit r β L| ≤
      2*(L : ℝ)*compensation (population r β L) (signalSize r β L) r +
        1/(signalSize r β L : ℝ) +
        2*((signalSize r β L : ℝ)/population r β L) := by
  let M := population r β L
  let q := signalSize r β L
  let ε := compensation M q r
  let p := (q : ℝ)/M
  let η := Real.log ((M : ℝ)*Real.exp (-center r L)/q)
  have hε : 0 ≤ ε := by dsimp [ε, compensation]; positivity
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have he := cell_logit_identity r β L hr hr1 hq hqm (by linarith only [hc])
  have hlogs := small_log_bounds ε hε hc
  have hlogp := (small_log_bounds p hp0 hp).1
  have hη := signal_log_rounding r β L hq
  dsimp only at hη
  have hk : 0 ≤ (centralPositive r L : ℝ) := Nat.cast_nonneg _
  have hl : 0 ≤ (centralNegative r L : ℝ) := Nat.cast_nonneg _
  have hsum : (centralPositive r L : ℝ)+(centralNegative r L : ℝ) = L := by
    rw [(central_rounding r L hr hr1.le).2.2.2]
    ring
  dsimp only at he
  rw [he]
  calc
    _ ≤ |-(centralPositive r L : ℝ)*Real.log (1-ε)| +
        |(centralNegative r L : ℝ)*Real.log (1+ε)| + |η| + |Real.log (1-p)| := by
      apply le_trans (abs_sub _ _)
      apply add_le_add_left
      apply le_trans (abs_sub _ _)
      apply add_le_add_left
      exact abs_sub _ _
    _ = (centralPositive r L : ℝ)*|Real.log (1-ε)| +
        (centralNegative r L : ℝ)*|Real.log (1+ε)| + η + |Real.log (1-p)| := by
      rw [abs_mul, abs_neg, abs_of_nonneg hk, abs_mul, abs_of_nonneg hl,
        abs_of_nonneg hη.1]
    _ ≤ (centralPositive r L : ℝ)*(2*ε) +
        (centralNegative r L : ℝ)*ε + 1/(q : ℝ) + 2*p := by
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hlogs.1 hk)
        (mul_le_mul_of_nonneg_left hlogs.2 hl)) hη.2.1) hlogp
    _ ≤ _ := by
      change (centralPositive r L : ℝ)*(2*ε) +
        (centralNegative r L : ℝ)*ε + 1/(q : ℝ) + 2*p ≤
        2*(L : ℝ)*ε + 1/(q : ℝ) + 2*p
      have hs := congrArg (fun z : ℝ => z*ε) hsum
      nlinarith only [hs, mul_nonneg hl hε]

private theorem compensation_density_bound (M q : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hqm : q < M) (hp : (q : ℝ)/M ≤ 1/2) :
    compensation M q r ≤ 2*r*((q : ℝ)/M) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hden : (0 : ℝ) < ((M-q : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hqm
  have hhalf : (M : ℝ)/2 ≤ ((M-q : ℕ) : ℝ) := by
    rw [Nat.cast_sub hqm.le]
    have h := (div_le_iff₀ hM).mp hp
    linarith only [h]
  calc
    compensation M q r ≤ r*(q : ℝ)/((M : ℝ)/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hhalf
    _ = _ := by ring

/-- The two integer populations eventually exceed every fixed threshold. -/
theorem original_populations_tendsto (r β : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n => (signalSize r β (scale n) : ℝ)) atTop atTop ∧
      Tendsto (fun n => (population r β (scale n) : ℝ)) atTop atTop := by
  have hφ := (information_rate_bounds r hr hr1).1
  have hcq : 0 < phi r / β - phi r := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ hβ).mpr
    nlinarith only [hφ, hβ1]
  have hqexp := Real.tendsto_exp_atTop.comp (scale_tendsto.const_mul_atTop hcq)
  have hMexp := Real.tendsto_exp_atTop.comp (scale_tendsto.const_mul_atTop (div_pos hφ hβ))
  constructor
  · apply tendsto_atTop_mono' atTop _ (hqexp.atTop_div_const (by norm_num : (0 : ℝ) < 4))
    filter_upwards [hqexp.eventually (eventually_ge_atTop 4)] with n hn
    exact (signal_exponential_bounds r β (scale n) hr.le hr1 hφ.le hβ hn).1
  · exact tendsto_atTop_mono
      (fun n => (population_exponential_bounds r β (scale n) hφ.le hβ).1)
      (hMexp.atTop_div_const (by norm_num : (0 : ℝ) < 2))

/-- The original compensation is negligible at every fixed polynomial scale. -/
theorem original_compensation_scales (r β : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (p : ℕ) :
    Tendsto (fun n => (scale n : ℝ)^p *
      compensation (population r β (scale n)) (signalSize r β (scale n)) r)
      atTop (𝓝 0) := by
  have hd := original_density_scales r β hr hr1 0
  simp only [pow_zero, one_mul] at hd
  have hh : ∀ᶠ n in atTop,
      (signalSize r β (scale n) : ℝ)/population r β (scale n) < 1/2 :=
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hz := (original_density_scales r β hr hr1 p).const_mul (2*r)
  simp only [mul_zero] at hz
  refine squeeze_zero' (Eventually.of_forall fun n => by unfold compensation; positivity) ?_ hz
  filter_upwards [hh] with n hn
  have hM : (0 : ℝ) < population r β (scale n) := by unfold population; positivity
  have hqm : signalSize r β (scale n) < population r β (scale n) := by
    have hratio : (signalSize r β (scale n) : ℝ)/population r β (scale n) < 1 := by linarith only [hn]
    exact_mod_cast (div_lt_one hM).mp hratio
  have hb := compensation_density_bound _ _ r hr.le hqm hn.le
  calc
    _ ≤ (scale n : ℝ)^p * (2*r*((signalSize r β (scale n) : ℝ)/population r β (scale n))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- The original A-logit error is smaller than any fixed constant divided by scale. -/
theorem original_cell_logit_precision (r β : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n => (scale n : ℝ)*|cellLogit r β (scale n)|) atTop (𝓝 0) := by
  have hq := (original_populations_tendsto r β hr hr1 hβ hβ1).1
  have hden := original_density_scales r β hr hr1 0
  simp only [pow_zero, one_mul] at hden
  have hcomp := original_compensation_scales r β hr hr1 0
  simp only [pow_zero, one_mul] at hcomp
  have hz := (((original_compensation_scales r β hr hr1 2).const_mul 2).add
    (original_polynomial_scales r β hr hr1 hβ hβ1 1).1).add
    ((original_density_scales r β hr hr1 1).const_mul 2)
  simp only [mul_zero, zero_add, pow_one] at hz
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hz
  filter_upwards [hq.eventually (eventually_gt_atTop 0),
    hden.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    hcomp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with n hnq hnp hnc
  have hqN : 0 < signalSize r β (scale n) := by exact_mod_cast hnq
  have hM : (0 : ℝ) < population r β (scale n) := by unfold population; positivity
  have hqm : signalSize r β (scale n) < population r β (scale n) := by
    have hratio : (signalSize r β (scale n) : ℝ)/population r β (scale n) < 1 := by linarith only [hnp]
    exact_mod_cast (div_lt_one hM).mp hratio
  have hb := mul_le_mul_of_nonneg_left
    (cell_logit_bound r β (scale n) hr.le hr1 hqN hqm hnc.le hnp.le)
    (show (0 : ℝ) ≤ scale n from Nat.cast_nonneg _)
  convert hb using 1 <;> first | rfl | ring

/-- Any prescribed root-origin precision and the occupancy log interval hold eventually. -/
theorem original_cell_logit_bounds (r β κ₀ : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ₀) :
    ∀ᶠ n in atTop,
      |cellLogit r β (scale n)| ≤ κ₀/(2*(scale n : ℝ)) ∧
      Real.log (7/8) ≤ -cellLogit r β (scale n) ∧
      -cellLogit r β (scale n) ≤ Real.log (9/8) := by
  have hprec := original_cell_logit_precision r β hr hr1 hβ hβ1
  have habs : Tendsto (fun n => |cellLogit r β (scale n)|) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) ?_ hprec
    filter_upwards [scale_tendsto.eventually (eventually_ge_atTop 1)] with n hn
    nlinarith only [hn, abs_nonneg (cellLogit r β (scale n))]
  have hlo : 0 < -Real.log (7/8 : ℝ) := by
    have h := Real.log_neg (by norm_num : (0 : ℝ) < 7/8) (by norm_num : (7/8 : ℝ) < 1)
    linarith only [h]
  have hhi : 0 < Real.log (9/8 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [hprec.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < κ₀/2)),
    habs.eventually (gt_mem_nhds hlo), habs.eventually (gt_mem_nhds hhi),
    scale_tendsto.eventually (eventually_gt_atTop 0)] with n hn hnl hnh hL
  refine ⟨(le_div_iff₀ (by positivity : 0 < 2*(scale n : ℝ))).mpr (by nlinarith only [hn]), ?_, ?_⟩
  · have h := (abs_le.mp hnl.le).2
    linarith only [h]
  · have h := (abs_le.mp hnh.le).1
    linarith only [h]

/-- The fixed Chernoff exponent dominates both population growth and squared odds growth. -/
theorem original_tail_rates (r β : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 1/2 < β) :
    0 < (8*Real.log 4-6)-phi r/β ∧
      0 < (8*Real.log 4-6)-2*phi r := by
  have hφ := information_rate_bounds r hr hr1
  have hβ0 : 0 < β := by linarith only [hβ]
  have hrate : phi r/β < 2*phi r := by
    apply (div_lt_iff₀ hβ0).mpr
    nlinarith only [hβ, hφ.1]
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by norm_num at hlog ⊢; exact hlog
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  constructor <;> nlinarith only [hφ.2, hrate, hlog2]

/-- Both all-row tail payments decay at the original scale. -/
theorem original_tail_scales (r β : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 1/2 < β) (hβ1 : β < 1) (p : ℕ) :
    Tendsto (fun n => (scale n : ℝ)^p * population r β (scale n) *
      Real.exp (-((8*Real.log 4-6)*(scale n : ℝ)))) atTop (𝓝 0) ∧
    Tendsto (fun n => (scale n : ℝ)^p *
      ((population r β (scale n) : ℝ)/signalSize r β (scale n))^2 *
      Real.exp (-((8*Real.log 4-6)*(scale n : ℝ)))) atTop (𝓝 0) := by
  have hφ := (information_rate_bounds r hr hr1).1
  have hβ0 : 0 < β := by linarith only [hβ]
  obtain ⟨hIM, hIq⟩ := original_tail_rates r β hr hr1 hβ
  let I := 8*Real.log 4-6
  constructor
  · have hz := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (p : ℝ) (I-phi r/β) hIM).comp scale_tendsto
    simp only [Function.comp_apply, Real.rpow_natCast] at hz
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hz
    apply Eventually.of_forall
    intro n
    have hm := (population_exponential_bounds r β (scale n) hφ.le hβ0).2
    calc
      _ ≤ (scale n : ℝ)^p * Real.exp (phi r/β*(scale n : ℝ)) *
          Real.exp (-(I*(scale n : ℝ))) := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 1; ring
  · have hcq : 0 < phi r/β-phi r := by
      apply sub_pos.mpr
      apply (lt_div_iff₀ hβ0).mpr
      nlinarith only [hφ, hβ1]
    have hlarge := (Real.tendsto_exp_atTop.comp
      (scale_tendsto.const_mul_atTop hcq)).eventually (eventually_ge_atTop 4)
    have hz := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (p : ℝ) (I-2*phi r) hIq).comp scale_tendsto).const_mul 16
    simp only [Function.comp_apply, Real.rpow_natCast, mul_zero] at hz
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hz
    filter_upwards [hlarge] with n hn
    have hq := (signal_exponential_bounds r β (scale n) hr.le hr1 hφ.le hβ0 hn).1
    have hqpos : (0 : ℝ) < signalSize r β (scale n) :=
      (div_pos (Real.exp_pos _) (by norm_num)).trans_le hq
    have hm := (population_exponential_bounds r β (scale n) hφ.le hβ0).2
    have hratio : (population r β (scale n) : ℝ)/signalSize r β (scale n) ≤
        4*Real.exp (phi r*(scale n : ℝ)) := by
      calc
        _ ≤ Real.exp (phi r/β*(scale n : ℝ)) /
            (Real.exp ((phi r/β-phi r)*(scale n : ℝ))/4) :=
          div_le_div₀ (by positivity) hm (by positivity) hq
        _ = _ := by
          rw [div_div_eq_mul_div, mul_comm (Real.exp _) (4 : ℝ), mul_div_assoc, ← Real.exp_sub]
          congr 1
          ring
    calc
      _ ≤ (scale n : ℝ)^p * (4*Real.exp (phi r*(scale n : ℝ)))^2 *
          Real.exp (-(I*(scale n : ℝ))) := by gcongr
      _ = 16*((scale n : ℝ)^p*Real.exp (-(I-2*phi r)*(scale n : ℝ))) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num only [Nat.cast_ofNat, show (4 : ℝ)^2 = 16 by norm_num]
        rw [show (scale n : ℝ)^p*(16*Real.exp (2*(phi r*(scale n : ℝ))))*
            Real.exp (-(I*(scale n : ℝ))) =
          16*((scale n : ℝ)^p*(Real.exp (2*(phi r*(scale n : ℝ)))*
            Real.exp (-(I*(scale n : ℝ))))) by ring, ← Real.exp_add]
        congr 2
        ring

/-- A deterministic budget shared by all supports and both native experiments. -/
def failureBudget (r β C : ℝ) (n : ℕ) : ℝ :=
  let L := (scale n : ℝ)
  let M := (population r β (scale n) : ℝ)
  let q := (signalSize r β (scale n) : ℝ)
  let ζ := Real.exp (-((8*Real.log 4-6)*L))
  C*(L^2/q+L^5/M+L^2*(M/q)^2*ζ+M*ζ)

/-- The four payments in the native uniform failure budget tend to zero. -/
theorem original_failure_budget_zero (r β C : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 1/2 < β) (hβ1 : β < 1) :
    Tendsto (failureBudget r β C) atTop (𝓝 0) := by
  have hβ0 : 0 < β := by linarith only [hβ]
  have h1 := (original_polynomial_scales r β hr hr1 hβ0 hβ1 2).1
  have h2 := (original_polynomial_scales r β hr hr1 hβ0 hβ1 5).2
  have h3 := (original_tail_scales r β hr hr1 hβ hβ1 2).2
  have h4 := (original_tail_scales r β hr hr1 hβ hβ1 0).1
  simp only [pow_zero, one_mul] at h4
  unfold failureBudget
  simpa only [zero_add, mul_zero, mul_one] using (((h1.add h2).add h3).add h4).const_mul C

private theorem eventually_four_sqrt_scale (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n in atTop, 4*Real.sqrt (scale n : ℝ) ≤ c*(scale n : ℝ) := by
  filter_upwards [(Real.tendsto_sqrt_atTop.comp scale_tendsto).eventually
    (eventually_ge_atTop (4/c))] with n hn
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mp hn) (Real.sqrt_nonneg (scale n : ℝ))
  simp only [Function.comp_apply] at h
  have hs := congrArg (fun z : ℝ => c*z)
    (Real.sq_sqrt (show (0 : ℝ) ≤ scale n from Nat.cast_nonneg _))
  nlinarith only [h, hs]

/-- Exact finite scale premises for the native relative, occupancy and variance interfaces. -/
theorem original_native_scale_conditions (r β A η : ℝ) (M₀ : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hβ : 0 < β) (hβ1 : β < 1) (hη : 0 < η) :
    ∀ᶠ n in atTop,
      M₀ ≤ population r β (scale n) ∧ 1 ≤ signalSize r β (scale n) ∧
      signalSize r β (scale n) < population r β (scale n) ∧
      4 ≤ scale n ∧ 6 ≤ population r β (scale n) ∧
      compensation (population r β (scale n)) (signalSize r β (scale n)) r ≤ (1+r)/2 ∧
      (scale n : ℝ)/population r β (scale n) ≤ η ∧
      (scale n : ℝ)/population r β (scale n) ≤ 1/45 ∧
      A*(scale n : ℝ)^2/population r β (scale n) ≤ 1/2 ∧
      15 ≤ ((1+r)/2)*(scale n : ℝ) ∧
      30 ≤ ((1-r)/2)*(scale n : ℝ) ∧
      4*Real.sqrt (scale n : ℝ) ≤ ((1+r)/2)*(scale n : ℝ) ∧
      4*Real.sqrt (scale n : ℝ) ≤ ((1-r)/2)*(scale n : ℝ) := by
  have ha : 0 < (1+r)/2 := by linarith only [hr]
  have hb : 0 < (1-r)/2 := by linarith only [hr1]
  obtain ⟨hq, hM⟩ := original_populations_tendsto r β hr hr1 hβ hβ1
  have hd := original_density_scales r β hr hr1 0
  have hc := original_compensation_scales r β hr hr1 0
  simp only [pow_zero, one_mul] at hd hc
  have hLM := (original_polynomial_scales r β hr hr1 hβ hβ1 1).2
  have hALM := ((original_polynomial_scales r β hr hr1 hβ hβ1 2).2).const_mul A
  simp only [pow_one] at hLM
  simp only [mul_zero] at hALM
  filter_upwards [hM.eventually (eventually_ge_atTop (M₀ : ℝ)),
    hq.eventually (eventually_ge_atTop 1), hM.eventually (eventually_ge_atTop 6),
    scale_tendsto.eventually (eventually_ge_atTop 4),
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hc.eventually (gt_mem_nhds ha), hLM.eventually (gt_mem_nhds hη),
    hLM.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/45)),
    hALM.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    (scale_tendsto.const_mul_atTop ha).eventually (eventually_ge_atTop 15),
    (scale_tendsto.const_mul_atTop hb).eventually (eventually_ge_atTop 30),
    eventually_four_sqrt_scale ((1+r)/2) ha,
    eventually_four_sqrt_scale ((1-r)/2) hb] with n hM₀ hq1 hM6 hL4 hden hcomp hLη hL45 hA haL hbL haS hbS
  have hM0 : (0 : ℝ) < population r β (scale n) := by unfold population; positivity
  have hqm : signalSize r β (scale n) < population r β (scale n) := by
    exact_mod_cast (div_lt_one hM0).mp hden
  exact ⟨by exact_mod_cast hM₀, by exact_mod_cast hq1, hqm,
    by exact_mod_cast hL4, by exact_mod_cast hM6, hcomp.le, hLη.le, hL45.le,
    by simpa only [← mul_div_assoc] using hA.le, haL, hbL, haS, hbS⟩

end
end D5.S3.Estimation.TimeArrow.NativeGrowthRounding
