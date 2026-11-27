/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entire log-power coefficients, the normalized null-diamond mixed derivative. -/

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! Log-power series on the positive axis and their entire coefficient functions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Set
open scoped Topology

namespace NullConeGravity

def pk (k : ℕ) : ℂ := 1 / ((k.factorial : ℂ) * ((k+1).factorial : ℂ))

def bk (k : ℕ) : ℂ :=
  (harmonic k : ℂ) + (harmonic (k+1) : ℂ) - 2 * (Real.eulerMascheroniConstant : ℂ)

private def powerSum (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' k, a k * z ^ k

private def weight (m : ℕ) (a : ℕ → ℂ) (k : ℕ) : ℂ := (k + 1 : ℂ)^m * a k

private def bCoeff (k : ℕ) : ℂ := bk k * pk k

def besselP : ℂ → ℂ := powerSum pk

def besselB : ℂ → ℂ := powerSum bCoeff

def besselP2 : ℂ → ℂ := powerSum (weight 2 pk)

def besselB2 : ℂ → ℂ := powerSum fun k =>
  (((k + 1 : ℂ)^2 * bk k) - 2 * (k + 1 : ℂ)) * pk k

def bulkDifference (M : ℝ) (q : ℂ) : ℂ :=
  let t := (M : ℂ)^2 * q / 4
  ((M : ℂ)^2 / (16 * (Real.pi : ℂ)^2)) *
    (Complex.log t * besselP t - besselB t)

def correctionLog (M : ℝ) (t ell : ℂ) : ℂ :=
  ((M : ℂ)^2 / (16 * (Real.pi : ℂ)^2)) * (ell * besselP2 t - besselB2 t)

def correction (M u v x : ℝ) : ℂ :=
  if x < 1 then
    correctionLog M ((M^2 * u*v*(1-x)/2 : ℝ) : ℂ)
      (Real.log (M^2 * u*v*(1-x)/2) : ℂ)
  else 0

private def FactorialBound (a : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ k : ℕ, ‖a k‖ ≤ C * (k + 1 : ℝ)^m / k.factorial

private theorem harmonic_bounds (k : ℕ) : 0 ≤ harmonic k ∧ harmonic k ≤ (k : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : (1 : ℚ) ≤ (k : ℚ) + 1 := by linarith [Nat.cast_nonneg (α := ℚ) k]
    rw [harmonic_succ, Nat.cast_succ]
    constructor
    · exact add_nonneg ih.1 (inv_nonneg.mpr (by positivity))
    · have hi : ((k : ℚ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
      linarith [ih.2]

private theorem norm_bk_le (k : ℕ) :
    ‖bk k‖ ≤ (2 + 2 * ‖Real.eulerMascheroniConstant‖) * (k + 1 : ℝ) := by
  have h (n : ℕ) : ‖(harmonic n : ℂ)‖ ≤ (n : ℝ) := by
    rw [Complex.norm_ratCast, abs_of_nonneg (by exact_mod_cast (harmonic_bounds n).1)]
    exact_mod_cast (harmonic_bounds n).2
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  calc
    ‖bk k‖ ≤ ‖(harmonic k : ℂ)‖ + ‖(harmonic (k+1) : ℂ)‖ +
        2 * ‖Real.eulerMascheroniConstant‖ := by
      unfold bk
      calc
        _ ≤ ‖(harmonic k : ℂ) + (harmonic (k+1) : ℂ)‖ +
            ‖2 * (Real.eulerMascheroniConstant : ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by
          rw [norm_mul, Complex.norm_real, show ‖(2 : ℂ)‖ = 2 by norm_num]
          exact add_le_add_left (norm_add_le _ _) _
    _ ≤ _ := by
      have hk1 := h (k+1)
      push_cast at hk1
      nlinarith [h k, hk1, norm_nonneg Real.eulerMascheroniConstant,
        mul_nonneg hk (norm_nonneg Real.eulerMascheroniConstant)]

private theorem norm_pk_le (k : ℕ) : ‖pk k‖ ≤ 1 / (k.factorial : ℝ) := by
  have h : (1 : ℝ) ≤ ((k+1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k+1)
  simp only [pk, norm_div, norm_one, norm_mul, Complex.norm_natCast]
  exact one_div_le_one_div_of_le (by positivity) (le_mul_of_one_le_right (by positivity) h)

private theorem pk_bound : FactorialBound pk :=
  ⟨1, zero_le_one, 0, fun k => by simpa using norm_pk_le k⟩

private theorem bCoeff_bound : FactorialBound bCoeff := by
  refine ⟨2 + 2 * ‖Real.eulerMascheroniConstant‖, by positivity, 1, fun k => ?_⟩
  rw [bCoeff, norm_mul, pow_one, show (2 + 2 * ‖Real.eulerMascheroniConstant‖) *
    (k + 1 : ℝ) / k.factorial = (2 + 2 * ‖Real.eulerMascheroniConstant‖) *
      (k + 1 : ℝ) * (1 / k.factorial) by ring]
  exact mul_le_mul (norm_bk_le k) (norm_pk_le k) (norm_nonneg _) (by positivity)

private theorem FactorialBound.weight {a : ℕ → ℂ} (ha : FactorialBound a) (d : ℕ) :
    FactorialBound (weight d a) := by
  obtain ⟨C, hC, m, hm⟩ := ha
  refine ⟨C, hC, d + m, fun k => ?_⟩
  have hk : (k + 1 : ℂ) = ((k+1 : ℕ) : ℂ) := by push_cast; rfl
  rw [NullConeGravity.weight, norm_mul, norm_pow, hk, Complex.norm_natCast, Nat.cast_add,
    Nat.cast_one, pow_add]
  calc
    _ ≤ (k + 1 : ℝ)^d * (C * (k + 1 : ℝ)^m / k.factorial) :=
      mul_le_mul_of_nonneg_left (hm k) (by positivity)
    _ = _ := by ring

private theorem FactorialBound.shift {a : ℕ → ℂ} (ha : FactorialBound a) :
    FactorialBound (fun k => a (k + 1)) := by
  obtain ⟨C, hC, m, hm⟩ := ha
  refine ⟨C * 2^m, by positivity, m, fun k => (hm (k+1)).trans ?_⟩
  have hfac : (k.factorial : ℝ) ≤ ((k+1).factorial : ℝ) :=
    by exact_mod_cast Nat.factorial_le (Nat.le_succ k)
  have hbase : (↑(k+1) + 1 : ℝ) ≤ 2 * (k+1 : ℝ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]
  calc
    _ ≤ C * (↑(k+1) + 1 : ℝ)^m / k.factorial := by gcongr
    _ ≤ C * (2 * (k + 1 : ℝ))^m / k.factorial := by gcongr
    _ = _ := by rw [mul_pow, mul_assoc]

private theorem factorialMajorant (C R : ℝ) (m : ℕ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    Summable (fun k : ℕ => C * (k + 1 : ℝ)^m / k.factorial * R^k) := by
  have hpow (k : ℕ) : (k+1 : ℝ) ≤ 2^k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ, Nat.cast_succ]
      linarith [Nat.cast_nonneg (α := ℝ) k]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
    ((Real.summable_pow_div_factorial (2^m * R)).mul_left C)
  calc
    _ ≤ C * (2^k : ℝ)^m / k.factorial * R^k := by gcongr; exact hpow k
    _ = _ := by rw [pow_right_comm (2 : ℝ) k m, mul_pow]; ring

private theorem powerSum_summable {a : ℕ → ℂ} (ha : FactorialBound a) (z : ℂ) :
    Summable (fun k => a k * z^k) := by
  obtain ⟨C, hC, m, hm⟩ := ha
  refine Summable.of_norm_bounded (factorialMajorant C ‖z‖ m hC (norm_nonneg _)) fun k => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hm k) (by positivity)

private theorem powerSum_shift {a : ℕ → ℂ} (ha : FactorialBound a) (z : ℂ) :
    powerSum a z = a 0 + z * powerSum (fun k => a (k+1)) z := by
  unfold powerSum
  rw [(powerSum_summable ha z).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, mul_one, pow_succ]
  congr 1
  exact tsum_congr fun k => by ring

private theorem hasDerivAt_mul_powerSum {a : ℕ → ℂ} (ha : FactorialBound a) (z : ℂ) :
    HasDerivAt (fun y => y * powerSum a y) (powerSum (weight 1 a) z) z := by
  obtain ⟨C, hC, m, hm⟩ := ha.weight 1
  let R := ‖z‖ + 1
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    simp [Metric.mem_ball, R]
  have hf : HasDerivAt (fun y : ℂ => ∑' k, a k * y^(k+1))
      (powerSum (weight 1 a) z) z := by
    apply hasDerivAt_tsum_of_isPreconnected
      (factorialMajorant C R m hC (by dsimp [R]; positivity))
      Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected ?_ ?_ hz ?_ hz
    · intro k y _
      simpa only [weight, pow_one, Nat.cast_succ, Nat.add_one_sub_one, mul_comm (a k), mul_assoc]
        using (hasDerivAt_pow (k+1) y).const_mul (a k)
    · intro k y hy
      have hy' : ‖y‖ ≤ R := le_of_lt (by simpa [Metric.mem_ball] using hy)
      rw [norm_mul, norm_pow]
      exact mul_le_mul (hm k) (pow_le_pow_left₀ (norm_nonneg _) hy' k)
        (by positivity) (by positivity)
    · simpa only [pow_succ, ← mul_assoc] using (powerSum_summable ha z).mul_right z
  convert hf using 1
  ext y
  rw [powerSum, ← tsum_mul_left]
  exact tsum_congr fun k => by rw [pow_succ]; ring

private theorem hasDerivAt_powerSum {a : ℕ → ℂ} (ha : FactorialBound a) (z : ℂ) :
    HasDerivAt (powerSum a) (powerSum (weight 1 (fun k => a (k+1))) z) z := by
  simpa only [← powerSum_shift ha] using (hasDerivAt_mul_powerSum ha.shift z).const_add (a 0)

private def firstP : ℂ → ℂ := powerSum (weight 1 pk)
private def firstB : ℂ → ℂ := powerSum (weight 1 bCoeff)
private def secondB : ℂ → ℂ := powerSum (weight 1 (fun k => weight 1 bCoeff (k+1)))

private theorem besselB2_eq (z : ℂ) :
    besselB2 z = powerSum (weight 2 bCoeff) z - 2 * firstP z := by
  unfold besselB2 firstP powerSum
  rw [← tsum_mul_left, ← ((powerSum_summable (bCoeff_bound.weight 2) z).tsum_sub
    ((powerSum_summable (pk_bound.weight 1) z).mul_left 2))]
  exact tsum_congr fun k => by unfold weight bCoeff; ring

theorem besselP_entire : Differentiable ℂ besselP :=
  fun z => (hasDerivAt_powerSum pk_bound z).differentiableAt

theorem besselB_entire : Differentiable ℂ besselB :=
  fun z => (hasDerivAt_powerSum bCoeff_bound z).differentiableAt

theorem besselP2_entire : Differentiable ℂ besselP2 :=
  fun z => (hasDerivAt_powerSum (pk_bound.weight 2) z).differentiableAt

theorem besselB2_entire : Differentiable ℂ besselB2 := by
  have he : besselB2 = fun z => powerSum (weight 2 bCoeff) z - 2 * firstP z :=
    funext besselB2_eq
  rw [he]
  have h : Differentiable ℂ (powerSum (weight 2 bCoeff)) :=
    fun z => (hasDerivAt_powerSum (bCoeff_bound.weight 2) z).differentiableAt
  have hp : Differentiable ℂ firstP :=
    fun z => (hasDerivAt_powerSum (pk_bound.weight 1) z).differentiableAt
  exact h.sub ((differentiable_const (c := (2 : ℂ))).mul hp)

private theorem pk_succ (k : ℕ) : (k+1 : ℂ) * (k+2) * pk (k+1) = pk k := by
  have h1 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h2 : (k + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k+1)
  have hf (n : ℕ) : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  unfold pk
  rw [Nat.factorial_succ (k+1), Nat.factorial_succ k]
  push_cast
  rw [show (k : ℂ) + 1 + 1 = k + 2 by ring]
  field_simp [hf, h1, h2]

private theorem bk_succ (k : ℕ) : bk (k+1) - bk k = (k+1 : ℂ)⁻¹ + (k+2 : ℂ)⁻¹ := by
  unfold bk
  rw [harmonic_succ (k+1), harmonic_succ k]
  push_cast
  ring

private theorem hasDerivAt_firstP (z : ℂ) : HasDerivAt firstP (besselP z) z := by
  change HasDerivAt (powerSum (weight 1 pk)) (besselP z) z
  convert hasDerivAt_powerSum (pk_bound.weight 1) z using 1
  unfold besselP powerSum
  exact tsum_congr fun k => by
    simp only [weight, pow_one, Nat.cast_add, Nat.cast_one]
    rw [← pk_succ k]
    ring

private theorem hasDerivAt_firstB (z : ℂ) : HasDerivAt firstB (secondB z) z :=
  hasDerivAt_powerSum (bCoeff_bound.weight 1) z

private theorem powerSum_weight_two {a : ℕ → ℂ} (ha : FactorialBound a) (z : ℂ) :
    powerSum (weight 2 a) z = powerSum (weight 1 a) z +
      z * powerSum (weight 1 (fun k => weight 1 a (k+1))) z := by
  let d : ℕ → ℂ := fun k => weight 2 a k - weight 1 a k
  have hs : Summable (fun k => d k * z^k) := by
    simpa only [d, sub_mul] using (powerSum_summable (ha.weight 2) z).sub
      (powerSum_summable (ha.weight 1) z)
  have hsplit := hs.tsum_eq_zero_add
  simp only [d, weight, Nat.cast_zero, zero_add, one_pow, pow_one, one_mul, sub_self,
    zero_mul, zero_add] at hsplit
  unfold powerSum
  rw [← sub_eq_iff_eq_add', ← (powerSum_summable (ha.weight 2) z).tsum_sub
    (powerSum_summable (ha.weight 1) z)]
  simp_rw [← sub_mul]
  rw [← tsum_mul_left]
  simp only [weight, pow_one]
  refine hsplit.trans (tsum_congr fun k => ?_)
  push_cast
  rw [pow_succ]
  simp only [pow_one]
  ring

private theorem besselP2_eq (z : ℂ) : besselP2 z = firstP z + z * besselP z := by
  rw [besselP2, powerSum_weight_two pk_bound]
  congr 1
  unfold besselP powerSum
  congr 1
  exact tsum_congr fun k => by
    simp only [weight, pow_one, Nat.cast_add, Nat.cast_one]
    rw [← pk_succ k]
    ring

private theorem secondB_eq (z : ℂ) :
    z * secondB z = z * besselB z + 2 * firstP z - besselP z - 1 := by
  have h (k : ℕ) : weight 1 (fun j => weight 1 bCoeff (j+1)) k - bCoeff k =
      2 * weight 1 pk (k+1) - pk (k+1) := by
    have h1 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have h2 : (k + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k+1)
    simp only [weight, pow_one, Nat.cast_add, Nat.cast_one, bCoeff]
    rw [show (k : ℂ) + 1 + 1 = k + 2 by ring, ← pk_succ k]
    calc
      _ = (bk (k+1) - bk k) * ((k+1 : ℂ) * (k+2) * pk (k+1)) := by ring
      _ = _ := by rw [bk_succ]; field_simp; ring
  have hP := powerSum_shift pk_bound z
  have hP1 := powerSum_shift (pk_bound.weight 1) z
  have hp0 : pk 0 = 1 := by norm_num [pk]
  have hp10 : weight 1 pk 0 = 1 := by norm_num [weight, hp0]
  change besselP z = _ at hP
  change firstP z = _ at hP1
  rw [hp0] at hP
  rw [hp10] at hP1
  have hd : secondB z - besselB z =
      2 * powerSum (fun k => weight 1 pk (k+1)) z - powerSum (fun k => pk (k+1)) z := by
    unfold secondB besselB powerSum
    rw [← tsum_mul_left, ← (powerSum_summable ((bCoeff_bound.weight 1).shift.weight 1) z).tsum_sub
      (powerSum_summable bCoeff_bound z),
      ← ((powerSum_summable (pk_bound.weight 1).shift z).mul_left 2).tsum_sub
        (powerSum_summable pk_bound.shift z)]
    exact tsum_congr fun k => by rw [← sub_mul, h]; ring
  linear_combination z * hd - 2 * hP1 + hP

/-- The normalized real-argument series is complex-valued. -/
def besselSeries (t : ℝ) : ℂ :=
  1 + (t : ℂ) * ((Real.log t : ℂ) * besselP t - besselB t)

/-- First derivative of the normalized series on the positive axis. -/
def besselSeriesSlope (t : ℝ) : ℂ :=
  (Real.log t : ℂ) * firstP t + besselP t - firstB t

theorem hasDerivAt_besselSeries {t : ℝ} (ht : 0 < t) :
    HasDerivAt besselSeries (besselSeriesSlope t) t := by
  have hp := (hasDerivAt_mul_powerSum pk_bound (t : ℂ)).comp_ofReal
  have hb := (hasDerivAt_mul_powerSum bCoeff_bound (t : ℂ)).comp_ofReal
  have hl := (Real.hasDerivAt_log ht.ne').ofReal_comp
  convert ((hl.mul hp).sub hb).const_add (1 : ℂ) using 1
  · ext s
    unfold besselSeries besselP besselB
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  · unfold besselSeriesSlope besselP firstP firstB
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
    ring

theorem hasDerivAt_besselSeriesSlope {t : ℝ} (ht : 0 < t) :
    HasDerivAt besselSeriesSlope (besselSeries t / (t : ℂ)) t := by
  have hp := (hasDerivAt_powerSum pk_bound (t : ℂ)).comp_ofReal
  have hp1 := (hasDerivAt_firstP (t : ℂ)).comp_ofReal
  have hb1 := (hasDerivAt_firstB (t : ℂ)).comp_ofReal
  have hl := (Real.hasDerivAt_log ht.ne').ofReal_comp
  have he : (t : ℂ) * (powerSum (weight 1 (fun k => pk (k+1))) t) =
      firstP t - besselP t := by
    have hh := (hasDerivAt_id (t : ℂ)).mul (hasDerivAt_powerSum pk_bound (t : ℂ))
    have h := hh.unique (hasDerivAt_mul_powerSum pk_bound (t : ℂ))
    simp only [one_mul, id_eq] at h
    change besselP t + (t : ℂ) * _ = firstP t at h
    linear_combination h
  convert ((hl.mul hp1).add hp).sub hb1 using 1
  · rfl
  · have hs := secondB_eq (t : ℂ)
    unfold besselSeries
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
    linear_combination -he + hs

private theorem powerSum_zero {a : ℕ → ℂ} (ha : FactorialBound a) :
    powerSum a 0 = a 0 := by simp [powerSum_shift ha]

theorem tendsto_besselSeries_zero : Tendsto besselSeries (𝓝[>] 0) (𝓝 1) := by
  have h1 : Continuous fun t : ℝ => ((t * Real.log t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp Real.continuous_mul_log
  have h2 : Continuous fun t : ℝ => besselP t :=
    besselP_entire.continuous.comp Complex.continuous_ofReal
  have h3 : Continuous fun t : ℝ => (t : ℂ) * besselB t :=
    Complex.continuous_ofReal.mul (besselB_entire.continuous.comp Complex.continuous_ofReal)
  have h1c : Continuous (fun _ : ℝ => (1 : ℂ)) := continuous_const
  have he : besselSeries = fun t : ℝ =>
      1 + ((t * Real.log t : ℝ) : ℂ) * besselP t - (t : ℂ) * besselB t := by
    ext t
    unfold besselSeries
    push_cast
    ring
  have h : Continuous besselSeries := by
    rw [he]
    exact (h1c.add (h1.mul h2)).sub h3
  have h0 : besselSeries 0 = 1 := by simp [besselSeries]
  rw [← h0]
  exact (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_besselSeriesSlope_sub_log :
    Tendsto (fun t => besselSeriesSlope t - (Real.log t : ℂ)) (𝓝[>] 0)
      (𝓝 ((2 * Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
  have hp0 : besselP 0 = 1 := by rw [besselP, powerSum_zero pk_bound]; norm_num [pk]
  have hp10 : firstP 0 = 1 := by
    rw [firstP, powerSum_zero (pk_bound.weight 1)]
    norm_num [weight, pk]
  have hb10 : firstB 0 = 1 - 2 * (Real.eulerMascheroniConstant : ℂ) := by
    rw [firstB, powerSum_zero (bCoeff_bound.weight 1)]
    norm_num [weight, bCoeff, bk, pk, harmonic_succ]
  have hd := (hasDerivAt_firstP 0).comp_ofReal
  have hs : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ * (firstP t - 1)) (𝓝[>] 0) (𝓝 (besselP 0)) := by
    simpa [slope, hp10, Complex.real_smul, sub_zero] using hd.tendsto_slope_zero_right
  have hl : Tendsto (fun t : ℝ => ((t * Real.log t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous (fun t : ℝ => ((t * Real.log t : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp Real.continuous_mul_log
    simpa only [zero_mul, Complex.ofReal_zero] using
      (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hp := (besselP_entire.continuous.comp Complex.continuous_ofReal).continuousAt
    (x := (0 : ℝ))
  have hb := (hasDerivAt_firstB 0).comp_ofReal.continuousAt
  have hlim := ((hl.mul hs).add (hp.tendsto.mono_left nhdsWithin_le_nhds)).sub
    (hb.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [Function.comp_apply, Complex.ofReal_zero, zero_mul, zero_add, hp0, hb10] at hlim
  have he : 1 - (1 - 2 * (Real.eulerMascheroniConstant : ℂ)) =
      ((2 * Real.eulerMascheroniConstant : ℝ) : ℂ) := by push_cast; ring
  rw [he] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (show 0 < t from ht))
  unfold besselSeriesSlope
  push_cast
  field_simp [ht']
  ring

theorem correctionLog_eq_series (t M : ℝ) :
    correctionLog M t (Real.log t) =
      ((M : ℂ)^2 / (16 * (Real.pi : ℂ)^2)) * (besselSeriesSlope t + besselSeries t) := by
  have hB := powerSum_weight_two bCoeff_bound (t : ℂ)
  change _ = firstB t + (t : ℂ) * secondB t at hB
  rw [correctionLog, besselP2_eq, besselB2_eq, hB, secondB_eq]
  unfold besselSeries besselSeriesSlope
  ring

theorem correction_mixed_deriv {M u v x : ℝ} (hM : 0 < M) (hu : 0 < u) (hv : 0 < v)
    (hx : x < 1) :
    deriv (fun s : ℝ => deriv (fun r : ℝ =>
      ((r*s : ℝ) : ℂ) * bulkDifference M ((2*r*s*(1-x) : ℝ) : ℂ)) u) v =
        correction M u v x := by
  let a : ℝ := M^2 * (1-x) / 2
  let c : ℂ := (M : ℂ)^2 / (16 * (Real.pi : ℂ)^2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hbulk (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
      ((r*s : ℝ) : ℂ) * bulkDifference M ((2*r*s*(1-x) : ℝ) : ℂ) =
        (c / (a : ℂ)) * (besselSeries (a*r*s) - 1) := by
    have harg : (M : ℂ)^2 * ((2*r*s*(1-x) : ℝ) : ℂ) / 4 = ((a*r*s : ℝ) : ℂ) := by
      dsimp [a]; push_cast; ring
    rw [bulkDifference, harg, ← Complex.ofReal_log (by positivity : 0 ≤ a*r*s)]
    unfold besselSeries
    push_cast
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    change _ * (c * _) = _
    field_simp [ha']
    ring
  have hinner (s : ℝ) (hs : 0 < s) : HasDerivAt
      (fun r : ℝ => ((r*s : ℝ) : ℂ) * bulkDifference M ((2*r*s*(1-x) : ℝ) : ℂ))
      ((s : ℂ) * c * besselSeriesSlope (a*u*s)) u := by
    have harg : HasDerivAt (fun r : ℝ => a*r*s) (a*s) u := by
      simpa [id, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id u).const_mul a).mul_const s
    have hh := ((hasDerivAt_besselSeries (show 0 < a*u*s by positivity)).scomp u harg).sub_const 1
    have hd := hh.const_mul (c / (a : ℂ))
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    apply (show HasDerivAt (fun r : ℝ => (c / (a : ℂ)) * (besselSeries (a*r*s) - 1))
      ((s : ℂ) * c * besselSeriesSlope (a*u*s)) u from by
        convert hd using 1
        · rfl
        · rw [Complex.real_smul]
          push_cast
          field_simp [ha']).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hu] with r hr
    exact hbulk r s hr hs
  have harg : HasDerivAt (fun s : ℝ => a*u*s) (a*u) v := hasDerivAt_const_mul _
  have ht : 0 < a*u*v := by positivity
  have hh := (hasDerivAt_besselSeriesSlope ht).scomp v harg
  have hd := (hasDerivAt_id v).ofReal_comp.mul (hh.const_mul c)
  have he : HasDerivAt
      (fun s : ℝ => deriv (fun r : ℝ =>
        ((r*s : ℝ) : ℂ) * bulkDifference M ((2*r*s*(1-x) : ℝ) : ℂ)) u)
      (c * (besselSeriesSlope (a*u*v) + besselSeries (a*u*v))) v := by
    apply (show HasDerivAt (fun s : ℝ => (s : ℂ) * (c * besselSeriesSlope (a*u*s)))
      (c * (besselSeriesSlope (a*u*v) + besselSeries (a*u*v))) v from by
        change HasDerivAt ((fun y : ℝ => (y : ℂ)) *
          fun y => c * besselSeriesSlope (a*u*y)) _ v
        convert hd using 1
        · rfl
        change _ = 1 * (c * besselSeriesSlope (a*u*v)) +
          (v : ℂ) * (c * ((a*u) • (besselSeries (a*u*v) / (↑(a*u*v) : ℂ))))
        rw [Complex.real_smul]
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr ha.ne', Complex.ofReal_ne_zero.mpr hu.ne',
          Complex.ofReal_ne_zero.mpr hv.ne']).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hv] with s hs
    rw [(hinner s hs).deriv, mul_assoc]
  rw [he.deriv, correction, ite_eq_left hx]
  have harg' : M^2*u*v*(1-x)/2 = a*u*v := by dsimp [a]; ring
  rw [harg', correctionLog_eq_series]

end NullConeGravity
