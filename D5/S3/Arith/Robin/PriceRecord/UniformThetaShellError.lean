/- GID: D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/UniformThetaShellError
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Exact real-shell theta-error supremum is finite and uniformly sublinear. -/
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! The supremum ranges over every real point of the shell, including the
jumps of theta. The sublinearity estimate uses the coarse prime number theorem. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError
open Real Filter
open scoped Topology

def errorValues (X : ℝ) : Set ℝ :=
  (fun y : ℝ => |Chebyshev.theta y - y|) '' Set.Icc (X / 2) (2 * X)
def shellError (X : ℝ) : ℝ := sSup (errorValues X)

theorem errorValues_nonempty {X : ℝ} (hX : 0 ≤ X) : (errorValues X).Nonempty :=
  ⟨|Chebyshev.theta X - X|, ⟨X, ⟨by linarith, by linarith⟩, rfl⟩⟩

theorem errorValues_bddAbove {X : ℝ} (hX : 0 ≤ X) : BddAbove (errorValues X) := by
  refine ⟨Chebyshev.theta (2 * X) + 2 * X, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hθ0 := Chebyshev.theta_nonneg y
  have hθ := Chebyshev.theta_mono hy.2
  exact abs_le.mpr ⟨by linarith [Chebyshev.theta_nonneg (2 * X), hy.2], by linarith⟩

theorem pointwise_le_shellError {X y : ℝ} (hX : 0 ≤ X)
    (hy : y ∈ Set.Icc (X / 2) (2 * X)) : |Chebyshev.theta y - y| ≤ shellError X :=
  le_csSup (errorValues_bddAbove hX) ⟨y, hy, rfl⟩

theorem shellError_nonneg {X : ℝ} (hX : 0 ≤ X) : 0 ≤ shellError X :=
  (abs_nonneg _).trans (pointwise_le_shellError (y := X) hX ⟨by linarith, by linarith⟩)

theorem shellError_le {X A : ℝ} (hX : 0 ≤ X)
    (hA : ∀ y : ℝ, y ∈ Set.Icc (X / 2) (2 * X) → |Chebyshev.theta y - y| ≤ A) :
    shellError X ≤ A := by
  apply csSup_le (errorValues_nonempty hX)
  rintro z ⟨y, hy, rfl⟩
  exact hA y hy

/-- One all-real threshold dominates the whole shell at once. -/
theorem shellError_eventually_le_mul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, 0 < X ∧ shellError X ≤ ε * X := by
  have hθ := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2
  have he := (Metric.tendsto_nhds.mp hθ) (ε / 2) (by positivity)
  obtain ⟨Y, hY⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop (max (2 * Y) 1)] with X hX
  have hX0 : 0 < X := by linarith [le_max_right (2 * Y) (1 : ℝ)]
  refine ⟨hX0, shellError_le hX0.le ?_⟩
  intro y hy
  have hy0 : 0 < y := by linarith [hy.1]
  have hyY : Y ≤ y := by linarith [hy.1, le_max_left (2 * Y) (1 : ℝ)]
  have hh : |Chebyshev.theta y / y - 1| < ε / 2 := by
    simpa only [Real.dist_eq] using hY y hyY
  have hid : Chebyshev.theta y / y - 1 = (Chebyshev.theta y - y) / y := by
    field_simp [hy0.ne']
  rw [hid, abs_div, abs_of_pos hy0] at hh
  have hm := (div_lt_iff₀ hy0).mp hh
  have hupper := mul_le_mul_of_nonneg_left hy.2 (show 0 ≤ ε / 2 by positivity)
  linarith

theorem shellError_ratio_tendsto_zero :
    Tendsto (fun X : ℝ => shellError X / X) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [shellError_eventually_le_mul (half_pos hε)] with X hX
  have hn := div_nonneg (shellError_nonneg hX.1.le) hX.1.le
  have hb : shellError X / X ≤ ε / 2 := (div_le_iff₀ hX.1).mpr (by linarith [hX.2])
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  linarith

/-- Uniform comparison for any real exponent, including negative exponents. -/
theorem shell_rpow_bound {X y : ℝ} (hX : 0 < X)
    (hy : y ∈ Set.Icc (X / 2) (2 * X)) (a : ℝ) :
    y ^ a ≤ (2 : ℝ) ^ |a| * X ^ a := by
  have hy0 : 0 < y := by linarith [hy.1]
  have ht0 : 0 < y / X := div_pos hy0 hX
  have hlo : (1 / 2 : ℝ) ≤ y / X := (le_div_iff₀ hX).mpr (by linarith [hy.1])
  have hhi : y / X ≤ 2 := (div_le_iff₀ hX).mpr (by linarith [hy.2])
  have habs : |log (y / X)| ≤ log 2 := by
    have hl := log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlo
    have hh := log_le_log ht0 hhi
    rw [log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      log_one, zero_sub] at hl
    exact abs_le.mpr ⟨by linarith, hh⟩
  have hexp : log (y / X) * a ≤ log 2 * |a| := by
    calc
      _ ≤ |log (y / X) * a| := le_abs_self _
      _ = |log (y / X)| * |a| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right habs (abs_nonneg a)
  have hr : (y / X) ^ a ≤ (2 : ℝ) ^ |a| := by
    rw [rpow_def_of_pos ht0, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact exp_le_exp.mpr hexp
  rw [div_rpow hy0.le hX.le] at hr
  exact (div_le_iff₀ (rpow_pos_of_pos hX a)).mp hr

/-- A global error law gives a uniform error envelope with an explicit shell
factor. This is conditional on the stated global law, never on a pointwise
estimate at the selected original record endpoint. -/
theorem shellError_global_power {σ B K Y : ℝ} (hK : 0 ≤ K)
    (hglobal : ∀ y : ℝ, Y ≤ y → 0 < y → 0 < log y →
      |Chebyshev.theta y - y| ≤ K * y ^ σ * (log y) ^ B) :
    ∀ X : ℝ, max 4 (2 * Y) < X →
      shellError X ≤ (K * (2 : ℝ) ^ |σ| * (2 : ℝ) ^ |B|) *
        X ^ σ * (log X) ^ B := by
  intro X hX
  have hX4 : 4 < X := (le_max_left _ _).trans_lt hX
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < log X := log_pos (by linarith)
  have hlog4 : 2 * log (2 : ℝ) ≤ log X := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < 4) hX4.le
    have he : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
      rfl
    linarith
  apply shellError_le hX0.le
  intro y hy
  have hy0 : 0 < y := by linarith [hy.1]
  have hy1 : 1 < y := by linarith [hy.1]
  have hly : log y ∈ Set.Icc (log X / 2) (2 * log X) := by
    have hlo := log_le_log (show 0 < X / 2 by positivity) hy.1
    have hhi := log_le_log hy0 hy.2
    rw [log_div hX0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlo
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at hhi
    exact ⟨by linarith, by linarith [log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]⟩
  have hp := shell_rpow_bound hX0 hy σ
  have hl := shell_rpow_bound hL0 hly B
  have hg := hglobal y (by linarith [hy.1, le_max_right (4 : ℝ) (2 * Y)]) hy0 (log_pos hy1)
  apply hg.trans
  have hm := mul_le_mul hp hl (rpow_nonneg (log_pos hy1).le B)
    (by positivity : 0 ≤ (2 : ℝ) ^ |σ| * X ^ σ)
  have hh := mul_le_mul_of_nonneg_left hm hK
  nlinarith
end D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError
