/- GID: D5/S3/Weil/ZetaBridge/RiemannVonMangoldtCountGrowth
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/RiemannVonMangoldtCountGrowth
   mirror-E: none(waiver:finite-growth-bridge-only)
   anchors: []
   digest: The Riemann-von Mangoldt main term forces the dyadic zero count of every ZeroConfig to tend to infinity. -/

import D5.S3.Weil.ZetaCore.Hypotheses
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Riemann-von Mangoldt forces unbounded dyadic zero count

This node extracts the small growth fragment needed by the canonical
`ZeroData` nonvacuity route.  It is adapted from the `Growth` section of the
machine-checked Zeta23 assembly, while reusing the repository's existing
`ZeroConfig`, `RiemannVonMangoldt`, `l`, `ell1`, and dyadic count `ZeroConfig.N`.

The theorem is generic in an abstract zero configuration.  It assumes the
published Riemann-von Mangoldt estimate explicitly and proves only that
`N(T,2T)` tends to infinity.  It neither instantiates the estimate for zeta nor
constructs `ZeroData`.
-/

/- Library-first audit trail (2026-09-03):
   * `D5/S3/Weil/ZetaCore/Hypotheses` owns `RiemannVonMangoldt` and its exact
     main-term field.
   * `D5/S3/Weil/ZetaCore/Defs` owns `l`, `ell1`, `ZeroConfig`, and
     `ZeroConfig.N` through that import.
   * Pinned Mathlib owns the logarithmic limit, positive-real pi bounds, and
     filter arithmetic used below.
   * The proof follows the already machine-checked Zeta23 growth argument:
     `N(T,2T) >= T l(T)/(4 pi)` eventually, hence `N(T,2T) -> infinity`.
   * Repository searches found no public owner of this implication on the
     current `dev` baseline. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter

namespace D5.S3.Weil.ZetaBridge.RiemannVonMangoldtCountGrowth

open Zeta23
open Filter Asymptotics Topology Real

private def c0 : ℝ := 2 * Real.log 2 - 1

private lemma c0_pos : 0 < c0 := by
  have h := Real.log_two_gt_d9
  unfold c0
  linarith

private lemma ell1_eq_l_add_c0 (T : ℝ) : ell1 T = l T + c0 := by
  simp only [ell1, c0]
  ring

/-- The logarithmic scale `l(T) = log(T / (2 pi))` tends to infinity. -/
theorem tendsto_l_atTop : Tendsto l atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_id.atTop_div_const (by positivity))

private lemma eventually_l_pos : ∀ᶠ T in atTop, 0 < l T :=
  tendsto_l_atTop.eventually_gt_atTop 0

private lemma log_eq_l_add {T : ℝ} (hT : 0 < T) :
    Real.log T = l T + Real.log (2 * Real.pi) := by
  rw [l, Real.log_div hT.ne' (by positivity)]
  ring

private lemma eventually_log_le_two_l :
    ∀ᶠ T in atTop, Real.log T ≤ 2 * l T := by
  filter_upwards
      [tendsto_l_atTop.eventually_ge_atTop (Real.log (2 * Real.pi)),
        eventually_gt_atTop 0]
      with T h1 h2
  rw [log_eq_l_add h2]
  linarith

private lemma eventually_log_nonneg :
    ∀ᶠ T in atTop, 0 ≤ Real.log T :=
  Real.tendsto_log_atTop.eventually_ge_atTop 0

/-- The main scale `T * l(T)` tends to infinity. -/
theorem tendsto_T_mul_l_atTop :
    Tendsto (fun T : ℝ => T * l T) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ tendsto_l_atTop

/-- The Riemann-von Mangoldt main term gives an eventual explicit lower bound
for the dyadic zero count. -/
theorem dyadic_zero_count_eventually_ge
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    ∀ᶠ T in atTop,
      T * l T / (4 * Real.pi) ≤ (Z.N T (2 * T) : ℝ) := by
  obtain ⟨C, T0, hmain⟩ := hR.main
  filter_upwards
      [eventually_ge_atTop T0,
        eventually_log_le_two_l,
        eventually_log_nonneg,
        eventually_l_pos,
        eventually_ge_atTop (16 * Real.pi * |C|),
        eventually_ge_atTop 0]
      with T hT hlog hlog0 hl hTC hT0
  have hLower := (abs_le.mp (hmain T hT)).1
  have hEll : l T ≤ ell1 T := by
    rw [ell1_eq_l_add_c0]
    exact le_add_of_nonneg_right c0_pos.le
  have hError : -(C * Real.log T) ≥ -(|C| * (2 * l T)) := by
    have hCLog : C * Real.log T ≤ |C| * Real.log T :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
    nlinarith [abs_nonneg C]
  have hMain :
      T / (2 * Real.pi) * l T ≤
        T / (2 * Real.pi) * ell1 T :=
    mul_le_mul_of_nonneg_left hEll (by positivity)
  have hAbsorb :
      2 * |C| * l T ≤ T * l T / (4 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg C, Real.pi_pos]
  have hDouble :
      T / (2 * Real.pi) * l T =
        2 * (T * l T / (4 * Real.pi)) := by
    ring
  linarith

/-- Under Riemann-von Mangoldt, the dyadic zero count tends to infinity. -/
theorem dyadic_zero_count_tendsto_atTop
    (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    Tendsto (fun T : ℝ => (Z.N T (2 * T) : ℝ)) atTop atTop :=
  tendsto_atTop_mono' _ (dyadic_zero_count_eventually_ge Z hR)
    (tendsto_T_mul_l_atTop.atTop_div_const (by positivity))

#print axioms tendsto_l_atTop
#print axioms tendsto_T_mul_l_atTop
#print axioms dyadic_zero_count_eventually_ge
#print axioms dyadic_zero_count_tendsto_atTop

end D5.S3.Weil.ZetaBridge.RiemannVonMangoldtCountGrowth
