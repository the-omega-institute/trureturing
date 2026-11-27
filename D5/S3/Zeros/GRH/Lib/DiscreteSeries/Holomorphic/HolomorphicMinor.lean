/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicMinor
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicMinor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Holomorphic.HolomorphicMinor. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Holomorphic/HolomorphicMinor.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen.TailBounds
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Holomorphic discrete series: highest coefficient and reproducing property (known
result; see Lib.DiscreteSeries.Holomorphic.HolomorphicExtension).

This file: Highest coefficient is holomorphic; circle mean and reproducing property of holomorphic
functions. -/


open Finset Int MeasureTheory ComplexConjugate Complex Circle
variable {n} [Fintype n] {ε o Φ F} [Fintype Φ] {u : Φ → _} (ho : @IsPosFirstOrder n ε o)
  (hu : ∀ τ, IsKDominant ε o (u τ)) (hF : IsHolOfWeight ε o u F)
attribute [local simp] holMinorsPi holMinors sum_nonneg zpow_add₀ weightMinors_ite_eq_zpow
  ite_eq_iff prod_ne_zero_iff fieldEq diagTorus Measure.real

lemma holMinors_ite_sign {a b} (h : a ≤ b) (g : USign ε) : holMinors ε (if ε · = 1 then a else b)
  g = g.1.1.det ^ b / principalMinor g (ε · = 1) ^ (b - a) := by rw [holMinors,
  weightMinors_ite_eq_zpow, div_eq_div_iff, ← weightMinors_add_ite, ← weightMinors_const,
  ← weightMinors_add_ite] <;> simp <;> grind
  [neg_sum_abs_le_and_le_sum_abs (if ε · = 1 then a else b)]

@[simp] lemma holMinorsPi_one : holMinorsPi ε u 1 = 1 := by simp

include ho hu

omit [Fintype Φ] in
lemma IsPosFirstOrder.isKDominant_shift a τ : IsKDominant 1 o fun i ↦ cond a 1 0 * u τ i + ite (ε
  i = 1) (2 * ∑ j, |u τ j|) 0 := by have := neg_sum_abs_le_and_le_sum_abs (u τ); grind [IsKDominant,
  IsPosFirstOrder, units_eq_one_or (ε _)]

/-- If the order o is injective with the indices of sign +1 first, and every u^τ is K-dominant
for o, then the product of minors m^hol_u (`holMinorsPi`) on U(diag ε)^Φ is holomorphic of weight
u in the sense of `IsHolOfWeight`. -/
lemma isHolOfWeight_holMinorsPi : IsHolOfWeight ε o u (holMinorsPi ε u) := by
  choose f _ using (isHolOfWeight_weightMinors (ε := ε) ho.1 1 <| ho.isKDominant_shift hu ·)
  use f true / f false
  simp_all (maxDischargeDepth := 4) [AnalyticAt.div, diagChar,
    IsBorelMatrix.diag_ne_zero ho.1, -mul_ite]

include hF

-- The mean over the rotations of the base point.
/-- Circle mean: let the order o be injective with sign +1 first, u K-dominant, F holomorphic of
weight u. The mean over |s| = 1 of F(diag(s^o)h)·∏_{τ,i} s^(−o_i u^τ_i) equals
m^hol_u(h)·F(1), for every h in U(diag ε)^Φ. -/
lemma IsHolOfWeight.circle_mean_holMinorsPi h : ∫ θ : UnitAddCircle, F ((fun _ ↦ diagTorus ε
  (θ.toCircle ^ o ·)) * h) * ∏ τ, ∏ i, ↑((θ.toCircle ^ o i) ^ u τ i)⁻¹ = holMinorsPi ε u h *
  F 1 := by simp [← integral_mul_const]; convert! (hF.mul ho.1 (isHolOfWeight_weightMinors ho.1 1
  (ho.isKDominant_shift hu false))).circle_mean_weightMinors ho.1 (by
  simpa using! ho.isKDominant_shift hu true) _ 1 analyticOnNhd_const using
  2 <;> simp (maxDischargeDepth := 4) [-mul_ite, Pi.add_def, ← weightMinors_ite_eq_zpow, funext_iff]

/-- Reproducing formula: let the order o be injective with signs +1 first, each u_τ K-dominant,
F holomorphic of weight u on U(diag ε)^Φ, and F·conj(m) integrable for the compact dual
measure, m = `holMinorsPi` ε u. Then ∫ F·conj(m) = (∫ |m|²)·F(1).

Known result: Holomorphic discrete series: highest coefficient and reproducing property. -/
lemma IsHolOfWeight.integral_mul_conj_holMinorsPi (hi : Integrable fun h ↦ F h * conj (holMinorsPi ε
  u h)) : ∫ h, F h * conj (holMinorsPi ε u h) = (∫ h, ‖holMinorsPi ε u h‖ ^ 2) * F 1 := by
  rw [← integral_complex_ofReal, ← integral_mul_const, integral_eq_of_circle_mean
    (map_mul_left_eq_self _ fun _ ↦ diagTorus ε fun i ↦ ·.toCircle ^ o i) hi]
  simp [← conj_mul', mul_assoc, ← hF.circle_mean_holMinorsPi, *, ← integral_const_mul, -holMinorsPi]
  congr! 2; simp (disch := simp) [← coe_inv_eq_conj, -pow_ite, mul_div_mul_comm]

/-- Let the order o be injective with signs +1 first, each u_τ K-dominant, and F holomorphic of
weight u on U(diag ε)^Φ with F(g⁻¹) = conj F(g). Then F = F(1)·`holMinorsPi` ε u. -/
lemma IsHolOfWeight.eq_holMinorsPi_mul (i : ∀ g, F g⁻¹ = conj (F g)) h : F h =
  holMinorsPi ε u h * F 1 := by simp [mul_comm, -Circle.coe_zpow, ← fun t y ↦ by
  simpa [← i, ← coe_inv_eq_conj, ← coe_zpow, -fieldEq] using congrArg
    conj (hF.apply_mul_diagTorus y⁻¹ t), ← hF.circle_mean_holMinorsPi, *, -holMinorsPi]
