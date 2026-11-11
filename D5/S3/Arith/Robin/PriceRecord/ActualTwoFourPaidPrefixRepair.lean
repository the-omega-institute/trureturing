/- GID: D5/S3/Arith/Robin/PriceRecord/ActualTwoFourPaidPrefixRepair
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualTwoFourPaidPrefixRepair
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Actual two/four-layer seeded prefix repair at inverse-log-squared reference cost. -/
import D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
import D5.S3.Arith.Robin.PriceRecord.PositiveCurvatureFloorMesh
import D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget
import D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerQuantitativeBudgetRepair
import Mathlib.Tactic

/-! SOURCE ONLY. UNCOMPILED_UNACCEPTED / RegUNVALIDATED.
The producers are imported, never copied. Consumed generalizations are
hash-bound UNAPPLIED patches. This file does not assert an original-record,
arbitrary-original-price, energy, RH or official-acceptance conclusion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualTwoFourPaidPrefixRepair
open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
open D5.S3.Arith.Robin.PriceRecord.PositiveCurvatureFloorMesh
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
open D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity (block first_margin)
open D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve
open D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret
open D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget
open D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerQuantitativeBudgetRepair

private def offset (j : ℕ) (X : ℝ) : ℝ :=
  (j : ℝ) * log (cutoff j (referencePrice X)) - log X
private def curvature (X : ℝ) : ℝ := offset 4 X - 2 * offset 2 X
private def uniformW (X : ℝ) : ℝ :=
  shellError X + 3 * sqrt X + 2000 * log X ^ 3 + 1

private theorem price_positive {X : ℝ} (hX : 1 < X) : 0 < referencePrice X :=
  one_div_pos.mpr (mul_pos (by linarith) (log_pos hX))

private theorem log_two_le_one : log (2 : ℝ) ≤ 1 := by
  have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hh
  exact hh

private theorem log_two_nonneg : 0 ≤ log (2 : ℝ) := by
  exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)

private theorem log_two_sq_le_one : log (2 : ℝ) ^ 2 ≤ 1 := by
  have hh : log (2 : ℝ) * log (2 : ℝ) ≤ (1 : ℝ) * 1 :=
    mul_self_le_mul_self log_two_nonneg log_two_le_one
  simpa [pow_two] using hh

private theorem three_curvature_div_four_pos {c : ℝ} (hc : 0 < c) :
    0 < 3 * c / 4 := by
  positivity

private theorem le_div_log_sq {a b L : ℝ} (hL : 0 < L)
    (h : L ^ 2 * a ≤ b) : a ≤ b / L ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
  simpa [mul_comm] using h

private theorem weighted_shell_error (n : ℕ) :
    Tendsto (fun X : ℝ => shellError X * log X ^ n / X) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K : ℝ := 2 ^ (n + 2)
  have hK : 0 < K := by dsimp [K]; positivity
  have he := Metric.tendsto_nhds.mp
    (theta_error_log_power n).tendsto_div_nhds_zero (ε / K) (div_pos hε hK)
  obtain ⟨Y, hY⟩ := eventually_atTop.mp he
  filter_upwards [eventually_gt_atTop (max 4 (2 * Y))] with X hX
  have hX4 : 4 < X := (le_max_left _ _).trans_lt hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < log X := log_pos (by linarith)
  have henv : shellError X ≤ (ε / 2) * X / log X ^ n := by
    apply shellError_le hX0.le
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hy1 : 1 < y := by linarith [hy.1]
    have hly : 0 < log y := log_pos hy1
    have hyY : Y ≤ y := by linarith [hy.1, le_max_right (4 : ℝ) (2 * Y)]
    have hp : |Chebyshev.theta y - y| * log y ^ n / y < ε / K := by
      have hh := hY y hyY
      rw [Real.dist_eq, sub_zero, abs_div,
        abs_of_pos (div_pos hy0 (pow_pos hly n))] at hh
      convert hh using 1
      field_simp [hy0.ne', (pow_pos hly n).ne']
    have hlxy : log X ≤ 2 * log y := by
      have hh := (log_shell hX4).2.1.trans
        (log_le_log (by positivity : 0 < X / 2) hy.1)
      linarith
    have hpow : log X ^ n ≤ 2 ^ n * log y ^ n := by
      simpa only [mul_pow] using pow_le_pow_left₀ hL.le hlxy n
    have hpoint : |Chebyshev.theta y - y| * log X ^ n / X ≤ ε / 2 := by
      calc
        _ ≤ |Chebyshev.theta y - y| * (2 ^ n * log y ^ n) / X :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) hX0.le
        _ = (|Chebyshev.theta y - y| * log y ^ n / y) * 2 ^ n * (y / X) := by
          field_simp [hy0.ne', hX0.ne']
        _ ≤ (ε / K) * 2 ^ n * 2 := by
          calc
            _ ≤ (ε / K) * 2 ^ n * (y / X) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hp.le (by positivity)) (by positivity)
            _ ≤ (ε / K) * 2 ^ n * 2 := by
              apply mul_le_mul_of_nonneg_left ((div_le_iff₀ hX0).mpr hy.2)
              positivity
        _ = ε / 2 := by
          dsimp [K]
          rw [pow_add]
          norm_num
          field_simp [(pow_pos (by norm_num : (0 : ℝ) < 2) n).ne']
          ring
    apply (le_div_iff₀ (pow_pos hL n)).mpr
    exact (div_le_iff₀ hX0).mp hpoint
  have h0 : 0 ≤ shellError X * log X ^ n / X := by
    exact div_nonneg (mul_nonneg (shellError_nonneg hX0.le) (pow_nonneg hL.le n)) hX0.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  have hh := (le_div_iff₀ (pow_pos hL n)).mp henv
  have hu : shellError X * log X ^ n / X ≤ ε / 2 := (div_le_iff₀ hX0).mpr hh
  linarith

private theorem uniformW_small (n : ℕ) :
    Tendsto (fun X : ℝ => uniformW X * log X ^ n / X) atTop (𝓝 0) := by
  have hs : Tendsto (fun X : ℝ => log X ^ n / sqrt X) atTop (𝓝 0) := by
    simpa only [rpow_natCast, ← sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop n (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hp (k : ℕ) : Tendsto (fun X : ℝ => log X ^ k / X) atTop (𝓝 0) := by
    simpa only [rpow_natCast, rpow_one] using
      (isLittleO_log_rpow_rpow_atTop k (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hh := (((weighted_shell_error n).add (hs.const_mul 3)).add
    ((hp (n + 3)).const_mul 2000)).add (hp n)
  simp only [mul_zero, zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  dsimp [uniformW]
  have hs0 := (sqrt_pos.mpr hX).ne'
  have hsq := sq_sqrt hX.le
  field_simp [hX.ne', hs0]
  rw [pow_add]
  ring_nf
  have hsq' := congrArg (fun t : ℝ => log X ^ n * t * 3) hsq
  linarith only [hsq']

private theorem eventual_scalar_estimates : ∀ᶠ X : ℝ in atTop,
    10 ≤ log X ∧
    log 2 / 2 ≤ offset 2 X ∧ offset 2 X ≤ 2 * log 2 ∧
    0 < curvature X ∧ curvature X < offset 2 X ∧
    log 2 ^ 2 / 2 ≤ log X ^ 2 * curvature X ∧
    log X ^ 2 * curvature X ≤ 2 * log 2 ^ 2 ∧
    4000 / log X ^ 2 + 2000 * (uniformW X * log X ^ 4 / X) ≤ log 2 ^ 2 / 8 ∧
    24000 * (uniformW X * log X ^ 5 / X) ≤ 1 ∧ 32000 ≤ log X := by
  have ha := fixed_layer_root_offset_tendsto (by norm_num : 2 ≤ 2)
  have hc := actual_two_four_curvature_tendsto
  have ha0 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hc0 := sq_pos_of_pos ha0
  have hz : Tendsto curvature atTop (𝓝 0) := by
    have hh := hc.div_atTop ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_log_atTop)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    dsimp [curvature, offset]
    field_simp [(log_pos hX).ne']
  have herr : Tendsto (fun X : ℝ =>
      4000 / log X ^ 2 + 2000 * (uniformW X * log X ^ 4 / X)) atTop (𝓝 0) := by
    have hfirst : Tendsto (fun X : ℝ => 4000 / log X ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_log_atTop)
    simpa only [mul_zero, zero_add] using hfirst.add ((uniformW_small 4).const_mul 2000)
  filter_upwards [tendsto_log_atTop.eventually_ge_atTop 32000,
    ha.eventually (eventually_gt_nhds (by linarith : log 2 / 2 < log (2 : ℝ))),
    ha.eventually (eventually_lt_nhds (by linarith : log (2 : ℝ) < 2 * log 2)),
    hc.eventually (eventually_gt_nhds (by linarith : log 2 ^ 2 / 2 < log (2 : ℝ) ^ 2)),
    hc.eventually (eventually_lt_nhds (by linarith : log (2 : ℝ) ^ 2 < 2 * log 2 ^ 2)),
    hz.eventually (eventually_lt_nhds (half_pos ha0)),
    herr.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < log 2 ^ 2 / 8)),
    ((uniformW_small 5).const_mul 24000).eventually
      (eventually_lt_nhds (by norm_num : (24000 : ℝ) * 0 < 1))]
      with X hL haL haU hcL hcU hcA he hC
  have hLp : 0 < log X := by linarith
  have hcur : 0 < curvature X := by
    change log 2 ^ 2 / 2 < log X ^ 2 * curvature X at hcL
    exact pos_of_mul_pos_right (lt_trans (by positivity) hcL) (sq_nonneg _)
  exact ⟨by linarith, haL.le, haU.le, hcur, hcA.trans_le haL.le,
    hcL.le, hcU.le, he.le, hC.le, hL⟩

private theorem finite_seed_coefficients {L α δ δ₀ : ℝ}
    (hL : 10 ≤ L) (hαL : log 2 / 2 ≤ α) (hαU : α ≤ 2 * log 2)
    (hδ : 0 < δ) (hδα : δ < α)
    (hcL : log 2 ^ 2 / 2 ≤ L ^ 2 * δ)
    (hδ₀ : 0 ≤ δ₀) (hδ₀U : δ₀ ≤ L + log 2)
    (S : Finset ℕ) (hcard : S.card = ⌈100 * L⌉₊)
    (hS : ∀ p ∈ S, L - log 2 ≤ log p ∧ log p ≤ L + log 2) :
    ∃ A B : ℕ, ((⌈100 * L⌉₊ + A + B : ℕ) : ℝ) ≤ 1000 * L ^ 2 ∧
      δ ≤ (δ₀ + ∑ p ∈ S, log p) - A * α - B * (2 * α + δ) ∧
      (δ₀ + ∑ p ∈ S, log p) - A * α - B * (2 * α + δ) < 2 * δ := by
  have ha0 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have haU : log (2 : ℝ) ≤ 1 := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have haL : (1 / 2 : ℝ) < log 2 := by
    have hh := lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
    norm_num at hh
    linarith
  have hα : 0 < α := by linarith
  have hsL : 100 * L ≤ (S.card : ℝ) := by rw [hcard]; exact Nat.le_ceil _
  have hsU : (S.card : ℝ) < 100 * L + 1 := by
    rw [hcard]
    exact Nat.ceil_lt_add_one (by linarith : 0 ≤ 100 * L)
  have hsumL : (S.card : ℝ) * (L - log 2) ≤ ∑ p ∈ S, log p := by
    calc
      _ = ∑ _p ∈ S, (L - log 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ S, log p := sum_le_sum (fun p hp => (hS p hp).1)
  have hsumU : (∑ p ∈ S, log p) ≤ (S.card : ℝ) * (L + log 2) := by
    calc
      (∑ p ∈ S, log p) ≤ ∑ _p ∈ S, (L + log 2) :=
        sum_le_sum (fun p hp => (hS p hp).2)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  let Δ := δ₀ + ∑ p ∈ S, log p
  have hΔL : 90 * L ^ 2 ≤ Δ := by
    have hm := mul_le_mul_of_nonneg_right hsL (by linarith : 0 ≤ L - log 2)
    dsimp [Δ]
    nlinarith only [hm, hsumL, hδ₀, hL, haU]
  have hΔU : Δ ≤ 200 * L ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hsU.le (by linarith : 0 ≤ L + log 2)
    dsimp [Δ]
    nlinarith only [hm, hsumU, hδ₀U, hL, haU, ha0]
  have hαsq : α ^ 2 ≤ 4 * log 2 ^ 2 := by nlinarith only [hαU, hα.le, ha0.le]
  have hratio : 4 * α ^ 2 / δ ≤ 32 * L ^ 2 := by
    apply (div_le_iff₀ hδ).mpr
    nlinarith only [hαsq, hcL]
  have hmesh : 4 * α ^ 2 / δ + 2 * α ≤ Δ := by
    nlinarith only [hratio, hΔL, hαU, haU, hL]
  obtain ⟨A, B, _, _, _, hAB, hresL, hresU⟩ :=
    positive_curvature_floor_mesh hα hδ hδα hmesh
  have hABU : (A + B : ℝ) ≤ 800 * L ^ 2 := by
    apply hAB.trans
    apply (div_le_iff₀ hα).mpr
    have hαquarter : (1 / 4 : ℝ) ≤ α := by linarith
    nlinarith only [hΔU, hαquarter, sq_nonneg L]
  refine ⟨A, B, ?_, hresL, hresU⟩
  rw [← hcard]
  push_cast
  nlinarith only [hsU.le, hABU, hL]

private theorem eventual_roster_geometry : ∀ᶠ X : ℝ in atTop,
    4 < cutoff 2 (referencePrice X) ∧ 4 < cutoff 4 (referencePrice X) ∧
    cutoff 2 (referencePrice X) * (1 + 1 / log X ^ 6) < X / 2 ∧
    cutoff 4 (referencePrice X) * (1 + 1 / log X ^ 6) < cutoff 2 (referencePrice X) ∧
    ∀ j : ℕ, j = 2 ∨ j = 4 → ∀ p : ℕ, p.Prime →
      cutoff j (referencePrice X) < (p : ℝ) →
      (p : ℝ) ≤ cutoff j (referencePrice X) * (1 + 1 / log X ^ 6) →
      optimalLayerCount (referencePrice X) p = j - 1 ∧
        (p : ℝ) < X / 2 ∧ log p ≤ log X := by
  have hκ : Tendsto (fun X : ℝ => 1 / log X ^ 6) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : 6 ≠ 0)).comp tendsto_log_atTop)
  filter_upwards [eventually_gt_atTop (4 : ℝ), tendsto_log_atTop.eventually_ge_atTop 10,
    (root_atTop (by norm_num : 2 ≤ 2)).eventually_gt_atTop 4,
    (root_atTop (by norm_num : 2 ≤ 4)).eventually_gt_atTop 4,
    (root_log_ratio (by norm_num : 2 ≤ 2)).eventually
      (eventually_gt_nhds (by norm_num : (9 / 20 : ℝ) < (2 : ℝ)⁻¹)),
    (root_log_ratio (by norm_num : 2 ≤ 2)).eventually
      (eventually_lt_nhds (by norm_num : (2 : ℝ)⁻¹ < 11 / 20)),
    (root_log_ratio (by norm_num : 2 ≤ 4)).eventually
      (eventually_lt_nhds (by norm_num : (4 : ℝ)⁻¹ < 3 / 10)),
    hκ.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16))]
      with X hX hL hρ2 hρ4 h2L h2U h4U hκX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < log X := log_pos (by linarith)
  have h2L' := (lt_div_iff₀ hlog).mp h2L
  have h2U' := (div_lt_iff₀ hlog).mp h2U
  have h4U' := (div_lt_iff₀ hlog).mp h4U
  have hκ0 : 0 ≤ 1 / log X ^ 6 := by positivity
  have hlogκ : log (1 + 1 / log X ^ 6) ≤ 1 := by
    have hh := log_le_sub_one_of_pos (show 0 < 1 + 1 / log X ^ 6 by positivity)
    linarith
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hupper : cutoff 2 (referencePrice X) * (1 + 1 / log X ^ 6) < X / 2 := by
    apply (log_lt_log_iff (by positivity : 0 < cutoff 2 (referencePrice X) *
      (1 + 1 / log X ^ 6)) (by positivity : 0 < X / 2)).mp
    rw [log_mul (by linarith : cutoff 2 (referencePrice X) ≠ 0) (by positivity),
      log_div hX0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    linarith only [h2U', hL, hlogκ, hlog2]
  have hdis : cutoff 4 (referencePrice X) * (1 + 1 / log X ^ 6) <
      cutoff 2 (referencePrice X) := by
    apply (log_lt_log_iff (by positivity : 0 < cutoff 4 (referencePrice X) *
      (1 + 1 / log X ^ 6)) (by linarith : 0 < cutoff 2 (referencePrice X))).mp
    rw [log_mul (by linarith : cutoff 4 (referencePrice X) ≠ 0) (by positivity)]
    linarith only [h4U', h2L', hL, hlogκ]
  refine ⟨hρ2, hρ4, hupper, hdis, ?_⟩
  intro j hj p hp hpl hpu
  have hj2 : 2 ≤ j := by rcases hj with rfl | rfl <;> norm_num
  have hj4 : j ≤ 4 := by rcases hj with rfl | rfl <;> norm_num
  have hρ : 4 < cutoff j (referencePrice X) := by rcases hj with rfl | rfl <;> assumption
  have hp4 : (4 : ℝ) < p := hρ.trans hpl
  have hLambda := price_positive (by linarith : 1 < X)
  have hroot := (cutoff_spec hj2 hLambda).2.2.1 (by linarith : 2 < cutoff j (referencePrice X))
  obtain ⟨_, hreg⟩ := insertion_regret hj2 hp (by linarith) hLambda hroot hκ0 hpl.le hpu
  have hcur : goldenLayerMarginal p j < referencePrice X := by
    rw [← beta_nat hp (by omega : 1 ≤ j), ← hroot]
    have hcut2 : (2 : ℝ) ≤ cutoff j (referencePrice X) := by linarith [hρ]
    exact beta_strictAntiOn hj2 hcut2
      (by change (2 : ℝ) ≤ p; exact_mod_cast hp.two_le) hpl
  have hbetaL : referencePrice X / 2 ≤ beta j (p : ℝ) := by
    have hjr : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
    rw [← beta_nat hp (by omega : 1 ≤ j)] at hreg
    have hm := mul_le_mul_of_nonneg_right hjr hκ0
    have hh := mul_le_mul_of_nonneg_right hm hLambda.le
    have hκLambda := mul_lt_mul_of_pos_right hκX hLambda
    have hbound : referencePrice X - beta j (p : ℝ) ≤
        8 * (1 / log X ^ 6) * referencePrice X := by
      exact hreg.trans (by nlinarith only [hh])
    have hsmall : 8 * (1 / log X ^ 6) * referencePrice X < referencePrice X / 2 := by
      nlinarith only [hκLambda]
    nlinarith only [hbound, hsmall]
  have hprev := adjacent_layer_strict hj2 (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ p)
  have hprev' : referencePrice X < goldenLayerMarginal p (j - 1) := by
    rw [← beta_nat hp (by omega : 1 ≤ j - 1)]
    have hprod := mul_lt_mul_of_pos_right (show (2 : ℝ) < p by linarith only [hp4])
      (beta_pos (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ p) (by omega : 1 ≤ j))
    nlinarith only [hprev, hbetaL, hprod]
  have hoptL := (strict_layer_iff hLambda hp (by omega : 1 ≤ j - 1)).mpr hprev'
  have hoptU : ¬j ≤ (strictInteger (referencePrice X)).factorization p := by
    intro hn
    exact (hcur.not_gt ((strict_layer_iff hLambda hp (by omega : 1 ≤ j)).mp hn))
  rw [strictInteger_counts hLambda] at hoptL hoptU
  have hpX : (p : ℝ) < X / 2 := by
    rcases hj with rfl | rfl
    · exact hpu.trans_lt hupper
    · have hρ2U : cutoff 2 (referencePrice X) ≤
          cutoff 2 (referencePrice X) * (1 + 1 / log X ^ 6) := by nlinarith
      exact hpu.trans_lt (hdis.trans_le (hρ2U.trans hupper.le))
  exact ⟨by omega, hpX, log_le_log (by exact_mod_cast hp.pos) (by linarith)⟩

private theorem fresh_rosters : ∃ T : ℝ, 1 < T ∧ ∀ X : ℝ, T ≤ X →
    ∀ A B : ℕ, (A + B : ℝ) ≤ 1000 * log X ^ 2 →
    ∃ P₂ P₄ : Finset ℕ, P₂.card = 2 * A ∧ P₄.card = 4 * B ∧ Disjoint P₂ P₄ ∧
      (∀ p ∈ P₂, p.Prime ∧ cutoff 2 (referencePrice X) < (p : ℝ) ∧
        (p : ℝ) ≤ cutoff 2 (referencePrice X) * (1 + 1 / log X ^ 6) ∧
        optimalLayerCount (referencePrice X) p = 1 ∧ (p : ℝ) < X / 2 ∧ log p ≤ log X) ∧
      (∀ p ∈ P₄, p.Prime ∧ cutoff 4 (referencePrice X) < (p : ℝ) ∧
        (p : ℝ) ≤ cutoff 4 (referencePrice X) * (1 + 1 / log X ^ 6) ∧
        optimalLayerCount (referencePrice X) p = 3 ∧ (p : ℝ) < X / 2 ∧ log p ≤ log X) := by
  obtain ⟨T₂, _, hT₂⟩ := fixed_layer_shrinking_prime_roster_power
    (by norm_num : 2 ≤ 2) 6 2 (by norm_num) 4000 (by norm_num)
  obtain ⟨T₄, _, hT₄⟩ := fixed_layer_shrinking_prime_roster_power
    (by norm_num : 2 ≤ 4) 6 2 (by norm_num) 4000 (by norm_num)
  obtain ⟨Tg, hTg⟩ := eventually_atTop.mp eventual_roster_geometry
  refine ⟨max 2 (max T₂ (max T₄ Tg)), by exact lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro X hXT A B hAB
  have h2 := (le_max_left T₂ (max T₄ Tg)).trans ((le_max_right 2 _).trans hXT)
  have h4 := (le_max_left T₄ Tg).trans ((le_max_right T₂ _).trans ((le_max_right 2 _).trans hXT))
  have hg := hTg X ((le_max_right T₄ Tg).trans
    ((le_max_right T₂ _).trans ((le_max_right 2 _).trans hXT)))
  obtain ⟨S₂, hc₂, hS₂, _⟩ := hT₂ X h2
  obtain ⟨S₄, hc₄, hS₄, _⟩ := hT₄ X h4
  have hcard₂ : 2 * A ≤ S₂.card := by
    have hh : (2 * A : ℝ) ≤ (S₂.card : ℝ) := by
      push_cast
      nlinarith only [hAB, hc₂, (Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
    exact_mod_cast hh
  have hcard₄ : 4 * B ≤ S₄.card := by
    have hh : (4 * B : ℝ) ≤ (S₄.card : ℝ) := by
      push_cast
      nlinarith only [hAB, hc₄, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
    exact_mod_cast hh
  obtain ⟨P₂, hP₂, hcard₂⟩ := exists_subset_card_eq hcard₂
  obtain ⟨P₄, hP₄, hcard₄⟩ := exists_subset_card_eq hcard₄
  refine ⟨P₂, P₄, hcard₂, hcard₄, ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro p hp₂ hp₄
    have hl := (hS₂ p (hP₂ hp₂)).2.1
    have hu := (hS₄ p (hP₄ hp₄)).2.2
    linarith only [hl, hu, hg.2.2.2.1]
  · intro p hp
    obtain ⟨hprime, hl, hu⟩ := hS₂ p (hP₂ hp)
    obtain ⟨hopt, hpX, hlog⟩ := hg.2.2.2.2 2 (Or.inl rfl) p hprime hl hu
    exact ⟨hprime, hl, hu, hopt, hpX, hlog⟩
  · intro p hp
    obtain ⟨hprime, hl, hu⟩ := hS₄ p (hP₄ hp)
    obtain ⟨hopt, hpX, hlog⟩ := hg.2.2.2.2 4 (Or.inr rfl) p hprime hl hu
    exact ⟨hprime, hl, hu, hopt, hpX, hlog⟩

private theorem roster_log_error {X u : ℝ} (hu : 0 < u) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ u < (p : ℝ) ∧ (p : ℝ) ≤ u * (1 + 1 / log X ^ 6)) :
    (∑ p ∈ P, log p) = (P.card : ℝ) * log u + ∑ p ∈ P, log ((p : ℝ) / u) ∧
    0 ≤ ∑ p ∈ P, log ((p : ℝ) / u) ∧
    (∑ p ∈ P, log ((p : ℝ) / u)) ≤ (P.card : ℝ) / log X ^ 6 := by
  have hpoint (p : ℕ) (hp : p ∈ P) : 0 ≤ log ((p : ℝ) / u) ∧
      log ((p : ℝ) / u) ≤ 1 / log X ^ 6 := by
    obtain ⟨hprime, hl, hh⟩ := hP p hp
    have hr : 1 ≤ (p : ℝ) / u := by
      apply (le_div_iff₀ hu).mpr
      simpa using hl.le
    have hrU : (p : ℝ) / u ≤ 1 + 1 / log X ^ 6 := by
      apply (div_le_iff₀ hu).mpr
      simpa [mul_comm] using hh
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlog := log_le_sub_one_of_pos (div_pos hp0 hu)
    exact ⟨log_nonneg hr, by linarith⟩
  refine ⟨?_, sum_nonneg (fun p hp => (hpoint p hp).1), ?_⟩
  · calc
      _ = ∑ p ∈ P, (log u + log ((p : ℝ) / u)) := by
        apply sum_congr rfl
        intro p hp
        rw [log_div (by exact_mod_cast (hP p hp).1.ne_zero) hu.ne']
        ring
      _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  · have hh := sum_le_sum (fun p hp => (hpoint p hp).2)
    simpa only [sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul] using hh

/- One uniform threshold, chosen before every real clock and every actual
Budget. The integer is constructed from the complete reference higher core,
an actual retained prime prefix, and exactly 2A/4B distinct fresh insertions.
The displayed remainder is the full all-layer arithmetic loss. -/
set_option maxHeartbeats 4000000 in
-- The proof combines the finite-sum, curvature, and full residual estimates.
theorem actual_two_four_paid_prefix_repair :
    ∃ X0 : ℝ, 1 < X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ b : Budget, b.spec X → ∃ k Qprime : ℕ,
        2 ≤ k ∧ Qprime.Prime ∧ X / 2 < (Qprime : ℝ) ∧ (Qprime : ℝ) ≤ 2 * X ∧
        k.primeFactors = Nat.primesLE Qprime ∧ log (k : ℝ) < X ∧
        |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| +
          (actualDefect X k - completeFirstLayerLoss X k) +
          referencePrice X * (X - log (k : ℝ)) ≤ 10 / (X * log X ^ 3) := by
  classical
  obtain ⟨TD, _, hTD⟩ := budget_prefix_deletion_reserve_power 2 2000 (by norm_num)
  obtain ⟨TF, _, hTF⟩ := fresh_rosters
  have hall : ∀ᶠ X : ℝ in atTop, ∀ b : Budget, b.spec X → ∃ k Qprime : ℕ,
      2 ≤ k ∧ Qprime.Prime ∧ X / 2 < (Qprime : ℝ) ∧ (Qprime : ℝ) ≤ 2 * X ∧
      k.primeFactors = Nat.primesLE Qprime ∧ log (k : ℝ) < X ∧
      |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| +
        (actualDefect X k - completeFirstLayerLoss X k) +
        referencePrice X * (X - log (k : ℝ)) ≤ 10 / (X * log X ^ 3) := by
    filter_upwards [eventually_gt_atTop (4 : ℝ), eventually_ge_atTop TD,
      eventually_ge_atTop TF, eventual_scalar_estimates, eventual_roster_geometry]
      with X hX hXD hXF hscalar hgeo
    intro b hb
    obtain ⟨hL10, hαL, hαU, hδpos, hδα, hcL, hcU, heSmall, hCSmall, hLbig⟩ := hscalar
    have hb_spec := hb
    obtain ⟨hb2, hbdef, hhdef, hh0, hh, hQold, hd0, hdlog, hds,
      hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩ := hb
    have hX0 : 0 < X := by linarith
    have hL : 0 < log X := log_pos (by linarith)
    have hLambda := price_positive (by linarith : 1 < X)
    have hκ : 0 ≤ 1 / log X ^ 6 := by positivity
    let s : ℕ := ⌈100 * log X⌉₊
    have hs : (s : ℝ) ≤ 1000 * log X ^ 2 := by
      have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ 100 * log X)
      change (⌈100 * log X⌉₊ : ℝ) ≤ 1000 * log X ^ 2
      nlinarith only [hh, hL10]
    obtain ⟨Qs, Ds, hQsprime, hQslo, hQsQ, hDs, hDscard, hDsmem, hDssum, hDsU⟩ :=
      hTD X hXD b hb_spec s (hs.trans (by nlinarith [sq_nonneg (log X)]))
    have hseed (p : ℕ) (hp : p ∈ Ds) :
        log X - log 2 ≤ log p ∧ log p ≤ log X + log 2 := by
      obtain ⟨hprime, hpQs, hpQ⟩ := hDsmem p hp
      have hlo : X / 2 ≤ (p : ℝ) := hQslo.le.trans (by exact_mod_cast hpQs.le)
      have hhi : (p : ℝ) ≤ 2 * X := (by exact_mod_cast hpQ : (p : ℝ) ≤ b.Q).trans hQold.2
      have hl := log_le_log (by positivity : 0 < X / 2) hlo
      have hu := log_le_log (by exact_mod_cast hprime.pos) hhi
      rw [log_div hX0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hl
      rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at hu
      exact ⟨hl, by linarith only [hu]⟩
    have hdlog' : b.δ ≤ log X + log 2 := by
      rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at hdlog
      linarith
    obtain ⟨A, B, hM, hmeshL, hmeshU⟩ := finite_seed_coefficients
      hL10 hαL hαU hδpos hδα hcL hd0 hdlog' Ds hDscard hseed
    let M : ℕ := s + A + B
    have hM' : (M : ℝ) ≤ 1000 * log X ^ 2 := hM
    have hAB : (A + B : ℝ) ≤ 1000 * log X ^ 2 := by
      dsimp [M] at hM'
      push_cast at hM' ⊢
      linarith only [hM', (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
    obtain ⟨Q, D, hQprime, hQlo, hQb, hD, hDcard, hDmem, hDsum, hDU⟩ :=
      hTD X hXD b hb_spec M (hM'.trans (by nlinarith [sq_nonneg (log X)]))
    have hQs : Q ≤ Qs := by
      by_contra! hn
      have hsub : D ⊆ Ds := by
        rw [hD, hDs]
        intro p hp
        obtain ⟨hpold, hpnot⟩ := mem_sdiff.mp hp
        exact mem_sdiff.mpr ⟨hpold, fun hpQs => hpnot
          ((Nat.primesLE_mono hn.le) hpQs)⟩
      have hQDs : Q ∈ Ds := by
        rw [hDs]
        exact mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hQb, hQprime⟩,
          fun hp => hn.not_ge (Nat.mem_primesLE.mp hp).1⟩
      have hQnot : Q ∉ D := by
        rw [hD]
        intro h
        exact (mem_sdiff.mp h).2 (Nat.mem_primesLE.mpr ⟨le_rfl, hQprime⟩)
      have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
        intro he
        exact hQnot (he.symm ▸ hQDs)⟩)
      rw [hDcard, hDscard] at hc
      dsimp [M] at hc
      omega
    have hseedsub : Ds ⊆ D := by
      rw [hDs, hD]
      intro p hp
      obtain ⟨hpold, hpnot⟩ := mem_sdiff.mp hp
      exact mem_sdiff.mpr ⟨hpold, fun hpQ => hpnot ((Nat.primesLE_mono hQs) hpQ)⟩
    let T := D \ Ds
    have hTcard : T.card = A + B := by
      rw [show T = D \ Ds from rfl, Finset.card_sdiff_of_subset hseedsub, hDcard, hDscard]
      dsimp [M]
      omega
    obtain ⟨P₂, P₄, hP₂card, hP₄card, hdis, hP₂, hP₄⟩ := hTF X hXF A B hAB
    have hQshell : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X) :=
      ⟨hQlo.le, (by exact_mod_cast hQb : (Q : ℝ) ≤ b.Q).trans hQold.2⟩
    have hQ2 : 2 ≤ Q := by exact_mod_cast (show (2 : ℝ) ≤ Q by linarith)
    have hsupport (p : ℕ) (hp : p.Prime)
        (hv : 2 ≤ (strictInteger (referencePrice X)).factorization p) : p ≤ Q := by
      have hactive := (strict_layer_iff hLambda hp (by norm_num : 1 ≤ 2)).mp hv
      rw [← beta_nat hp (by norm_num : 1 ≤ 2)] at hactive
      have hpρ := (cutoff_occupancy (by norm_num : 2 ≤ 2) hLambda
        (by exact_mod_cast hp.two_le)).mp hactive
      have hρU : cutoff 2 (referencePrice X) ≤
          cutoff 2 (referencePrice X) * (1 + 1 / log X ^ 6) := by
        have hcut : 0 ≤ cutoff 2 (referencePrice X) := by linarith [hgeo.1]
        have hkappa : 0 ≤ 1 / log X ^ 6 := by positivity
        calc
          cutoff 2 (referencePrice X) = cutoff 2 (referencePrice X) * 1 := by ring
          _ ≤ cutoff 2 (referencePrice X) * (1 + 1 / log X ^ 6) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hcut
      exact_mod_cast (hpρ.trans_le (hρU.trans (hgeo.2.2.1.le.trans hQlo.le))).le
    let n := strictInteger (referencePrice X)
    let base := higherCore n * prefixInteger Q
    let k := base * (∏ p ∈ P₂, p) * (∏ p ∈ P₄, p)
    obtain ⟨hk2, hkp, hkf, hkl, hkh, hkr, hkall⟩ :=
      two_roster_integer_ledger_at_layers (by norm_num : 2 ≤ 2) (by norm_num : 2 ≤ 4)
        hX hQ2 hQshell hr hroot hsupport P₂ P₄ hdis
        (fun p hp => ⟨(hP₂ p hp).1, by exact_mod_cast (hP₂ p hp).2.2.2.2.1.le.trans hQlo.le,
          (hP₂ p hp).2.2.2.1⟩)
        (fun p hp => ⟨(hP₄ p hp).1, by exact_mod_cast (hP₄ p hp).2.2.2.2.1.le.trans hQlo.le,
          (hP₄ p hp).2.2.2.1⟩)
    change 2 ≤ k at hk2
    change k.primeFactors = Nat.primesLE Q at hkp
    change log (k : ℝ) = _ at hkl
    change actualDefect X k - completeFirstLayerLoss X k = _ at hkr
    rw [← hhdef] at hkl
    obtain ⟨hCraw, hlocal⟩ :=
      finite_prefix_deletion_cost hX b hb_spec hk2 hkp hQshell hQb D hD hDcard
    have hW0 : 0 ≤ uniformW X := by
      have hE := shellError_nonneg hX0.le
      dsimp [uniformW]
      positivity
    have hW : shellError X + 3 * sqrt X + (M : ℝ) * log (2 * X) + 1 ≤ uniformW X := by
      have hmul := mul_le_mul_of_nonneg_right hM' (log_pos (by linarith : 1 < 2 * X)).le
      have hlog2X := (log_shell hX).2.2
      have hh := mul_le_mul_of_nonneg_left hlog2X (by positivity : 0 ≤ 1000 * log X ^ 2)
      dsimp [uniformW]
      nlinarith only [hmul, hh]
    have hlocal' (p : ℕ) (hp : p ∈ T) : |log p - log X| ≤ (2 / X) * uniformW X := by
      have hpD : p ∈ D := (mem_sdiff.mp hp).1
      have hl := hlocal p (by exact_mod_cast (hDmem p hpD).2.1.le)
        (by exact_mod_cast (hDmem p hpD).2.2)
      apply hl.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith only [hW]
    let e₂ : ℝ := ∑ p ∈ P₂, log ((p : ℝ) / cutoff 2 (referencePrice X))
    let e₄ : ℝ := ∑ p ∈ P₄, log ((p : ℝ) / cutoff 4 (referencePrice X))
    let eD : ℝ := ∑ p ∈ T, (log p - log X)
    let e : ℝ := e₂ + e₄ - eD
    let Δ : ℝ := b.δ + ∑ p ∈ Ds, log p
    obtain ⟨hlog₂, he₂L, he₂U⟩ := roster_log_error (by linarith [hgeo.1]) P₂
      (fun p hp => ⟨(hP₂ p hp).1, (hP₂ p hp).2.1, (hP₂ p hp).2.2.1⟩)
    obtain ⟨hlog₄, he₄L, he₄U⟩ := roster_log_error (by linarith [hgeo.2.1]) P₄
      (fun p hp => ⟨(hP₄ p hp).1, (hP₄ p hp).2.1, (hP₄ p hp).2.2.1⟩)
    have hDlog : (∑ p ∈ D, log p) = (∑ p ∈ Ds, log p) + (A + B : ℝ) * log X + eD := by
      have hs := sum_sdiff hseedsub (f := fun p : ℕ => log p)
      have ht : eD = (∑ p ∈ T, log p) - (A + B : ℝ) * log X := by
        dsimp [eD]
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hTcard]
        push_cast
        ring
      change (∑ p ∈ T, log p) + (∑ p ∈ Ds, log p) = ∑ p ∈ D, log p at hs
      linarith only [hs, ht]
    have hθbudget : b.h + Chebyshev.theta (b.Q : ℝ) + b.δ = X := by
      have hlb : log (b.k : ℝ) = b.h + Chebyshev.theta (b.Q : ℝ) := by
        rw [hbdef, Nat.cast_mul, log_mul (by exact_mod_cast (higher_core_pos _).ne')
          (by exact_mod_cast (prefix_integer_pos _).ne'), prefix_integer_log, ← hhdef]
      linarith only [hlb, hbudget]
    have hCsigned : completeFirstLayerLoss X k - completeFirstLayerLoss X b.k =
        ∑ p ∈ D, rawLayerMargin X p 1 := by
      have hs := ordered_prefix_difference (by linarith : 1 < X) hkp hpref hQb
      have hblock : block (Q : ℝ) b.Q = D := by rw [hD]; simp [block]
      rw [hblock] at hs
      linarith only [hs]
    have hCprime (p : ℕ) (hp : p ∈ D) :
        |rawLayerMargin X p 1| ≤ (6 / X ^ 2) *
          (shellError X + b.h + b.δ + (M : ℝ) * log (2 * X) + 1) := by
      obtain ⟨hprime, hQp, hpQ⟩ := hDmem p hp
      have hptube : (p : ℝ) ∈ Set.Icc (X / 2) (2 * X) :=
        ⟨hQlo.le.trans (by exact_mod_cast hQp.le),
          (by exact_mod_cast hpQ : (p : ℝ) ≤ b.Q).trans hQold.2⟩
      have hθlo := Chebyshev.theta_mono (by exact_mod_cast hQp.le : (Q : ℝ) ≤ p)
      have hθhi := Chebyshev.theta_mono (by exact_mod_cast hpQ : (p : ℝ) ≤ b.Q)
      have hmass0 : 0 ≤ ∑ q ∈ D, log q := sum_nonneg (fun q hq => (hDmem q hq).1.log_pos.le)
      have hθp : |Chebyshev.theta (p : ℝ) - X| ≤ b.h + b.δ + (M : ℝ) * log (2 * X) := by
        apply abs_le.mpr
        constructor <;> linarith only [hθlo, hθhi, hDsum, hθbudget, hh0, hd0, hmass0, hDU]
      have hpX : |(p : ℝ) - X| ≤ shellError X + b.h + b.δ + (M : ℝ) * log (2 * X) := by
        have ht := abs_add_le ((p : ℝ) - Chebyshev.theta p) (Chebyshev.theta p - X)
        rw [sub_add_sub_cancel, abs_sub_comm (p : ℝ) (Chebyshev.theta p)] at ht
        linarith only [ht, pointwise_le_shellError hX0.le hptube, hθp]
      have hpr : |(p : ℝ) - b.r| ≤ shellError X + b.h + b.δ + (M : ℝ) * log (2 * X) + 1 := by
        have ht := abs_add_le ((p : ℝ) - X) (X - b.r)
        rw [sub_add_sub_cancel, abs_of_pos hXr] at ht
        linarith only [ht, hpX, hrX]
      rw [first_margin hprime]
      exact (raw_first_bound_at_root hX hr hroot hptube).trans
        (mul_le_mul_of_nonneg_left hpr (by positivity))
    have hlogexact : log (k : ℝ) = X - Δ + A * offset 2 X + B * offset 4 X + e := by
      rw [hP₂card] at hlog₂
      rw [hP₄card] at hlog₄
      dsimp [Δ, e, e₂, e₄, offset]
      push_cast at hlog₂ hlog₄ ⊢
      nlinarith only [hkl, hlog₂, hlog₄, hDlog, hDsum, hθbudget]
    have heDU : |eD| ≤ (A + B : ℝ) * (2 / X) * uniformW X := by
      calc
        _ ≤ ∑ p ∈ T, |log p - log X| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _p ∈ T, (2 / X) * uniformW X := sum_le_sum hlocal'
        _ = _ := by
          rw [sum_const, nsmul_eq_mul, hTcard]
          push_cast
          ring
    have hcount : (P₂.card + P₄.card : ℝ) ≤ 4000 * log X ^ 2 := by
      rw [hP₂card, hP₄card]
      push_cast
      nlinarith only [hAB, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
    have heabs : |e| ≤ 4000 / log X ^ 4 + 2000 * log X ^ 2 * uniformW X / X := by
      have he0 : |e₂ + e₄ - eD| ≤ |e₂ + e₄| + |eD| := by
        simpa [sub_zero, zero_sub, abs_neg] using (abs_sub_le (e₂ + e₄) 0 eD)
      have he₂L' : 0 ≤ e₂ := by simpa [e₂] using he₂L
      have he₄L' : 0 ≤ e₄ := by simpa [e₄] using he₄L
      have he0' := he0.trans (add_le_add_left (abs_add_le e₂ e₄) |eD|)
      rw [abs_of_nonneg he₂L', abs_of_nonneg he₄L'] at he0'
      have hc := div_le_div_of_nonneg_right hcount (by positivity : 0 ≤ log X ^ 6)
      have hd := mul_le_mul_of_nonneg_right hAB (by positivity : 0 ≤ (2 / X) * uniformW X)
      have halg : 4000 * log X ^ 2 / log X ^ 6 = 4000 / log X ^ 4 := by
        field_simp [hL.ne']
      dsimp [e, e₂, e₄] at *
      rw [halg] at hc
      have hsum : e₂ + e₄ ≤ (P₂.card + P₄.card : ℝ) / log X ^ 6 := by
        calc
          _ ≤ (P₂.card : ℝ) / log X ^ 6 + (P₄.card : ℝ) / log X ^ 6 :=
            add_le_add he₂U he₄U
          _ = _ := by ring
      have hsum' : e₂ + e₄ ≤ 4000 / log X ^ 4 := hsum.trans hc
      have hD' : |eD| ≤ 2000 * log X ^ 2 * uniformW X / X := by
        calc
          _ ≤ (A + B : ℝ) * (2 / X) * uniformW X := heDU
          _ ≤ 1000 * log X ^ 2 * (2 / X * uniformW X) := by
            simpa [mul_assoc] using hd
          _ = 2000 * log X ^ 2 * uniformW X / X := by ring
      exact he0'.trans (add_le_add hsum' hD')
    have hequarter : |e| ≤ curvature X / 4 := by
      have hs := mul_le_mul_of_nonneg_left heabs (sq_nonneg (log X))
      have healg : log X ^ 2 * (4000 / log X ^ 4 + 2000 * log X ^ 2 * uniformW X / X) =
          4000 / log X ^ 2 + 2000 * (uniformW X * log X ^ 4 / X) := by
        field_simp [hL.ne', hX0.ne']
      rw [healg] at hs
      have hprod : log X ^ 2 * |e| ≤ log X ^ 2 * (curvature X / 4) := by
        nlinarith only [hs, heSmall, hcL]
      exact le_of_mul_le_mul_left hprod (sq_pos_of_pos hL)
    have hslackL : 3 * curvature X / 4 ≤ X - log (k : ℝ) := by
      rw [hlogexact]
      have heL := (abs_le.mp hequarter).2
      have hmesh := hmeshL
      change curvature X ≤ Δ - A * offset 2 X - B * (2 * offset 2 X + curvature X) at hmesh
      have hmesh' : curvature X ≤ Δ - A * offset 2 X - B * offset 4 X := by
        calc
          _ ≤ Δ - A * offset 2 X - B * (2 * offset 2 X + curvature X) := hmesh
          _ = Δ - A * offset 2 X - B * offset 4 X := by
            dsimp [curvature]
            ring
      nlinarith only [hmesh', heL]
    have hslackU : X - log (k : ℝ) < 9 * curvature X / 4 := by
      rw [hlogexact]
      have heL := (abs_le.mp hequarter).1
      have hmesh := hmeshU
      change Δ - A * offset 2 X - B * (2 * offset 2 X + curvature X) < 2 * curvature X at hmesh
      have hmesh' : Δ - A * offset 2 X - B * offset 4 X < 2 * curvature X := by
        calc
          _ = Δ - A * offset 2 X - B * (2 * offset 2 X + curvature X) := by
            dsimp [curvature]
            ring
          _ < _ := hmesh
      nlinarith only [hmesh', heL]
    have hCscaled : |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| ≤
        referencePrice X / log X ^ 2 := by
      have hbound : |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| ≤
          24000 * uniformW X * log X ^ 2 / X ^ 2 := by
        have hpointW (p : ℕ) (hp : p ∈ D) : |rawLayerMargin X p 1| ≤ (6 / X ^ 2) * uniformW X := by
          apply (hCprime p hp).trans
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith only [hW, hh, hds]
        calc
          _ = |∑ p ∈ D, rawLayerMargin X p 1| := congrArg abs hCsigned
          _ ≤ ∑ p ∈ D, |rawLayerMargin X p 1| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ _p ∈ D, (6 / X ^ 2) * uniformW X := sum_le_sum hpointW
          _ = (M : ℝ) * ((6 / X ^ 2) * uniformW X) := by simp [hDcard]
          _ ≤ (1000 * log X ^ 2) * ((6 / X ^ 2) * uniformW X) :=
            mul_le_mul_of_nonneg_right hM' (by positivity)
          _ ≤ _ := by
            have hfactor : 0 ≤ uniformW X * log X ^ 2 / X ^ 2 := by positivity
            have heq :
                (1000 * log X ^ 2) * ((6 / X ^ 2) * uniformW X) =
                  6000 * (uniformW X * log X ^ 2 / X ^ 2) := by
              field_simp [hX0.ne']
              ring
            rw [heq]
            calc
              _ ≤ 24000 * (uniformW X * log X ^ 2 / X ^ 2) :=
                mul_le_mul_of_nonneg_right (by norm_num : (6000 : ℝ) ≤ 24000) hfactor
              _ = 24000 * uniformW X * log X ^ 2 / X ^ 2 := by ring
      apply hbound.trans
      have heq : 24000 * uniformW X * log X ^ 2 / X ^ 2 =
          (24000 * (uniformW X * log X ^ 5 / X)) * (referencePrice X / log X ^ 2) := by
        dsimp [referencePrice]
        field_simp [hX0.ne', hL.ne']
      rw [heq]
      exact mul_le_of_le_one_left (div_nonneg hLambda.le (sq_nonneg _)) hCSmall
    have hRhigher : actualDefect X k - completeFirstLayerLoss X k ≤
        referencePrice X / log X ^ 2 := by
      have hcut₂ : (2 : ℝ) < cutoff 2 (referencePrice X) := by
        linarith only [hgeo.1]
      have hroot₂ := (cutoff_spec (by norm_num : 2 ≤ 2) hLambda).2.2.1 hcut₂
      have hroot₄ := (cutoff_spec (by norm_num : 2 ≤ 4) hLambda).2.2.1
        (by linarith only [hgeo.2.1])
      have hterm₂ (p : ℕ) (hp : p ∈ P₂) :
          (referencePrice X - goldenLayerMarginal p 2) * log p ≤
            8 * (1 / log X ^ 6) * referencePrice X * log X := by
        have he := insertion_regret (by norm_num : 2 ≤ 2) (hP₂ p hp).1
          hcut₂.le hLambda hroot₂ hκ (hP₂ p hp).2.1.le (hP₂ p hp).2.2.1
        norm_num only [Nat.cast_ofNat] at he
        have hlog := (hP₂ p hp).2.2.2.2.2
        have hl0 := (hP₂ p hp).1.log_pos.le
        calc
          _ ≤ 4 * (1 / log X ^ 6) * referencePrice X * log X := by
            calc
              _ ≤ (4 * (1 / log X ^ 6) * referencePrice X) * log p :=
                mul_le_mul_of_nonneg_right he.2 hl0
              _ ≤ (4 * (1 / log X ^ 6) * referencePrice X) * log X :=
                mul_le_mul_of_nonneg_left hlog (by positivity)
              _ = _ := by ring
          _ ≤ _ := by
            calc
              4 * (1 / log X ^ 6) * referencePrice X * log X =
                  4 * ((1 / log X ^ 6) * referencePrice X * log X) := by ring
              _ ≤ 8 * ((1 / log X ^ 6) * referencePrice X * log X) := by
                exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
              _ = 8 * (1 / log X ^ 6) * referencePrice X * log X := by ring
      have hterm₄ (p : ℕ) (hp : p ∈ P₄) :
          (referencePrice X - goldenLayerMarginal p 4) * log p ≤
            8 * (1 / log X ^ 6) * referencePrice X * log X := by
        have hcut4 : (2 : ℝ) < cutoff 4 (referencePrice X) := by
          linarith only [hgeo.2.1]
        have he := insertion_regret (by norm_num : 2 ≤ 4) (hP₄ p hp).1
          hcut4.le hLambda hroot₄ hκ (hP₄ p hp).2.1.le (hP₄ p hp).2.2.1
        norm_num only [Nat.cast_ofNat] at he
        exact mul_le_mul he.2 (hP₄ p hp).2.2.2.2.2 (hP₄ p hp).1.log_pos.le (by positivity)
      have hsum₂ : (∑ p ∈ P₂, (referencePrice X - goldenLayerMarginal p 2) * log p) ≤
          ∑ _p ∈ P₂, 8 * (1 / log X ^ 6) * referencePrice X * log X :=
        by
          apply sum_le_sum
          intro p hp
          exact hterm₂ p hp
      have hsum₄ : (∑ p ∈ P₄, (referencePrice X - goldenLayerMarginal p 4) * log p) ≤
          ∑ _p ∈ P₄, 8 * (1 / log X ^ 6) * referencePrice X * log X :=
        by
          apply sum_le_sum
          intro p hp
          exact hterm₄ p hp
      have hsum := add_le_add hsum₂ hsum₄
      rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul] at hsum
      have hcount' := mul_le_mul_of_nonneg_right hcount
        (by positivity : 0 ≤ 8 * (1 / log X ^ 6) * referencePrice X * log X)
      have hbound : actualDefect X k - completeFirstLayerLoss X k ≤
          32000 * referencePrice X / log X ^ 3 := by
        rw [hkr]
        calc
          _ ≤ _ := hsum
          _ = (P₂.card + P₄.card : ℝ) * (8 * (1 / log X ^ 6) * referencePrice X * log X) := by ring
          _ ≤ _ := hcount'
          _ = _ := by field_simp [hL.ne']; ring
      apply hbound.trans
      apply (div_le_div_iff₀ (pow_pos hL 3) (sq_pos_of_pos hL)).mpr
      have hh := mul_le_mul_of_nonneg_right hLbig
        (mul_nonneg hLambda.le (sq_nonneg (log X)))
      nlinarith only [hh]
    have hlog2U : log (2 : ℝ) ≤ 1 := log_two_le_one
    have hlog20 : 0 ≤ log (2 : ℝ) := log_two_nonneg
    have hlog2sq : log (2 : ℝ) ^ 2 ≤ 1 := log_two_sq_le_one
    have hslackCost : referencePrice X * (X - log (k : ℝ)) ≤
        (9 / 2 : ℝ) * log 2 ^ 2 * (referencePrice X / log X ^ 2) := by
      have hδU : curvature X ≤ 2 * log 2 ^ 2 / log X ^ 2 :=
        le_div_log_sq (a := curvature X) (b := 2 * log 2 ^ 2)
          (L := log X) hL hcU
      have hsu : X - log (k : ℝ) ≤ (9 / 4 : ℝ) * curvature X := by
        linarith only [hslackU.le]
      have hmul : (9 / 4 : ℝ) * curvature X ≤
          (9 / 4 : ℝ) * (2 * log 2 ^ 2 / log X ^ 2) :=
        mul_le_mul_of_nonneg_left hδU (by norm_num)
      have hgap : X - log (k : ℝ) ≤
          (9 / 4 : ℝ) * (2 * log 2 ^ 2 / log X ^ 2) := hsu.trans hmul
      have hh := mul_le_mul_of_nonneg_left hgap hLambda.le
      convert hh using 1 <;> ring
    refine ⟨k, Q, hk2, hQprime, hQlo, hQshell.2, hkp, ?_, ?_⟩
    · have hpos : 0 < 3 * curvature X / 4 :=
        three_curvature_div_four_pos (c := curvature X) hδpos
      have hgap : 0 < X - log (k : ℝ) := lt_of_lt_of_le hpos hslackL
      linarith only [hgap]
    · have htarget : 10 / (X * log X ^ 3) = 10 * (referencePrice X / log X ^ 2) := by
        dsimp [referencePrice]
        field_simp [hX0.ne', hL.ne']
      rw [htarget]
      have hh := mul_le_mul_of_nonneg_right hlog2sq
        (by positivity : 0 ≤ referencePrice X / log X ^ 2)
      nlinarith only [hCscaled, hRhigher, hslackCost, hh,
        (div_pos hLambda (sq_pos_of_pos hL)).le]
  obtain ⟨T, hT⟩ := eventually_atTop.mp hall
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro X hX
  exact hT X ((le_max_left T 2).trans hX)

/-- An actual canonical Budget family is obtained from the existing crossing
constructor. No Budget-spec or paid-repair inequality is a premise. -/
theorem canonical_paid_prefix_budget_eventually :
    ∃ b : ℝ → Budget, ∀ᶠ X : ℝ in atTop, (b X).spec X ∧
      ∃ k Qprime : ℕ, 2 ≤ k ∧ Qprime.Prime ∧ X / 2 < (Qprime : ℝ) ∧
        (Qprime : ℝ) ≤ 2 * X ∧ k.primeFactors = Nat.primesLE Qprime ∧
        log (k : ℝ) < X ∧
        |completeFirstLayerLoss X k - completeFirstLayerLoss X (b X).k| +
          (actualDefect X k - completeFirstLayerLoss X k) +
          referencePrice X * (X - log (k : ℝ)) ≤ 10 / (X * log X ^ 3) := by
  classical
  let b : ℝ → Budget := fun X => if h : ∃ b : Budget, b.spec X then
    Classical.choose h else ⟨0, 0, 0, 0, 0⟩
  obtain ⟨X0, _, hX0⟩ := actual_two_four_paid_prefix_repair
  refine ⟨b, ?_⟩
  filter_upwards [canonical_budget_eventually, eventually_ge_atTop X0] with X hB hX
  have hb : (b X).spec X := by
    simpa only [b, dif_pos hB] using Classical.choose_spec hB
  exact ⟨hb, hX0 X hX (b X) hb⟩

#print axioms actual_two_four_paid_prefix_repair
#print axioms canonical_paid_prefix_budget_eventually
end D5.S3.Arith.Robin.PriceRecord.ActualTwoFourPaidPrefixRepair
