/- GID: D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Uniform moving-layer estimates and exact finite quantitative budget arithmetic. -/
import D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair
import D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Tactic

/-! UNCOMPILED_UNACCEPTED; RegUNVALIDATED.
Full source proof candidate, not native acceptance. The completed fixed-J owner
and Budget/prefix sources are imported, never forked. The accompanying patch only
exposes three actually consumed finite helpers. The growing-J analytic supplier
has a full by-body in eventual_growing_roster, with no target/window/PNT premise in either
final theorem. All bodies and imports remain subject to native diagnostics.
The existing real beta and literal arithmetic marginal retain their definitions. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerQuantitativeBudgetRepair
open Finset Filter Real Asymptotics
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
open D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope

private theorem reciprocal_log_bounds {s : ℝ} (hs : 0 < s) :
    1 / (s + 1) < log (1 + 1 / s) ∧ log (1 + 1 / s) < 1 / s := by
  have hx : 0 < 1 / s := one_div_pos.mpr hs
  constructor
  · have h := lt_log_one_add_of_pos hx
    have hr : 1 / (s + 1) < 2 * (1 / s) / (1 / s + 2) := by
      apply (div_lt_div_iff₀ (by linarith : 0 < s + 1)
        (by linarith : 0 < 1 / s + 2)).mpr
      field_simp [hs.ne']
      nlinarith
    exact hr.trans h
  · have h := log_lt_sub_one_of_pos
      (show 0 < 1 + 1 / s by linarith) (show 1 + 1 / s ≠ 1 by linarith)
    linarith

private theorem sum_add_one_le_twice {u : ℝ} (hu : 2 ≤ u) (j : ℕ) :
    powerSum j u + 1 ≤ 2 * u ^ j := by
  have hg := powerSum_geometric j u
  have hp := pow_nonneg (show 0 ≤ u by linarith) j
  have he : (u - 1) * (2 * u ^ j - (powerSum j u + 1)) =
      (u - 2) * u ^ j + 1 := by nlinarith [hg]
  have hn : 0 ≤ (u - 2) * u ^ j + 1 :=
    add_nonneg (mul_nonneg (by linarith : 0 ≤ u - 2) hp) zero_le_one
  have hd : 0 < u - 1 := by linarith
  have hh : 0 ≤ 2 * u ^ j - (powerSum j u + 1) := by
    exact nonneg_of_mul_nonneg_right (he.symm ▸ hn) hd
  linarith

private theorem beta_uniform_bounds {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 1 ≤ j) :
    1 / (2 * u ^ j * log u) ≤ beta j u ∧
      beta j u ≤ 1 / (u ^ j * log u) := by
  have hu0 : 0 < u := by linarith
  have hl : 0 < log u := log_pos (by linarith)
  have hs := powerSum_pos hu0 hj
  have hlow := (reciprocal_log_bounds hs).1.le
  have hr := one_div_le_one_div_of_le (by linarith : 0 < powerSum j u + 1)
    (sum_add_one_le_twice hu j)
  have hh := div_le_div_of_nonneg_right (hr.trans hlow) hl.le
  refine ⟨?_, beta_le_inv_pow_log hu hj⟩
  simpa only [beta, gain, div_div] using hh

private theorem weighted_sum_upper {u : ℝ} (hu : 0 ≤ u) (j : ℕ) :
    u * powerSumDerivative j u ≤ (j : ℝ) * powerSum j u := by
  calc
    _ = ∑ k ∈ range j, ((k + 1 : ℕ) : ℝ) * u ^ (k + 1) := by
      simp only [powerSumDerivative, mul_sum, pow_succ]
      apply sum_congr rfl
      intro k hk
      push_cast
      ring
    _ ≤ ∑ k ∈ range j, (j : ℝ) * u ^ (k + 1) := by
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hu _)
      exact_mod_cast (show k + 1 ≤ j by have := mem_range.mp hk; omega)
    _ = _ := by simp only [powerSum, mul_sum]

private theorem slope_upper {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 2 ≤ j) :
    logarithmicSlope j u ≤ 2 * (j : ℝ) := by
  have hu0 : 0 < u := by linarith
  have hs := powerSum_pos hu0 (show 1 ≤ j by omega)
  have hg := gain_pos hu0 (show 1 ≤ j by omega)
  have hD : 0 ≤ powerSumDerivative j u := by
    exact sum_nonneg fun k _ => mul_nonneg (by positivity) (pow_nonneg hu0.le k)
  have hB : u * powerSumDerivative j u / powerSum j u ≤ (j : ℝ) :=
    (div_le_iff₀ hs).mpr (weighted_sum_upper hu0.le j)
  have hB0 : 0 ≤ u * powerSumDerivative j u / powerSum j u := by positivity
  have hlog := (reciprocal_log_bounds hs).1.le
  have hf : (1 / powerSum j u) /
      ((1 + 1 / powerSum j u) * gain j u) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by positivity) hg)).mpr
    have hm := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ 1 + 1 / powerSum j u by positivity)
    have he : (1 + 1 / powerSum j u) * (1 / (powerSum j u + 1)) =
        1 / powerSum j u := by field_simp [hs.ne', (by linarith : powerSum j u + 1 ≠ 0)]
    dsimp only [gain]
    rw [he] at hm
    simpa only [one_mul] using hm
  have hprod := mul_le_mul_of_nonneg_left hf hB0
  have hl2 : (1 / 2 : ℝ) < log 2 := by
    have h := lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
    norm_num at h ⊢
    linarith
  have hl : (1 / 2 : ℝ) < log u := hl2.trans_le (log_le_log (by norm_num) hu)
  have hinv : 1 / log u ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < log u)).mpr
    linarith
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  dsimp only [logarithmicSlope]
  nlinarith

/-- Uniform in the full natural index and the full real half-line. -/
theorem uniform_beta_and_slope {j : ℕ} (hj : 2 ≤ j) {u : ℝ} (hu : 2 ≤ u) :
    1 / (2 * u ^ j * log u) ≤ beta j u ∧
      beta j u ≤ 1 / (u ^ j * log u) ∧
      0 < logarithmicSlope j u ∧ logarithmicSlope j u ≤ 2 * (j : ℝ) ∧
      HasDerivAt (fun v => log (beta j v)) (-logarithmicSlope j u / u) u := by
  have hb := beta_uniform_bounds hu (show 1 ≤ j by omega)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  exact ⟨hb.1, hb.2, (div_pos hj0 (by norm_num)).trans_le (logarithmicSlope_ge hu hj),
    slope_upper hu hj, log_beta_hasDerivAt hu (by omega)⟩

/-- Strict adjacent separation. It includes j=2 and u=2. -/
theorem adjacent_layer_strict {j : ℕ} (hj : 2 ≤ j) {u : ℝ} (hu : 2 ≤ u) :
    u * beta j u < beta (j - 1) u := by
  have hu0 : 0 < u := by linarith
  have hl : 0 < log u := log_pos (by linarith)
  have hs := powerSum_pos hu0 (show 1 ≤ j - 1 by omega)
  have hsum : powerSum j u = u * (powerSum (j - 1) u + 1) := by
    have h1 := powerSum_geometric j u
    have h2 := powerSum_geometric (j - 1) u
    have hp : u ^ j = u ^ (j - 1) * u := by
      rw [← pow_succ]; congr 1; omega
    rw [hp] at h1
    have he : (u - 1) * (powerSum j u - u * (powerSum (j - 1) u + 1)) = 0 := by
      nlinarith [h1, h2]
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (by linarith)))
  have hupp := (reciprocal_log_bounds (powerSum_pos hu0 (show 1 ≤ j by omega))).2
  have hlow := (reciprocal_log_bounds hs).1
  have hprod := mul_lt_mul_of_pos_left hupp hu0
  have he : u * (1 / powerSum j u) = 1 / (powerSum (j - 1) u + 1) := by
    rw [hsum]
    field_simp [hu0.ne', (by linarith : powerSum (j - 1) u + 1 ≠ 0)]
  rw [he] at hprod
  have hgain : u * gain j u < gain (j - 1) u := hprod.trans hlow
  simpa only [beta, mul_div_assoc] using (div_lt_div_iff_of_pos_right hl).mpr hgain

private theorem log_beta_drop_upper {j : ℕ} (hj : 2 ≤ j) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    log (beta j u / beta j v) ≤ 2 * (j : ℝ) * log (v / u) := by
  let f : ℝ → ℝ := fun t => log (beta j t) + 2 * (j : ℝ) * log t
  have hd (t : ℝ) (ht : 2 ≤ t) :
      HasDerivAt f ((2 * (j : ℝ) - logarithmicSlope j t) / t) t := by
    convert (log_beta_hasDerivAt ht (show 1 ≤ j by omega)).add
      ((hasDerivAt_log (by linarith : t ≠ 0)).const_mul (2 * (j : ℝ))) using 1 <;> ring
  have hmono : MonotoneOn f (Set.Ici 2) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 2)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact div_nonneg (sub_nonneg.mpr (slope_upper (interior_subset ht) hj))
        (by have ht2 : 2 ≤ t := interior_subset ht; linarith)
  have h := hmono hu (hu.trans huv) huv
  dsimp only [f] at h
  rw [log_div (by linarith : v ≠ 0) (by linarith : u ≠ 0),
    log_div (beta_pos hu (by omega)).ne' (beta_pos (hu.trans huv) (by omega)).ne']
  linarith

/-- The exact moving-window ratio, without a fixed-index limit. The endpoint b
is included and the root is excluded, even if either endpoint is prime. -/
theorem moving_interval_marginals {j : ℕ} (hj : 3 ≤ j) {ρ priceLambda q : ℝ}
    (hρ : 2 ≤ ρ) (hLambda : 0 < priceLambda) (hroot : beta j ρ = priceLambda)
    (hq : ρ < q) (hqb : q ≤ ρ * (1 + 1 / (j : ℝ) ^ 2)) :
    exp (-2 / (j : ℝ)) * priceLambda ≤ beta j q ∧ beta j q < priceLambda ∧
      0 < priceLambda - beta j q ∧ priceLambda - beta j q ≤ (2 / (j : ℝ)) * priceLambda := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hρ0 : 0 < ρ := by linarith
  have hq2 : 2 ≤ q := hρ.trans hq.le
  have hlog := log_beta_drop_upper (show 2 ≤ j by omega) hρ hq.le
  have hratio : q / ρ ≤ 1 + 1 / (j : ℝ) ^ 2 := (div_le_iff₀ hρ0).mpr (by nlinarith)
  have hlogratio : log (q / ρ) ≤ 1 / (j : ℝ) ^ 2 := by
    have h1 := log_le_log (div_pos (by linarith : 0 < q) hρ0) hratio
    have h2 := log_le_sub_one_of_pos (show 0 < 1 + 1 / (j : ℝ) ^ 2 by positivity)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlogratio (show 0 ≤ 2 * (j : ℝ) by positivity)
  have he : 2 * (j : ℝ) * (1 / (j : ℝ) ^ 2) = 2 / (j : ℝ) := by
    field_simp [hj0.ne']
  rw [he] at hmul
  rw [hroot] at hlog
  have hlogs : -2 / (j : ℝ) ≤ log (beta j q) - log priceLambda := by
    rw [log_div hLambda.ne' (beta_pos hq2 (by omega)).ne'] at hlog
    have hneg : -(2 * (j : ℝ) * log (q / ρ)) ≤
        log (beta j q) - log priceLambda := by linarith only [hlog]
    have hneg' : -2 / (j : ℝ) ≤ -(2 * (j : ℝ) * log (q / ρ)) := by
      convert neg_le_neg hmul using 1 <;> ring
    exact hneg'.trans hneg
  have hexp := exp_le_exp.mpr hlogs
  have hlow : exp (-2 / (j : ℝ)) * priceLambda ≤ beta j q := by
    rw [exp_sub, exp_log (beta_pos hq2 (by omega)), exp_log hLambda] at hexp
    exact (le_div_iff₀ hLambda).mp hexp
  have hstrict : beta j q < priceLambda := by
    rw [← hroot]
    exact beta_strictAntiOn (show 2 ≤ j by omega) hρ hq2 hq
  have hlin := add_one_le_exp (-2 / (j : ℝ))
  have hm := mul_le_mul_of_nonneg_right hlin hLambda.le
  have hbeta : (1 - 2 / (j : ℝ)) * priceLambda ≤ beta j q := by
    convert hm.trans hlow using 1 <;> ring
  exact ⟨hlow, hstrict, sub_pos.mpr hstrict, by nlinarith only [hbeta]⟩

/-- No asymptotic or root supplier: these are consequences of the literal root
and elementary index inequalities, uniformly in j. -/
theorem uniform_root_geometry {j : ℕ} (hj : 3 ≤ j) {X M ρ : ℝ}
    (hXpos : 1 < X) (hX : 4 ≤ log X) (hM : 2 ≤ M) (hρ : 2 ≤ ρ)
    (hroot : beta j ρ = referencePrice X)
    (hjlo : log X / (2 * M) ≤ (j : ℝ))
    (hjhi : (j : ℝ) ≤ log X / M) :
    X * log X / 2 ≤ ρ ^ j * log ρ ∧ ρ ^ j * log ρ ≤ X * log X ∧
      log X + log (log X) - log 2 ≤ (j : ℝ) * log ρ + log (log ρ) ∧
      (j : ℝ) * log ρ + log (log ρ) ≤ log X + log (log X) ∧
      M / 2 ≤ log ρ ∧ log ρ ≤ 4 * M ∧
      log X - log 2 ≤ (j : ℝ) * log ρ ∧
      (j : ℝ) * log ρ ≤ log X + log (log X) := by
  have hX0 : 0 < X := by linarith
  have hL : 0 < log X := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hy : 0 < log ρ := log_pos (by linarith)
  have hjr : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hp := pow_pos hρ0 j
  have hb := beta_uniform_bounds hρ (show 1 ≤ j by omega)
  rw [hroot] at hb
  have hXL : 0 < X * log X := mul_pos hX0 hL
  have hLambda : referencePrice X = 1 / (X * log X) := rfl
  have hlow : X * log X / 2 ≤ ρ ^ j * log ρ := by
    have h := (one_div_le_one_div (show 0 < 2 * ρ ^ j * log ρ by positivity) hXL).mp
      (hLambda ▸ hb.1)
    linarith
  have hupp : ρ ^ j * log ρ ≤ X * log X := by
    exact (one_div_le_one_div hXL (mul_pos hp hy)).mp (hLambda ▸ hb.2)
  have hloglo := log_le_log (div_pos hXL (by norm_num)) hlow
  have hloghi := log_le_log (mul_pos hp hy) hupp
  rw [log_div hXL.ne' (by norm_num : (2 : ℝ) ≠ 0), log_mul hX0.ne' hL.ne',
    log_mul hp.ne' hy.ne', log_pow] at hloglo
  rw [log_mul hp.ne' hy.ne', log_pow, log_mul hX0.ne' hL.ne'] at hloghi
  have h2 : log 2 ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hyL : log ρ ≤ log X := by
    by_contra! hn
    have hll := log_le_log hL hn.le
    have hjy : log ρ ≤ (j : ℝ) * log ρ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ j by linarith) hy.le
    linarith
  have hJylo : log X - log 2 ≤ (j : ℝ) * log ρ := by
    have hh := log_le_log hy hyL
    linarith
  have hhalf : log X / 2 ≤ (j : ℝ) * log ρ := by linarith
  have hJMul : (j : ℝ) * M ≤ log X := (le_div_iff₀ (by linarith : 0 < M)).mp hjhi
  have hlower : M / 2 ≤ log ρ := by
    by_contra! hbad
    have hm := mul_lt_mul_of_pos_left hbad hj0
    nlinarith
  have hy1 : 1 ≤ log ρ := by linarith
  have hJyhi : (j : ℝ) * log ρ ≤ log X + log (log X) := by
    linarith [log_nonneg hy1]
  have hlogL : log (log X) ≤ log X := log_le_self hL.le
  have hJlower : log X ≤ (j : ℝ) * (2 * M) :=
    (div_le_iff₀ (by linarith : 0 < 2 * M)).mp hjlo
  have hupper : log ρ ≤ 4 * M := by
    have hh := mul_le_mul_of_nonneg_right hJlower hy.le
    by_contra! hbad
    have hm := mul_lt_mul_of_pos_left hbad hj0
    nlinarith
  exact ⟨hlow, hupp, hloglo, hloghi, hlower, hupper, hJylo, hJyhi⟩

/-- Exact floor arithmetic. Threshold selection is performed later in eventual_growing_roster. No fixed finite set of layer indices is used. -/
theorem growing_layer_floor_bounds {L M : ℝ} (hL : 0 < L) (hM : 1 ≤ M)
    (hlarge : 6 ≤ L / M) :
    3 ≤ ⌊L / M⌋₊ ∧ L / (2 * M) ≤ (⌊L / M⌋₊ : ℝ) ∧
      (⌊L / M⌋₊ : ℝ) ≤ L / M ∧ (⌊L / M⌋₊ : ℝ) ≤ L := by
  have hM0 : 0 < M := by linarith
  have hratio : 0 ≤ L / M := (div_pos hL hM0).le
  have hfloor := Nat.floor_le hratio
  have herr := Nat.lt_floor_add_one (L / M)
  have h3 : (3 : ℝ) ≤ L / M := by linarith
  have hj : 3 ≤ ⌊L / M⌋₊ := (Nat.le_floor_iff hratio).mpr h3
  have hhalf : L / (2 * M) ≤ (⌊L / M⌋₊ : ℝ) := by
    have he : L / (2 * M) = (L / M) / 2 := by ring
    rw [he]
    linarith
  have hlast : L / M ≤ L := by
    apply (div_le_iff₀ hM0).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hM hL.le
  exact ⟨hj, hhalf, hfloor, hfloor.trans hlast⟩

private theorem sqrt_le_pnt_model {c : ℝ} (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, sqrt t ≤ t * exp (-c * log t ^ (1 / 10 : ℝ)) := by
  have hlim : Tendsto (fun t : ℝ => c * log t ^ (-(9 / 10 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp
      tendsto_log_atTop).const_mul c
  have hevent := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hevent, eventually_gt_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := by linarith
  have hl : 0 < log t := log_pos ht1
  have hid : log t ^ (1 / 10 : ℝ) = log t * log t ^ (-(9 / 10 : ℝ)) := by
    calc
      log t ^ (1 / 10 : ℝ) = log t ^ ((1 : ℝ) + (-(9 / 10 : ℝ))) := by norm_num
      _ = log t ^ (1 : ℝ) * log t ^ (-(9 / 10 : ℝ)) := rpow_add hl _ _
      _ = _ := by rw [rpow_one]
  have hsmall : c * log t ^ (1 / 10 : ℝ) ≤ log t / 2 := by
    rw [hid]
    have hh := mul_le_mul_of_nonneg_right ht.le hl.le
    nlinarith
  rw [sqrt_eq_rpow, rpow_def_of_pos ht0]
  calc
    exp (log t * (1 / 2 : ℝ)) ≤ exp (log t - c * log t ^ (1 / 10 : ℝ)) :=
      exp_le_exp.mpr (by linarith)
    _ = t * exp (-c * log t ^ (1 / 10 : ℝ)) := by
      rw [exp_sub, exp_log ht0, div_eq_mul_inv, ← exp_neg]
      ring

/-- One weakened exponential theta estimate, derived directly from the actual
canonical MediumPNT and psi-minus-theta theorem. All constants precede t. -/
theorem quantitative_theta_error : ∃ c1 A Y0 : ℝ,
    0 < c1 ∧ 1 ≤ A ∧ 1 < Y0 ∧ ∀ t : ℝ, Y0 ≤ t →
      |Chebyshev.theta t - t| ≤ A * t * exp (-c1 * log t ^ (1 / 10 : ℝ)) := by
  obtain ⟨c, hc, hpnt⟩ := _root_.MediumPNT
  obtain ⟨B, hB⟩ := hpnt.bound
  obtain ⟨D, hD⟩ := Chebyshev.isBigO_psi_sub_theta_sqrt.bound
  let c1 := c / 2
  have hc1 : 0 < c1 := by dsimp [c1]; positivity
  have hs := sqrt_le_pnt_model hc1
  have hall : ∀ᶠ t : ℝ in atTop,
      |Chebyshev.theta t - t| ≤ (|B| + |D| + 1) * t *
        exp (-c1 * log t ^ (1 / 10 : ℝ)) := by
    filter_upwards [hB, hD, hs, eventually_gt_atTop (1 : ℝ)] with t hBt hDt hst ht
    have ht0 : 0 < t := by linarith
    have hl0 : 0 ≤ log t := (log_pos ht).le
    have hp0 : 0 ≤ log t ^ (1 / 10 : ℝ) := rpow_nonneg hl0 _
    have he : exp (-c * log t ^ (1 / 10 : ℝ)) ≤
        exp (-c1 * log t ^ (1 / 10 : ℝ)) := by
      apply exp_le_exp.mpr
      dsimp only [c1]
      nlinarith [mul_nonneg hc.le hp0]
    have hpsi : |Chebyshev.psi t - t| ≤ |B| * t *
        exp (-c1 * log t ^ (1 / 10 : ℝ)) := by
      simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs,
        abs_of_pos (mul_pos ht0 (exp_pos _))] at hBt
      calc
        _ ≤ B * (t * exp (-c * log t ^ (1 / 10 : ℝ))) := hBt
        _ ≤ |B| * (t * exp (-c * log t ^ (1 / 10 : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg B) ht0.le)]
    have hpt : |Chebyshev.psi t - Chebyshev.theta t| ≤
        |D| * (t * exp (-c1 * log t ^ (1 / 10 : ℝ))) := by
      simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg t)] at hDt
      exact hDt.trans ((mul_le_mul_of_nonneg_right (le_abs_self D) (sqrt_nonneg t)).trans
        (mul_le_mul_of_nonneg_left hst (abs_nonneg D)))
    have htri : |Chebyshev.theta t - t| ≤ |Chebyshev.psi t - t| +
        |Chebyshev.psi t - Chebyshev.theta t| := by
      calc
        _ = |(Chebyshev.psi t - t) + -(Chebyshev.psi t - Chebyshev.theta t)| := by
          congr 1; ring
        _ ≤ |Chebyshev.psi t - t| + |-(Chebyshev.psi t - Chebyshev.theta t)| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    nlinarith [mul_pos ht0 (exp_pos (-c1 * log t ^ (1 / 10 : ℝ)))]
  obtain ⟨T, hT⟩ := eventually_atTop.mp hall
  refine ⟨c1, |B| + |D| + 1, max T 2, hc1, ?_, ?_, ?_⟩
  · linarith [abs_nonneg B, abs_nonneg D]
  · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  · intro t ht
    exact hT t ((le_max_left _ _).trans ht)

/-- A fixed A0 with c1*A0>=12 suffices; the slightly larger constant avoids
any new algebraic-root constant. This proves the actual L^-6 suppression. -/
theorem root_pnt_suppression {c1 A0 L y : ℝ} (hc : 0 < c1)
    (hA : 1 ≤ A0) (hL : 1 < L) (hlarge : 12 ≤ c1 * A0)
    (hy : (A0 * log L) ^ 10 / 2 ≤ y) :
    exp (-c1 * y ^ (1 / 10 : ℝ)) ≤ 1 / L ^ 6 := by
  have hl : 0 < log L := log_pos hL
  have ha : 0 < A0 * log L := mul_pos (by linarith) hl
  have ha10 : 0 ≤ (A0 * log L) ^ 10 := pow_nonneg ha.le _
  have hpow : (A0 * log L / 2) ^ 10 ≤ y := by
    have he : (A0 * log L / 2) ^ 10 = (A0 * log L) ^ 10 / 1024 := by
      rw [div_pow]; norm_num
    rw [he]
    linarith
  have hroot := rpow_le_rpow (pow_nonneg (show 0 ≤ A0 * log L / 2 by positivity) 10)
    hpow (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have he : ((A0 * log L / 2) ^ 10) ^ (1 / 10 : ℝ) = A0 * log L / 2 := by
    simpa using pow_rpow_inv_natCast (show 0 ≤ A0 * log L / 2 by positivity)
      (by norm_num : (10 : ℕ) ≠ 0)
  rw [he] at hroot
  have hcroot := mul_le_mul_of_nonneg_left hroot hc.le
  have hamul := mul_le_mul_of_nonneg_right hlarge hl.le
  have hexp : exp (-c1 * y ^ (1 / 10 : ℝ)) ≤ exp (-(6 * log L)) :=
    exp_le_exp.mpr (by nlinarith)
  have heq : exp (-(6 * log L)) = 1 / L ^ 6 := by
    have hpow : exp (6 * log L) = L ^ 6 := by
      change exp (((6 : ℕ) : ℝ) * log L) = L ^ 6
      rw [Real.exp_nat_mul, exp_log (by linarith : 0 < L)]
    rw [exp_neg, hpow]
    simp [one_div]
  exact hexp.trans_eq heq

private theorem endpoint_theta_mass {c A L ρ : ℝ} {j : ℕ}
    (hc : 0 < c) (hA : 0 ≤ A) (hL : 0 < L) (hρ : 2 ≤ ρ)
    (hj : 3 ≤ j) (hjL : (j : ℝ) ≤ L) (hAL : 6 * A ≤ L ^ 4)
    (hdecay : exp (-c * log ρ ^ (1 / 10 : ℝ)) ≤ 1 / L ^ 6)
    (hlo : |Chebyshev.theta ρ - ρ| ≤ A * ρ * exp (-c * log ρ ^ (1 / 10 : ℝ)))
    (hhi : |Chebyshev.theta (ρ * (1 + 1 / (j : ℝ) ^ 2)) -
        ρ * (1 + 1 / (j : ℝ) ^ 2)| ≤
      A * (ρ * (1 + 1 / (j : ℝ) ^ 2)) *
        exp (-c * log (ρ * (1 + 1 / (j : ℝ) ^ 2)) ^ (1 / 10 : ℝ))) :
    ρ / (2 * (j : ℝ) ^ 2) ≤
      Chebyshev.theta (ρ * (1 + 1 / (j : ℝ) ^ 2)) - Chebyshev.theta ρ := by
  have hρ0 : 0 < ρ := by linarith
  have hjr : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  let b := ρ * (1 + 1 / (j : ℝ) ^ 2)
  have hb : ρ ≤ b := by
    have hh := mul_nonneg hρ0.le (one_div_nonneg.mpr (sq_nonneg (j : ℝ)))
    dsimp only [b]
    nlinarith
  have hb3 : b + ρ ≤ 3 * ρ := by
    have hs : 1 / (j : ℝ) ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hj0)).mpr
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hs hρ0.le
    dsimp only [b]
    nlinarith
  have hexp : exp (-c * log b ^ (1 / 10 : ℝ)) ≤
      exp (-c * log ρ ^ (1 / 10 : ℝ)) := by
    have hlog := log_le_log hρ0 hb
    have hp := rpow_le_rpow (log_pos (by linarith : 1 < ρ)).le hlog
      (by norm_num : (0 : ℝ) ≤ 1 / 10)
    apply exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hp hc.le
    linarith
  have hsmall : 3 * A / L ^ 6 ≤ 1 / (2 * (j : ℝ) ^ 2) := by
    have hsq : (j : ℝ) ^ 2 ≤ L ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 6 * A by positivity)
    have hprod2 := mul_le_mul_of_nonneg_right hAL (sq_nonneg L)
    have he : L ^ 4 * L ^ 2 = L ^ 6 := by ring
    rw [he] at hprod2
    apply (div_le_div_iff₀ (pow_pos hL 6) (by positivity : 0 < 2 * (j : ℝ) ^ 2)).mpr
    nlinarith
  have hb0 : 0 ≤ b := (hρ0.trans_le hb).le
  have hhi' : |Chebyshev.theta b - b| ≤ A * b / L ^ 6 := by
    have he := hexp.trans hdecay
    have hh := hhi.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hA hb0))
    simpa only [b, div_eq_mul_inv, one_mul, mul_assoc] using hh
  have hlo' : |Chebyshev.theta ρ - ρ| ≤ A * ρ / L ^ 6 := by
    have hh := hlo.trans (mul_le_mul_of_nonneg_left hdecay (mul_nonneg hA hρ0.le))
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hh
  have herr : A * b / L ^ 6 + A * ρ / L ^ 6 ≤ 3 * A * ρ / L ^ 6 := by
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right (pow_pos hL 6)).mpr
    nlinarith [hb3]
  have hsmallρ := mul_le_mul_of_nonneg_left hsmall hρ0.le
  have hwidth : b - ρ = ρ / (j : ℝ) ^ 2 := by dsimp [b]; ring
  have hneed : ρ / (2 * (j : ℝ) ^ 2) ≤
      Chebyshev.theta b - Chebyshev.theta ρ := by
    have hl := (abs_le.mp hlo').2
    have hh := (abs_le.mp hhi').1
    have he : ρ * (1 / (2 * (j : ℝ) ^ 2)) = ρ / (2 * (j : ℝ) ^ 2) := by ring
    rw [he] at hsmallρ
    have he2 : ρ / (j : ℝ) ^ 2 = 2 * (ρ / (2 * (j : ℝ) ^ 2)) := by ring
    rw [he2] at hwidth
    have herr' : A * b / L ^ 6 + A * ρ / L ^ 6 ≤
        ρ * (3 * A / L ^ 6) := by
      calc
        _ ≤ 3 * A * ρ / L ^ 6 := herr
        _ = ρ * (3 * A / L ^ 6) := by ring
    have hErrTarget : A * b / L ^ 6 + A * ρ / L ^ 6 ≤
        ρ / (2 * (j : ℝ) ^ 2) := herr'.trans hsmallρ
    calc
      _ ≤ (b - ρ) - (A * b / L ^ 6 + A * ρ / L ^ 6) := by
        linarith only [hwidth, hErrTarget]
      _ ≤ (b - ρ) + (Chebyshev.theta b - b) -
          (Chebyshev.theta ρ - ρ) := by
        linarith only [hh, hl]
      _ = Chebyshev.theta b - Chebyshev.theta ρ := by ring
  exact hneed

private theorem prime_interval_sum {ρ b : ℝ} (hρ : 0 ≤ ρ) (hρb : ρ ≤ b) :
    let S := Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊ρ⌋₊
    Chebyshev.theta b - Chebyshev.theta ρ = ∑ p ∈ S, log p ∧
      ∀ p ∈ S, p.Prime ∧ ρ < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  classical
  have hsub : Nat.primesLE ⌊ρ⌋₊ ⊆ Nat.primesLE ⌊b⌋₊ := by
    intro p hp
    obtain ⟨hpρ, hpp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpρ.trans (Nat.floor_mono hρb), hpp⟩
  constructor
  · rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    have he := sum_sdiff hsub (f := fun p : ℕ => log p)
    linarith
  · intro p hp
    obtain ⟨hpb, hnpρ⟩ := mem_sdiff.mp hp
    obtain ⟨hpb, hpp⟩ := Nat.mem_primesLE.mp hpb
    refine ⟨hpp, ?_, (Nat.le_floor_iff (hρ.trans hρb)).mp hpb⟩
    by_contra! hbad
    exact hnpρ (Nat.mem_primesLE.mpr ⟨Nat.le_floor hbad, hpp⟩)

/-- Quantitative PNT at BOTH actual varying endpoints gives 2*j+2 distinct
primes. No fixed-cardinality prime-window theorem is used. All constants are
chosen from MediumPNT before L,rho,j; the explicit inequalities are finite
endpoint conditions, discharged in eventual_growing_roster. -/
theorem quantitative_moving_prime_roster : ∃ c A Y0 : ℝ,
    0 < c ∧ 1 ≤ A ∧ 1 < Y0 ∧
    ∀ (L ρ : ℝ) (j : ℕ), 3 ≤ j → 4 ≤ L → 2 ≤ ρ → Y0 ≤ ρ →
      (j : ℝ) ≤ L → 6 * A ≤ L ^ 4 → L ^ 6 ≤ ρ →
      log (ρ * (1 + 1 / (j : ℝ) ^ 2)) ≤ L →
      exp (-c * log ρ ^ (1 / 10 : ℝ)) ≤ 1 / L ^ 6 →
      ρ / (2 * (j : ℝ) ^ 2) ≤
        Chebyshev.theta (ρ * (1 + 1 / (j : ℝ) ^ 2)) - Chebyshev.theta ρ ∧
      ∃ S : Finset ℕ, S.card = 2 * j + 2 ∧
        ∀ p ∈ S, p.Prime ∧ ρ < (p : ℝ) ∧
          (p : ℝ) ≤ ρ * (1 + 1 / (j : ℝ) ^ 2) := by
  classical
  obtain ⟨c, A, Y0, hc, hA, hY, htheta⟩ := quantitative_theta_error
  refine ⟨c, A, Y0, hc, hA, hY, ?_⟩
  intro L ρ j hj hL hρ hYρ hjL hAL hρlarge hz hdecay
  have hL0 : 0 < L := by linarith
  have hjr : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hρ0 : 0 < ρ := by linarith
  let b := ρ * (1 + 1 / (j : ℝ) ^ 2)
  have hb : ρ ≤ b := by
    have hh := mul_nonneg hρ0.le (one_div_nonneg.mpr (sq_nonneg (j : ℝ)))
    dsimp only [b]
    nlinarith
  have hmass := endpoint_theta_mass hc (by linarith : 0 ≤ A) hL0 hρ hj hjL hAL
    hdecay (htheta ρ hYρ) (htheta b (hYρ.trans hb))
  refine ⟨hmass, ?_⟩
  let T := Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊ρ⌋₊
  obtain ⟨hsum, hT⟩ := prime_interval_sum hρ0.le hb
  have hsumupper : (∑ p ∈ T, log p) ≤ (T.card : ℝ) * L := by
    calc
      _ ≤ ∑ p ∈ T, L := by
        apply sum_le_sum
        intro p hp
        have hpb := (hT p hp).2.2
        exact (log_le_log (by exact_mod_cast (hT p hp).1.pos) hpb).trans hz
      _ = _ := by simp
  have hcount : 2 * j + 2 ≤ T.card := by
    by_contra! hbad
    have hbadR : (T.card : ℝ) < 2 * (j : ℝ) + 2 := by exact_mod_cast hbad
    have hmassupper : ρ / (2 * (j : ℝ) ^ 2) < (2 * L + 2) * L := by
      have hc := mul_lt_mul_of_pos_right hbadR hL0
      have hmono : (2 * (j : ℝ) + 2) * L ≤ (2 * L + 2) * L := by nlinarith
      linarith [hmass, hsumupper]
    have hden : 0 < 2 * (j : ℝ) ^ 2 := by positivity
    have hrho : ρ < ((2 * L + 2) * L) * (2 * (j : ℝ) ^ 2) :=
      (div_lt_iff₀ hden).mp hmassupper
    have hs : (j : ℝ) ^ 2 ≤ L ^ 2 := by nlinarith
    have hpoly : ((2 * L + 2) * L) * (2 * (j : ℝ) ^ 2) ≤ 5 * L ^ 4 := by
      have h1 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * ((2 * L + 2) * L) by positivity)
      have h2 : 2 * L + 2 ≤ (5 / 2 : ℝ) * L := by linarith
      have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 2 * L ^ 3 by positivity)
      nlinarith
    have h16 : 16 ≤ L ^ 2 := by nlinarith
    have hp4 : 0 ≤ L ^ 4 := pow_nonneg hL0.le _
    have hpow : 5 * L ^ 4 < L ^ 6 := by
      have hmul := mul_le_mul_of_nonneg_right h16 hp4
      have he : L ^ 2 * L ^ 4 = L ^ 6 := by ring
      rw [he] at hmul
      have hp4pos : 0 < L ^ 4 := pow_pos hL0 _
      nlinarith
    linarith
  obtain ⟨S, hST, hcard⟩ := exists_subset_card_eq hcount
  exact ⟨S, hcard, fun p hp => hT p (hST hp)⟩

/-- Finite arithmetic stage: eventual_growing_roster supplies its explicit roster
in the final theorem. The existing finite helpers are reused without copying. -/
theorem finite_roster_quantitative_repair {X : ℝ} (hX : 14 ≤ X)
    {b : Budget} (hb : b.spec X) {J : ℕ} (hJ : 3 ≤ J) (S : Finset ℕ)
    (hfull : log (2 * X) < ∑ p ∈ S, log p)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ b.Q ∧
      log p ≤ 2 * log X / (J : ℝ) ∧
      b.k.factorization p = J - 1 ∧
      goldenLayerMarginal p J < referencePrice X ∧
      referencePrice X - goldenLayerMarginal p J ≤ (2 / (J : ℝ)) * referencePrice X) :
    ∃ (k : ℕ) (A : Finset ℕ), A ⊆ S ∧
      2 ≤ k ∧ k.primeFactors = Nat.primesLE b.Q ∧
      k = b.k * ∏ p ∈ A, p ∧
      (∀ p : ℕ, k.factorization p = b.k.factorization p + if p ∈ A then 1 else 0) ∧
      log (k : ℝ) - log (b.k : ℝ) = ∑ p ∈ A, log p ∧
      0 ≤ log (k : ℝ) - log (b.k : ℝ) ∧
      log (k : ℝ) - log (b.k : ℝ) ≤ b.δ ∧
      0 ≤ X - log (k : ℝ) ∧ X - log (k : ℝ) < 2 * log X / (J : ℝ) ∧
      actualDefect X k - completeFirstLayerLoss X k =
        ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p ∧
      0 ≤ actualDefect X k - completeFirstLayerLoss X k +
        referencePrice X * (X - log (k : ℝ)) ∧
      actualDefect X k - completeFirstLayerLoss X k +
        referencePrice X * (X - log (k : ℝ)) ≤ 6 / (X * (J : ℝ)) := by
  classical
  have hX0 : 0 < X := by linarith
  have hL : 0 < log X := log_pos (by linarith)
  have hLambda := reference_price_pos (show 1 < X by linarith)
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  rcases hb with ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0, hdlog, hds,
    hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩
  have hb' : b.spec X := ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0, hdlog, hds,
    hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩
  obtain ⟨A, hAS, hAd, hdnew0, hdnew⟩ :=
    ActualHigherLayerBudgetRepair.finite_pack S (fun p => log p) hd0
      (hdlog.trans hfull) (fun p hp => ⟨(hS p hp).1.log_pos.le, (hS p hp).2.2.1⟩)
  have hA : ∀ p ∈ A, p.Prime ∧ p ≤ b.Q ∧ b.k.factorization p = J - 1 := by
    intro p hp
    obtain ⟨hpp, hpQ, hpl, hpval, hpm, hpmgap⟩ := hS p (hAS hp)
    exact ⟨hpp, hpQ, hpval⟩
  let k := b.k * ∏ p ∈ A, p
  obtain ⟨hk2, hkprefix, hlogk, hkf, hcost⟩ :=
    ActualHigherLayerBudgetRepair.insert_roster (show 4 < X by linarith) hb' hJ A hA
  have hslack : X - log (k : ℝ) = b.δ - ∑ p ∈ A, log p := by
    change log (k : ℝ) - log (b.k : ℝ) = _ at hlogk
    linarith
  have hmass0 : 0 ≤ ∑ p ∈ A, log p := sum_nonneg (fun p hp => (hA p hp).1.log_pos.le)
  have hR0 : 0 ≤ actualDefect X k - completeFirstLayerLoss X k := by
    rw [hcost]
    apply sum_nonneg
    intro p hp
    exact mul_nonneg (sub_nonneg.mpr (hS p (hAS hp)).2.2.2.2.1.le) (hA p hp).1.log_pos.le
  have hR : actualDefect X k - completeFirstLayerLoss X k ≤
      ((2 / (J : ℝ)) * referencePrice X) * b.δ := by
    rw [hcost]
    calc
      _ ≤ ∑ p ∈ A, ((2 / (J : ℝ)) * referencePrice X) * log p := by
        apply sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_right (hS p (hAS hp)).2.2.2.2.2 (hA p hp).1.log_pos.le
      _ = ((2 / (J : ℝ)) * referencePrice X) * (∑ p ∈ A, log p) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hAd (by positivity)
  have hδ : b.δ ≤ 2 * log X := hdlog.le.trans
    (ActualRecordAllLogBudgetRemainder.log_shell (show 4 < X by linarith)).2.2
  have hR' : actualDefect X k - completeFirstLayerLoss X k ≤
      ((2 / (J : ℝ)) * referencePrice X) * (2 * log X) :=
    hR.trans (mul_le_mul_of_nonneg_left hδ (by positivity))
  have hround : referencePrice X * (X - log (k : ℝ)) ≤
      referencePrice X * (2 * log X / (J : ℝ)) :=
    mul_le_mul_of_nonneg_left (by rw [hslack]; exact hdnew.le) hLambda.le
  have he : ((2 / (J : ℝ)) * referencePrice X) * (2 * log X) +
      referencePrice X * (2 * log X / (J : ℝ)) = 6 / (X * (J : ℝ)) := by
    unfold referencePrice
    field_simp [hX0.ne', hL.ne', hJ0.ne'] <;> ring
  refine ⟨k, A, hAS, hk2, hkprefix, rfl, hkf, hlogk, ?_, ?_, ?_, ?_, hcost, ?_, ?_⟩
  · rw [hlogk]; exact hmass0
  · rw [hlogk]; exact hAd
  · rw [hslack]; exact hdnew0
  · rw [hslack]; exact hdnew
  · exact add_nonneg hR0 (mul_nonneg hLambda.le (by rw [hslack]; exact hdnew0))
  · linarith

/-- Exact arbitrary-price comparison at an actual same-prefix k. The price
term keeps ACTUAL new slack. The theta block keeps ORIGINAL b.delta.
k=m is included by the reused two-price helper's reflexive branch. -/
theorem original_price_exact_slack {X μ : ℝ} (hX : 14 ≤ X) {m k : ℕ}
    (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)
    (hrecord : ∀ a : ℕ, 0 < a → a < m →
      goldenResourceObjective μ a < goldenResourceObjective μ m)
    (hclock : X = log (m : ℝ)) (b : Budget) (hb : b.spec X)
    (hP : (largestPrime m : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (hkprefix : k.primeFactors = Nat.primesLE b.Q)
    (hslack : 0 ≤ X - log (k : ℝ)) :
    k ≤ m ∧ actualDefect X m - completeFirstLayerLoss X m + μ * (X - log (k : ℝ)) ≤
      actualDefect X k - completeFirstLayerLoss X k + referencePrice X * (X - log (k : ℝ)) +
        6 * max (|(largestPrime m : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *
          |b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ))| /
            (X ^ 2 * log (X / 2)) := by
  have htwo := ActualHigherLayerBudgetRepair.two_price_compare hm hk hμ hrecord hclock hslack
  rcases hb with ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0, hdlog, hds,
    hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩
  have hmprefix := (price_record_prime_structure hm hμ hrecord).2
  have hcancel := complete_first_layer_prefix_cancellation (show 4 < X by linarith)
    hm hk hmprefix hkprefix hP hQ hr hroot
  have hlogb : log (b.k : ℝ) = b.h + Chebyshev.theta (b.Q : ℝ) := by
    rw [hbdef, Nat.cast_mul,
      log_mul (by exact_mod_cast (higher_core_pos (strictInteger (referencePrice X))).ne')
        (by exact_mod_cast (prefix_integer_pos b.Q).ne'), prefix_integer_log, ← hhdef]
  have hmass : Chebyshev.theta (largestPrime m : ℝ) - Chebyshev.theta (b.Q : ℝ) =
      b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ)) := by
    rw [hlogb] at hbudget
    linarith
  rw [hmass] at hcancel
  have horient := (le_abs_self (completeFirstLayerLoss X k - completeFirstLayerLoss X m)).trans hcancel
  exact ⟨htwo.1, by nlinarith [htwo.2]⟩

/-- Finite rate conversion with the literal growing index, not eta chosen
as a function of X in the fixed-J theorem. -/
theorem growing_layer_cost_conversion {X A0 : ℝ} (hX : 1 < X)
    (hA : 0 < A0) (hloglog : 0 < log (log X))
    (hlarge : 6 ≤ log X / (A0 * log (log X)) ^ 10) :
    6 / (X * (⌊log X / (A0 * log (log X)) ^ 10⌋₊ : ℝ)) ≤
      (12 * A0 ^ 10) * log (log X) ^ 10 / (X * log X) := by
  have hL := log_pos hX
  have hM0 : 0 < (A0 * log (log X)) ^ 10 := pow_pos (mul_pos hA hloglog) _
  have hrat : 0 ≤ log X / (A0 * log (log X)) ^ 10 := (div_pos hL hM0).le
  have herr := Nat.lt_floor_add_one (log X / (A0 * log (log X)) ^ 10)
  have hj : 0 < (⌊log X / (A0 * log (log X)) ^ 10⌋₊ : ℝ) := by linarith
  have hhalf : log X / (2 * (A0 * log (log X)) ^ 10) ≤
      (⌊log X / (A0 * log (log X)) ^ 10⌋₊ : ℝ) := by
    have he : log X / (2 * (A0 * log (log X)) ^ 10) =
        (log X / (A0 * log (log X)) ^ 10) / 2 := by ring
    rw [he]; linarith
  have hprod : log X ≤
      (⌊log X / (A0 * log (log X)) ^ 10⌋₊ : ℝ) * (2 * (A0 * log (log X)) ^ 10) :=
    (div_le_iff₀ (by positivity : 0 < 2 * (A0 * log (log X)) ^ 10)).mp hhalf
  apply (div_le_div_iff₀ (mul_pos (by linarith : 0 < X) hj)
    (mul_pos (by linarith : 0 < X) hL)).mpr
  rw [mul_pow] at hprod ⊢
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 6 * X by positivity)
  nlinarith

private theorem root_exists_for_index {X : ℝ} (hX : 1 < X) (hL : 4 ≤ log X)
    {j : ℕ} (hj : 3 ≤ j) (hjL : (j : ℝ) ≤ log X) :
    ∃ ρ : ℝ, 2 < ρ ∧ beta j ρ = referencePrice X := by
  have hX0 : 0 < X := by linarith
  have hLambda := reference_price_pos hX
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlog2' : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h2pow : (2 : ℝ) ^ j ≤ X := by
    apply (log_le_log_iff (pow_pos (by norm_num) j) hX0).mp
    rw [log_pow]
    nlinarith
  have hden : 2 * (2 : ℝ) ^ j * log 2 < X * log X := by
    have hh := mul_le_mul_of_nonneg_right h2pow (show 0 ≤ 2 * log 2 by positivity)
    have hm := mul_lt_mul_of_pos_left (show 2 * log 2 < log X by linarith) hX0
    nlinarith
  have hactive : referencePrice X < beta j 2 := by
    have h1 : 1 / (X * log X) < 1 / (2 * (2 : ℝ) ^ j * log 2) :=
      one_div_lt_one_div_of_lt (by positivity) hden
    exact h1.trans_le (beta_uniform_bounds (by norm_num : (2 : ℝ) ≤ 2) (by omega : 1 ≤ j)).1
  obtain ⟨v, hv, hsmall⟩ := beta_small_endpoint (show 1 ≤ j by omega) hLambda
  obtain ⟨ρ, hρ, hroot⟩ := intermediate_value_Icc' hv
    ((beta_continuousOn (show 1 ≤ j by omega)).mono (fun t ht => ht.1))
    ⟨hsmall.le, hactive.le⟩
  have hρgt : 2 < ρ := by
    have hne : 2 ≠ ρ := by intro he; rw [← he] at hroot; linarith
    exact lt_of_le_of_ne hρ.1 hne
  exact ⟨ρ, hρgt, hroot⟩

private theorem tenth_scale_large {A0 l : ℝ} (hA : 1 ≤ A0) (hl : 2 ≤ l) :
    2 ≤ (A0 * l) ^ 10 ∧ 6 * l ≤ (A0 * l) ^ 10 / 2 := by
  have hl0 : 0 ≤ l := by linarith
  have hbase : l ≤ A0 * l := by nlinarith
  have hpow := pow_le_pow_left₀ hl0 hbase 10
  have h9 : (2 : ℝ) ^ 9 ≤ l ^ 9 := pow_le_pow_left₀ (by norm_num) hl 9
  have hm := mul_le_mul_of_nonneg_right h9 hl0
  have he : l ^ 9 * l = l ^ 10 := by ring
  rw [he] at hm
  norm_num at hm
  constructor <;> nlinarith

set_option maxHeartbeats 4000000 in
private theorem eventual_growing_roster : ∃ A0 : ℝ, 1 ≤ A0 ∧
    ∀ᶠ X : ℝ in atTop, 14 ≤ X ∧ 0 < log (log X) ∧
      6 ≤ log X / (A0 * log (log X)) ^ 10 ∧
      let J := ⌊log X / (A0 * log (log X)) ^ 10⌋₊
      ∃ S : Finset ℕ, 3 ≤ J ∧ log (2 * X) < ∑ p ∈ S, log p ∧
        ∀ p ∈ S, p.Prime ∧ (p : ℝ) < X / 2 ∧
          log p ≤ 2 * log X / (J : ℝ) ∧
          goldenLayerMarginal p J < referencePrice X ∧
          referencePrice X - goldenLayerMarginal p J ≤ (2 / (J : ℝ)) * referencePrice X ∧
          referencePrice X < goldenLayerMarginal p (J - 1) := by
  classical
  obtain ⟨c, A, Y0, hc, hA, hY, hroster⟩ := quantitative_moving_prime_roster
  let A0 := max 1 (12 / c)
  have hA0 : 1 ≤ A0 := le_max_left _ _
  have hA00 : 0 < A0 := by linarith
  have hcA0 : 12 ≤ c * A0 := by
    have h := le_max_right (1 : ℝ) (12 / c)
    change 12 / c ≤ A0 at h
    have hh := (div_le_iff₀ hc).mp h
    nlinarith
  have hratio : Tendsto (fun X : ℝ => (A0 * log (log X)) ^ 10 / log X) atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_rpow_atTop (10 : ℝ)
      (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp tendsto_log_atTop
    simp only [rpow_natCast, rpow_one, Function.comp_def] at h
    have hpow (x : ℝ) : x ^ (10 : ℝ) = x ^ (10 : ℕ) := by
      convert Real.rpow_natCast x 10 using 1 <;> norm_num
    have hh : Tendsto (fun X : ℝ => A0 ^ 10 * (log (log X) ^ 10 / log X)) atTop (𝓝 0) := by
      simpa only [hpow, mul_zero] using h.const_mul (A0 ^ 10)
    apply hh.congr'
    filter_upwards [] with X
    rw [mul_pow]
    ring
  have hsmall := hratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 6)
  have hloglog := tendsto_log_atTop.comp tendsto_log_atTop
  refine ⟨A0, hA0, ?_⟩
  filter_upwards [eventually_ge_atTop (14 : ℝ),
    tendsto_log_atTop.eventually_ge_atTop (max 4 (6 * A)),
    hloglog.eventually_ge_atTop (max 2 (log Y0 / 6)), hsmall] with X hX hLX hlX hsmallX
  let L := log X
  let l := log L
  let M := (A0 * l) ^ 10
  let J := ⌊L / M⌋₊
  have hL4 : 4 ≤ L := (le_max_left _ _).trans hLX
  have hLA : 6 * A ≤ L := (le_max_right _ _).trans hLX
  have hl2 : 2 ≤ l := (le_max_left _ _).trans hlX
  have hlY : log Y0 / 6 ≤ l := (le_max_right _ _).trans hlX
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < L := by linarith
  have hl0 : 0 < l := by linarith
  have hM := tenth_scale_large hA0 hl2
  have hM0 : 0 < M := by dsimp only [M]; linarith [hM.1]
  have hML : M / L < 1 / 6 := hsmallX
  have hlarge : 6 ≤ L / M := by
    have hh := (div_lt_iff₀ hL0).mp hML
    apply (le_div_iff₀ hM0).mpr
    nlinarith
  have hfloor := growing_layer_floor_bounds hL0 (show 1 ≤ M by linarith [hM.1]) hlarge
  have hJ : 3 ≤ J := hfloor.1
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  obtain ⟨ρ, hρ, hroot⟩ := root_exists_for_index hX1 hL4 hJ hfloor.2.2.2
  have hg := uniform_root_geometry hJ hX1 hL4 hM.1 hρ.le hroot
    hfloor.2.1 hfloor.2.2.1
  obtain ⟨hpowlo, hpowhi, hloglo, hloghi, hylo, hyhi, hJylo, hJyhi⟩ := hg
  let b := ρ * (1 + 1 / (J : ℝ) ^ 2)
  have hρ0 : 0 < ρ := by linarith
  have hb : ρ ≤ b := by
    have hh := mul_nonneg hρ0.le (one_div_nonneg.mpr (sq_nonneg (J : ℝ)))
    dsimp only [b]
    nlinarith
  have hb0 : 0 < b := hρ0.trans_le hb
  have hlogb : log b = log ρ + log (1 + 1 / (J : ℝ) ^ 2) :=
    log_mul hρ0.ne' (by positivity : 1 + 1 / (J : ℝ) ^ 2 ≠ 0)
  have hlogwidth : log (1 + 1 / (J : ℝ) ^ 2) ≤ 1 / (J : ℝ) ^ 2 := by
    have hh := log_le_sub_one_of_pos (show 0 < 1 + 1 / (J : ℝ) ^ 2 by positivity)
    linarith
  have hJr : (3 : ℝ) ≤ J := by exact_mod_cast hJ
  have hinv : 1 / (J : ℝ) ≤ 1 := (div_le_iff₀ hJ0).mpr (by linarith)
  have hlogL : l ≤ L - 1 := log_le_sub_one_of_pos hL0
  have hz : log b ≤ 2 * L / (J : ℝ) := by
    apply (le_div_iff₀ hJ0).mpr
    rw [hlogb]
    have hh := mul_le_mul_of_nonneg_left hlogwidth hJ0.le
    have he : (J : ℝ) * (1 / (J : ℝ) ^ 2) = 1 / (J : ℝ) := by field_simp [hJ0.ne']
    rw [he] at hh
    nlinarith
  have hzL : log b ≤ L := by
    have hh : 2 * L / (J : ℝ) ≤ L := (div_le_iff₀ hJ0).mpr (by nlinarith)
    exact hz.trans hh
  have hdecay : exp (-c * log ρ ^ (1 / 10 : ℝ)) ≤ 1 / L ^ 6 :=
    root_pnt_suppression hc hA0 (by linarith) hcA0 hylo
  have hy6 : 6 * l ≤ log ρ := hM.2.trans hylo
  have hρlarge : L ^ 6 ≤ ρ := by
    apply (log_le_log_iff (pow_pos hL0 6) hρ0).mp
    rw [log_pow]
    exact hy6
  have hYρ : Y0 ≤ ρ := by
    apply (log_le_log_iff (by linarith : 0 < Y0) hρ0).mp
    linarith
  have hAL : 6 * A ≤ L ^ 4 := by
    have hh : L ≤ L ^ 4 := by
      simpa using pow_le_pow_right₀ (by linarith : 1 ≤ L) (by norm_num : (1 : ℕ) ≤ 4)
    exact hLA.trans hh
  obtain ⟨hmass, S, hcard, hS⟩ := hroster L ρ J hJ hL4 hρ.le hYρ hfloor.2.2.2 hAL
    hρlarge hzL hdecay
  have hlog2 : log 2 ≤ 1 := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hfull : log (2 * X) < ∑ p ∈ S, log p := by
    have hlow : (S.card : ℝ) * log ρ ≤ ∑ p ∈ S, log p := by
      calc
        _ = ∑ p ∈ S, log ρ := by simp
        _ ≤ _ := by
          apply sum_le_sum
          intro p hp
          exact log_le_log hρ0 (hS p hp).2.1.le
    have hcardR : (S.card : ℝ) = 2 * (J : ℝ) + 2 := by exact_mod_cast hcard
    rw [hcardR] at hlow
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne']
    have hy0 : 0 ≤ log ρ := (log_pos (by linarith : 1 < ρ)).le
    nlinarith
  have hbX : b < X / 2 := by
    apply (log_lt_log_iff hb0 (by positivity : 0 < X / 2)).mp
    rw [log_div hX0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have hh : 2 * L / (J : ℝ) ≤ (2 / 3 : ℝ) * L := by
      apply (div_le_iff₀ hJ0).mpr
      have hm := mul_le_mul_of_nonneg_left hJr (show 0 ≤ (2 / 3 : ℝ) * L by positivity)
      nlinarith
    have hh' : (2 / 3 : ℝ) * L < L - log 2 := by linarith
    exact hz.trans_lt (hh.trans_lt hh')
  have hρ4 : 4 ≤ ρ := by
    have h46 : (4 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL4 6
    norm_num at h46
    linarith
  refine ⟨hX, hl0, hlarge, S, hJ, hfull, ?_⟩
  intro p hp
  obtain ⟨hpp, hρp, hpb⟩ := hS p hp
  have hpm := moving_interval_marginals hJ hρ.le (reference_price_pos hX1) hroot hρp hpb
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hnat := beta_nat hpp (show 1 ≤ J by omega)
  have hprevnat := beta_nat hpp (show 1 ≤ J - 1 by omega)
  have hprev : referencePrice X < goldenLayerMarginal p (J - 1) := by
    have hlow : referencePrice X / 3 ≤ beta J (p : ℝ) := by
      have he := add_one_le_exp (-2 / (J : ℝ))
      have hfrac : 2 / (J : ℝ) ≤ 2 / 3 :=
        (div_le_div_iff₀ hJ0 (by norm_num : (0 : ℝ) < 3)).mpr (by linarith)
      have hm := mul_le_mul_of_nonneg_right he (reference_price_pos hX1).le
      have hLambda0 := (reference_price_pos hX1).le
      have hfracLambda := mul_le_mul_of_nonneg_right hfrac hLambda0
      nlinarith [hpm.1]
    have hp4 : (4 : ℝ) < p := hρ4.trans_lt hρp
    have hLambda : 0 < referencePrice X := reference_price_pos hX1
    have hmul : referencePrice X < (p : ℝ) * beta J (p : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ (p : ℝ) by positivity)
      have hpLambda := mul_lt_mul_of_pos_right hp4 hLambda
      nlinarith
    have ha := adjacent_layer_strict (show 2 ≤ J by omega) hp2
    rw [hprevnat] at ha
    exact hmul.trans ha
  refine ⟨hpp, hpb.trans_lt hbX, ?_, ?_, ?_, hprev⟩
  · exact (log_le_log (by exact_mod_cast hpp.pos) hpb).trans hz
  · simpa only [hnat] using hpm.2.1
  · simpa only [hnat] using hpm.2.2.2

/-- A genuinely growing layer repairs the literal Budget. C,X0,A0 precede X
and every Budget; J is the displayed floor, not a fixed-J asymptotic supplier.
The returned identities are for the complete actual loss and every valuation. -/
theorem actual_higher_layer_quantitative_budget_repair :
    ∃ C X0 A0 : ℝ, 0 < C ∧ exp (exp 1) < X0 ∧ 1 ≤ A0 ∧
    ∀ X : ℝ, X0 ≤ X → ∀ b : Budget, b.spec X →
    ∃ k : ℕ, 2 ≤ k ∧ k.primeFactors = Nat.primesLE b.Q ∧
      0 ≤ X - log (k : ℝ) ∧
      0 ≤ log (k : ℝ) - log (b.k : ℝ) ∧
      log (k : ℝ) - log (b.k : ℝ) ≤ b.δ ∧
      log (higherCore k : ℝ) - b.h = log (k : ℝ) - log (b.k : ℝ) ∧
      0 ≤ actualDefect X k - completeFirstLayerLoss X k +
        referencePrice X * (X - log (k : ℝ)) ∧
      actualDefect X k - completeFirstLayerLoss X k +
        referencePrice X * (X - log (k : ℝ)) ≤
          C * log (log X) ^ 10 / (X * log X) ∧
      let J := ⌊log X / (A0 * log (log X)) ^ 10⌋₊
      ∃ A : Finset ℕ, 3 ≤ J ∧
        (∀ p ∈ A, p.Prime ∧ p ≤ b.Q ∧
          b.k.factorization p = J - 1 ∧
          optimalLayerCount (referencePrice X) p = J - 1) ∧
        k = b.k * ∏ p ∈ A, p ∧
        log (k : ℝ) - log (b.k : ℝ) = ∑ p ∈ A, log p ∧
        (∀ p : ℕ, k.factorization p = b.k.factorization p + if p ∈ A then 1 else 0) ∧
        actualDefect X k - completeFirstLayerLoss X k =
          ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p := by
  classical
  obtain ⟨A0, hA0, hevent⟩ := eventual_growing_roster
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  let X0 := max T (max 14 (exp (exp 1) + 1))
  have hA00 : 0 < A0 := by linarith
  refine ⟨12 * A0 ^ 10, X0, A0, by positivity, ?_, hA0, ?_⟩
  · dsimp only [X0]
    have hh := (le_max_right (14 : ℝ) (exp (exp 1) + 1)).trans
      (le_max_right T (max 14 (exp (exp 1) + 1)))
    linarith
  · intro X hX b hb
    have hTX : T ≤ X := (le_max_left _ _).trans hX
    obtain ⟨hX14, hl, hlarge, S, hJ, hfull, hS⟩ := hT X hTX
    let J := ⌊log X / (A0 * log (log X)) ^ 10⌋₊
    have hLambda := reference_price_pos (show 1 < X by linarith)
    rcases hb with ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0, hdlog, hds,
      hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩
    have hb' : b.spec X := ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0, hdlog, hds,
      hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩
    have hexp (p : ℕ) (hp : p ∈ S) :
        b.k.factorization p = J - 1 ∧ optimalLayerCount (referencePrice X) p = J - 1 := by
      obtain ⟨hpp, hpX, hplog, hupp, hgap, hprev⟩ := hS p hp
      have hlo : J - 1 ≤ optimalLayerCount (referencePrice X) p := by
        rw [← strictInteger_counts hLambda]
        exact (strict_layer_iff hLambda hpp (by omega : 1 ≤ J - 1)).mpr hprev
      have hhi : ¬ J ≤ optimalLayerCount (referencePrice X) p := by
        rw [← strictInteger_counts hLambda]
        exact fun hj => hupp.not_ge ((strict_layer_iff hLambda hpp (by omega)).mp hj).le
      have hc : optimalLayerCount (referencePrice X) p = J - 1 := by omega
      have hblo := (hhigher p hpp (J - 1) (by omega)).mpr hlo
      have hbhi : ¬ J ≤ b.k.factorization p :=
        fun hj => hhi ((hhigher p hpp J (by omega)).mp hj)
      exact ⟨by omega, hc⟩
    have hSfinite : ∀ p ∈ S, p.Prime ∧ p ≤ b.Q ∧
        log p ≤ 2 * log X / (J : ℝ) ∧ b.k.factorization p = J - 1 ∧
        goldenLayerMarginal p J < referencePrice X ∧
        referencePrice X - goldenLayerMarginal p J ≤ (2 / (J : ℝ)) * referencePrice X := by
      intro p hp
      obtain ⟨hpp, hpX, hplog, hupp, hgap, hprev⟩ := hS p hp
      have hpQstrict : p < b.Q := by exact_mod_cast (hpX.trans_le hQ.1)
      have hpQ : p ≤ b.Q := hpQstrict.le
      exact ⟨hpp, hpQ, hplog, (hexp p hp).1, hupp, hgap⟩
    obtain ⟨k, A, hAS, hk2, hkp, hkdef, hkf, hlogk, hi0, hi, hs0, hs,
      hcost, hc0, hc⟩ := finite_roster_quantitative_repair hX14 hb' hJ S hfull hSfinite
    have hrate := growing_layer_cost_conversion (show 1 < X by linarith) hA00 hl hlarge
    have hcore : log (higherCore k : ℝ) - b.h = log (k : ℝ) - log (b.k : ℝ) := by
      have hlogb : log (b.k : ℝ) = b.h + Chebyshev.theta (b.Q : ℝ) := by
        rw [hbdef, Nat.cast_mul,
          log_mul (by exact_mod_cast (higher_core_pos (strictInteger (referencePrice X))).ne')
            (by exact_mod_cast (prefix_integer_pos b.Q).ne'), prefix_integer_log, ← hhdef]
      rw [higher_core_log (show 0 < k by omega) hkp, hlogb]
      ring
    refine ⟨k, hk2, hkp, hs0, hi0, hi, hcore, hc0, hc.trans hrate,
      A, hJ, ?_, hkdef, hlogk, hkf, hcost⟩
    intro p hp
    exact ⟨(hSfinite p (hAS hp)).1, (hSfinite p (hAS hp)).2.1,
      (hexp p (hAS hp)).1, (hexp p (hAS hp)).2⟩

/-- One threshold before ALL original records and ALL positive original prices.
The witness retains actual new slack in the price term, with original delta in
the first-layer block. Actual exponents of m have no relation to the repair J. -/
theorem actual_record_quantitative_repaired_prefix_residual :
    ∃ C X0 : ℝ, 0 < C ∧ exp (exp 1) < X0 ∧
    ∀ m : ℕ, 2 ≤ m → ∀ μ : ℝ, 0 < μ →
      (∀ a : ℕ, 0 < a → a < m →
        goldenResourceObjective μ a < goldenResourceObjective μ m) →
      X0 ≤ log (m : ℝ) →
      ∃ (b : Budget) (k : ℕ), b.spec (log (m : ℝ)) ∧ 2 ≤ k ∧ k ≤ m ∧
        k.primeFactors = Nat.primesLE b.Q ∧
        0 ≤ log (m : ℝ) - log (k : ℝ) ∧
        0 ≤ log (k : ℝ) - log (b.k : ℝ) ∧
        log (k : ℝ) - log (b.k : ℝ) ≤ b.δ ∧
        actualDefect (log (m : ℝ)) m - completeFirstLayerLoss (log (m : ℝ)) m +
          μ * (log (m : ℝ) - log (k : ℝ)) ≤
          C * log (log (log (m : ℝ))) ^ 10 / (log (m : ℝ) * log (log (m : ℝ))) +
          6 * max (|(largestPrime m : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *
            |b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ))| /
              ((log (m : ℝ)) ^ 2 * log (log (m : ℝ) / 2)) := by
  classical
  obtain ⟨C, T, A0, hC, hT, hA0, hrepair⟩ := actual_higher_layer_quantitative_budget_repair
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧
    ∀ a : ℕ, 0 < a → a < v.1 →
      goldenResourceObjective v.2 a < goldenResourceObjective v.2 v.1}
  let m : S → ℕ := fun x => x.1.1
  let μ : S → ℝ := fun x => x.1.2
  let X : S → ℝ := fun x => log (m x : ℝ)
  let l : Filter S := comap X atTop
  have hX : Tendsto X l atTop := tendsto_comap
  have hm (x : S) : 2 ≤ m x := x.2.1
  have hμ (x : S) : 0 < μ x := x.2.2.1
  have hrec (x : S) (a : ℕ) : 0 < a → a < m x →
      goldenResourceObjective (μ x) a < goldenResourceObjective (μ x) (m x) := x.2.2.2 a
  have hb := hX.eventually canonical_budget_eventually
  have hbounds := original_record_bounds m μ hm hμ hrec hX
  have hall : ∀ᶠ x in l,
      ∃ (b : Budget) (k : ℕ), b.spec (X x) ∧ 2 ≤ k ∧ k ≤ m x ∧
        k.primeFactors = Nat.primesLE b.Q ∧ 0 ≤ X x - log (k : ℝ) ∧
        0 ≤ log (k : ℝ) - log (b.k : ℝ) ∧
        log (k : ℝ) - log (b.k : ℝ) ≤ b.δ ∧
        actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x) +
          μ x * (X x - log (k : ℝ)) ≤
          C * log (log (X x)) ^ 10 / (X x * log (X x)) +
          6 * max (|(largestPrime (m x) : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *
            |b.h + b.δ - (log (m x : ℝ) - Chebyshev.theta (largestPrime (m x) : ℝ))| /
              ((X x) ^ 2 * log (X x / 2)) := by
    filter_upwards [hb, hbounds, hX.eventually_ge_atTop T,
      hX.eventually_ge_atTop 14] with x hb hbounds hxT hx14
    obtain ⟨b, hb⟩ := hb
    obtain ⟨k, hk, hkp, hs, hi0, hi, hcore, hc0, hc, htel⟩ := hrepair (X x) hxT b hb
    have hcomp := original_price_exact_slack hx14 (hm x) hk (hμ x) (hrec x)
      rfl b hb hbounds.1 hkp hs
    /- The equality k=m is already a literal branch of two_price_compare.
       It gives slack=0 by reflexivity, with no strict-predecessor invocation. -/
    exact ⟨b, k, hb, hk, hcomp.1, hkp, hs, hi0, hi, by linarith [hcomp.2]⟩
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  let X0 := max B (exp (exp 1) + 1)
  refine ⟨C, X0, hC, ?_, ?_⟩
  · have hh : exp (exp 1) + 1 ≤ X0 := le_max_right _ _
    linarith
  · intro n hn price hprice hrecord hlarge
    let x : S := ⟨(n, price), hn, hprice, hrecord⟩
    have hx := hB (log (n : ℝ)) ((le_max_left _ _).trans hlarge) x rfl
    simpa only [X, m, μ] using hx

#print axioms uniform_beta_and_slope
#print axioms adjacent_layer_strict
#print axioms moving_interval_marginals
#print axioms uniform_root_geometry
#print axioms growing_layer_floor_bounds
#print axioms quantitative_theta_error
#print axioms root_pnt_suppression
#print axioms quantitative_moving_prime_roster
#print axioms finite_roster_quantitative_repair
#print axioms original_price_exact_slack
#print axioms growing_layer_cost_conversion
#print axioms actual_higher_layer_quantitative_budget_repair
#print axioms actual_record_quantitative_repaired_prefix_residual
end D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerQuantitativeBudgetRepair
