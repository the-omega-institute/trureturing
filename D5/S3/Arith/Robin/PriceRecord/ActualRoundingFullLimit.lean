/- GID: D5/S3/Arith/Robin/PriceRecord/ActualRoundingFullLimit
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualRoundingFullLimit
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: The normalized actual prime rounding sum converges to twice the square root of two. -/

import D5.S3.Arith.Robin.PriceRecord.ActualRoundingGapEstimates
import D5.S3.Arith.Robin.PriceRecord.PrimeBoundarySecondOrder
import D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
import D5.S3.Arith.Robin.ActualRobinClockCovariance

/-! The prime rounding sum uses the compact profile at the square-root scale.
The crossover at `sqrt 2` splits the profile into a counting term and a
reciprocal-square term. The global gap estimates control both tails. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualRoundingFullLimit

open Finset Filter Real
open scoped Topology Chebyshev
open ActualRobinClockCovariance (g)
open BoundaryPrimePrice ActualRoundingGapEstimates
open QuantitativePrimeAbel (log_deficit_bounds primeCount primeInterval squareSum)

private theorem scaled_gap_chamber_error {L p : ℝ} (hL : 1 < L) (hp : 1 < p)
    (hlo : p ^ (2 : ℕ) < 1 + L * log L)
    (hhi : 1 + L * log L < p ^ (3 : ℕ)) :
    |L * integerGap p (g L) - min (L / p ^ (2 : ℕ)) (1 / 2)| ≤
      L * (((p ^ (2 : ℕ))⁻¹) ^ 2 / (1 - (p ^ (2 : ℕ))⁻¹)) +
        L * ((p ^ (3 : ℕ))⁻¹ / (1 - (p ^ (3 : ℕ))⁻¹)) +
        (1 + log ((1 + L * log L) / p ^ (2 : ℕ)) + |log p - log L / 2|) / log L := by
  have hL0 : 0 < L := by linarith
  have hq : 0 < log L := log_pos hL
  have hp0 : 0 < p := by linarith
  have hlam : 0 < g L := by
    exact div_pos (by norm_num) (mul_pos hL0 hq)
  have hC : cutoff (g L) = 1 + L * log L := by
    simp [cutoff, g]
  have hC0 : 0 < 1 + L * log L := by positivity
  have hCr : (1 + L * log L)⁻¹ < 1 :=
    (inv_lt_one₀ hC0).mpr (by nlinarith [mul_pos hL0 hq])
  have hbase := integer_gap_chamber_error hp hlam
    (by simpa only [hC] using hlo) (by simpa only [hC] using hhi)
  rw [hC] at hbase
  let E : ℝ :=
    (1 + L * log L)⁻¹ / (1 - (1 + L * log L)⁻¹) +
      g L * log ((1 + L * log L) / p ^ (2 : ℕ)) +
      ((p ^ (2 : ℕ))⁻¹) ^ 2 / (1 - (p ^ (2 : ℕ))⁻¹) +
      (p ^ (3 : ℕ))⁻¹ / (1 - (p ^ (3 : ℕ))⁻¹)
  have hmin : L * min ((p ^ (2 : ℕ))⁻¹) (g L * log p) =
      min (L / p ^ (2 : ℕ)) (log p / log L) := by
    rw [mul_min_of_nonneg _ _ hL0.le]
    rw [show L * (p ^ (2 : ℕ))⁻¹ = L / p ^ (2 : ℕ) from (div_eq_mul_inv _ _).symm]
    congr 1
    dsimp [g]
    field_simp [hL0.ne', hq.ne']
  have hscaled : |L * integerGap p (g L) -
      min (L / p ^ (2 : ℕ)) (log p / log L)| ≤ L * E := by
    calc
      _ = |L * (integerGap p (g L) -
          min ((p ^ (2 : ℕ))⁻¹) (g L * log p))| := by
        rw [mul_sub, hmin]
      _ = L * |integerGap p (g L) -
          min ((p ^ (2 : ℕ))⁻¹) (g L * log p)| := by
        rw [abs_mul, abs_of_pos hL0]
      _ ≤ _ := mul_le_mul_of_nonneg_left hbase hL0.le
  have hprofile :
      |min (L / p ^ (2 : ℕ)) (log p / log L) - min (L / p ^ (2 : ℕ)) (1 / 2)| ≤
        |log p - log L / 2| / log L := by
    have hm := abs_min_sub_min_le_max (L / p ^ (2 : ℕ)) (log p / log L)
      (L / p ^ (2 : ℕ)) (1 / 2)
    simp only [sub_self, abs_zero] at hm
    rw [max_eq_right (abs_nonneg (log p / log L - 1 / 2))] at hm
    have heq : log p / log L - 1 / 2 = (log p - log L / 2) / log L := by
      field_simp [hq.ne']
    rwa [heq, abs_div, abs_of_pos hq] at hm
  have hodds : L * ((1 + L * log L)⁻¹ / (1 - (1 + L * log L)⁻¹)) = 1 / log L := by
    field_simp [hC0.ne', hq.ne', hL0.ne', show 1 - (1 + L * log L)⁻¹ ≠ 0 by linarith]
    <;> ring
  have hlinear : L * (g L * log ((1 + L * log L) / p ^ (2 : ℕ))) =
      log ((1 + L * log L) / p ^ (2 : ℕ)) / log L := by
    dsimp [g]
    field_simp [hL0.ne', hq.ne']
  calc
    _ ≤ |L * integerGap p (g L) - min (L / p ^ (2 : ℕ)) (log p / log L)| +
        |min (L / p ^ (2 : ℕ)) (log p / log L) - min (L / p ^ (2 : ℕ)) (1 / 2)| :=
      abs_sub_le _ _ _
    _ ≤ L * E + |log p - log L / 2| / log L := add_le_add hscaled hprofile
    _ = _ := by
      dsimp only [E]
      rw [mul_add, mul_add, mul_add, hodds, hlinear]
      ring

/-- The explicit majorant (7), with the literal cutoff inside its logarithm. -/
private def compactError (eps M L : ℝ) : ℝ :=
  2 / (eps ^ (4 : ℕ) * L) + 2 / (eps ^ (3 : ℕ) * sqrt L) +
    (1 + log ((1 + L * log L) / L) +
      3 * max (|log eps|) (|log M|)) / log L

private lemma cutoff_div_clock {L : ℝ} (hL : 0 < L) :
    (1 + L * log L) / L = log L + 1 / L := by
  field_simp [hL.ne']
  <;> ring

private lemma cutoff_div_clock_atTop :
    Tendsto (fun L : ℝ => (1 + L * log L) / L) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [cutoff_div_clock hL]
  exact le_add_of_nonneg_right (div_nonneg (by norm_num) hL.le)

private lemma cutoff_div_clock_sqrt_zero :
    Tendsto (fun L : ℝ => (1 + L * log L) / (L * sqrt L)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun L : ℝ => log L / sqrt L) atTop (𝓝 0) := by
    simpa only [sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hi : Tendsto (fun L : ℝ => 1 / L) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id
  have hs : Tendsto (fun L : ℝ => 1 / sqrt L) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_sqrt_atTop
  have h := hlog.add (hi.mul hs)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hs0 : sqrt L ≠ 0 := (sqrt_pos.mpr hL).ne'
  field_simp [hL.ne', hs0]
  <;> ring

private lemma eventual_compact_chamber {eps M : ℝ} (heps : 0 < eps)
    (hM : eps < M) :
    ∀ᶠ L : ℝ in atTop, 1 < L ∧ ∀ p : ℝ,
      eps * sqrt L ≤ p → p ≤ M * sqrt L →
        2 ≤ p ∧ p ^ (2 : ℕ) < 1 + L * log L ∧
          1 + L * log L < p ^ (3 : ℕ) := by
  have heps3 : (0 : ℝ) < eps ^ (3 : ℕ) := pow_pos heps _
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    cutoff_div_clock_atTop.eventually_gt_atTop (M ^ (2 : ℕ)),
    cutoff_div_clock_sqrt_zero.eventually_lt_const heps3,
    (tendsto_sqrt_atTop.const_mul_atTop heps).eventually_ge_atTop 2]
    with L hL hClo hChi htwo
  have hL0 : 0 < L := by linarith
  have hs : 0 < sqrt L := sqrt_pos.mpr hL0
  have hs2 : (sqrt L) ^ (2 : ℕ) = L := sq_sqrt hL0.le
  have hs3 : (sqrt L) ^ (3 : ℕ) = L * sqrt L := by
    rw [pow_succ, hs2]
  refine ⟨hL, ?_⟩
  intro p hlo hhi
  have hp0 : 0 ≤ p := (mul_pos heps hs).le.trans hlo
  have hM0 : 0 < M := heps.trans hM
  refine ⟨htwo.trans hlo, ?_, ?_⟩
  · have hp2 : p ^ (2 : ℕ) ≤ M ^ (2 : ℕ) * L := by
      calc
        _ ≤ (M * sqrt L) ^ (2 : ℕ) := by gcongr
        _ = _ := by rw [mul_pow, hs2]
    exact hp2.trans_lt ((lt_div_iff₀ hL0).mp hClo)
  · have hp3 : eps ^ (3 : ℕ) * (L * sqrt L) ≤ p ^ (3 : ℕ) := by
      calc
        _ = (eps * sqrt L) ^ (3 : ℕ) := by rw [mul_pow, hs3]
        _ ≤ _ := by gcongr
    exact ((div_lt_iff₀ (mul_pos hL0 hs)).mp hChi).trans_le hp3

private lemma finite_compact_majorant {eps M L p : ℝ}
    (heps : 0 < eps) (hM : eps < M) (hL : 1 < L) (hp : 2 ≤ p)
    (hlo : eps * sqrt L ≤ p) (hhi : p ≤ M * sqrt L)
    (hClo : p ^ (2 : ℕ) < 1 + L * log L)
    (hChi : 1 + L * log L < p ^ (3 : ℕ)) :
    |L * integerGap p (g L) - min (L / p ^ (2 : ℕ)) (1 / 2)| ≤
      compactError eps M L := by
  have hL0 : 0 < L := by linarith
  have hs : 0 < sqrt L := sqrt_pos.mpr hL0
  have hq : 0 < log L := log_pos hL
  have hp0 : 0 < p := by linarith
  have hM0 : 0 < M := heps.trans hM
  have hs2 : (sqrt L) ^ (2 : ℕ) = L := sq_sqrt hL0.le
  have hs3 : (sqrt L) ^ (3 : ℕ) = L * sqrt L := by rw [pow_succ, hs2]
  have hs4 : (sqrt L) ^ (4 : ℕ) = L ^ (2 : ℕ) := by
    calc
      _ = ((sqrt L) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = _ := by rw [hs2]
  let u : ℝ := (p ^ (2 : ℕ))⁻¹
  let v : ℝ := (p ^ (3 : ℕ))⁻¹
  have hv0 : 0 ≤ v := (inv_pos.mpr (pow_pos hp0 _)).le
  have hu : u ≤ 1 / 2 := by
    have hp2 : (2 : ℝ) ^ (2 : ℕ) ≤ p ^ (2 : ℕ) := by gcongr
    have hi := (inv_le_inv₀ (pow_pos hp0 2) (by norm_num : (0 : ℝ) < 2)).mpr
      (show (2 : ℝ) ≤ p ^ (2 : ℕ) by norm_num at hp2; linarith)
    norm_num at hi
    exact hi
  have hv : v ≤ 1 / 2 := by
    have hp3 : (2 : ℝ) ^ (3 : ℕ) ≤ p ^ (3 : ℕ) := by gcongr
    have hi := (inv_le_inv₀ (pow_pos hp0 3) (by norm_num : (0 : ℝ) < 2)).mpr
      (show (2 : ℝ) ≤ p ^ (3 : ℕ) by norm_num at hp3; linarith)
    norm_num at hi
    exact hi
  have hdu : 0 < 1 - u := by linarith
  have hdv : 0 < 1 - v := by linarith
  have hdu2 : 1 / (1 - u) ≤ 2 := (div_le_iff₀ hdu).mpr (by linarith)
  have hdv2 : 1 / (1 - v) ≤ 2 := (div_le_iff₀ hdv).mpr (by linarith)
  have hp4 : eps ^ (4 : ℕ) * L ^ (2 : ℕ) ≤ p ^ (4 : ℕ) := by
    calc
      _ = (eps * sqrt L) ^ (4 : ℕ) := by rw [mul_pow, hs4]
      _ ≤ _ := by gcongr
  have hp3 : eps ^ (3 : ℕ) * (L * sqrt L) ≤ p ^ (3 : ℕ) := by
    calc
      _ = (eps * sqrt L) ^ (3 : ℕ) := by rw [mul_pow, hs3]
      _ ≤ _ := by gcongr
  have hfour : L * u ^ (2 : ℕ) ≤ 1 / (eps ^ (4 : ℕ) * L) := by
    calc
      _ = L / p ^ (4 : ℕ) := by
        dsimp [u]
        field_simp [hp0.ne']
        <;> ring
      _ ≤ L / (eps ^ (4 : ℕ) * L ^ (2 : ℕ)) :=
        div_le_div_of_nonneg_left hL0.le (by positivity) hp4
      _ = _ := by
        field_simp [heps.ne', hL0.ne']
        <;> ring
  have hthree : L * v ≤ 1 / (eps ^ (3 : ℕ) * sqrt L) := by
    calc
      _ = L / p ^ (3 : ℕ) := by simp only [v, div_eq_mul_inv]
      _ ≤ L / (eps ^ (3 : ℕ) * (L * sqrt L)) :=
        div_le_div_of_nonneg_left hL0.le (by positivity) hp3
      _ = _ := by
        field_simp [heps.ne', hL0.ne', hs.ne']
        <;> ring
  have hterm2 : L * (u ^ (2 : ℕ) / (1 - u)) ≤ 2 / (eps ^ (4 : ℕ) * L) := by
    calc
      _ = (L * u ^ (2 : ℕ)) * (1 / (1 - u)) := by ring
      _ ≤ (L * u ^ (2 : ℕ)) * 2 :=
        mul_le_mul_of_nonneg_left hdu2 (mul_nonneg hL0.le (sq_nonneg u))
      _ ≤ (1 / (eps ^ (4 : ℕ) * L)) * 2 :=
        mul_le_mul_of_nonneg_right hfour (by norm_num)
      _ = _ := by ring
  have hterm3 : L * (v / (1 - v)) ≤ 2 / (eps ^ (3 : ℕ) * sqrt L) := by
    calc
      _ = (L * v) * (1 / (1 - v)) := by ring
      _ ≤ (L * v) * 2 := mul_le_mul_of_nonneg_left hdv2 (mul_nonneg hL0.le hv0)
      _ ≤ (1 / (eps ^ (3 : ℕ) * sqrt L)) * 2 :=
        mul_le_mul_of_nonneg_right hthree (by norm_num)
      _ = _ := by ring
  let x : ℝ := p / sqrt L
  let B : ℝ := max (|log eps|) (|log M|)
  have hxl : eps ≤ x := (le_div_iff₀ hs).mpr hlo
  have hxu : x ≤ M := (div_le_iff₀ hs).mpr hhi
  have hx0 : 0 < x := heps.trans_le hxl
  have hlogx : log x = log p - log L / 2 := by
    dsimp [x]
    rw [log_div hp0.ne' hs.ne', log_sqrt hL0.le]
  have hxB : |log x| ≤ B := by
    apply abs_le.mpr
    constructor
    · calc
        -B ≤ -|log eps| := neg_le_neg (le_max_left _ _)
        _ ≤ log eps := neg_abs_le _
        _ ≤ log x := log_le_log heps hxl
    · calc
        log x ≤ log M := log_le_log hx0 hxu
        _ ≤ |log M| := le_abs_self _
        _ ≤ B := le_max_right _ _
  have hC0 : 0 < 1 + L * log L := by positivity
  have hlogC : log ((1 + L * log L) / p ^ (2 : ℕ)) =
      log ((1 + L * log L) / L) - 2 * log x := by
    rw [log_div hC0.ne' (pow_pos hp0 2).ne', log_div hC0.ne' hL0.ne',
      log_pow, hlogx]
    norm_num
    <;> ring
  have hnum : 1 + log ((1 + L * log L) / p ^ (2 : ℕ)) +
      |log p - log L / 2| ≤ 1 + log ((1 + L * log L) / L) + 3 * B := by
    rw [hlogC, ← hlogx]
    linarith [(abs_le.mp hxB).1]
  have htermLog := div_le_div_of_nonneg_right hnum hq.le
  have hbase := scaled_gap_chamber_error hL (by linarith : 1 < p) hClo hChi
  exact hbase.trans (by
    change L * (u ^ (2 : ℕ) / (1 - u)) + L * (v / (1 - v)) + _ ≤ _
    exact add_le_add (add_le_add hterm2 hterm3) htermLog)

private lemma log_cutoff_ratio_zero :
    Tendsto (fun L : ℝ => log ((1 + L * log L) / L) / log L) atTop (𝓝 0) := by
  have hi : Tendsto (fun L : ℝ => 1 / log L) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_log_atTop
  have hloglog : Tendsto (fun L : ℝ => log (log L) / log L) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_log_atTop
  have hupper : Tendsto (fun L : ℝ => (log 2 + log (log L)) / log L)
      atTop (𝓝 0) := by
    have h := (hi.const_mul (log 2)).add hloglog
    simpa only [mul_zero, zero_add, mul_one_div, add_div] using h
  have hb : ∀ᶠ L : ℝ in atTop,
      0 ≤ log ((1 + L * log L) / L) / log L ∧
      log ((1 + L * log L) / L) / log L ≤ (log 2 + log (log L)) / log L := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      tendsto_log_atTop.eventually_ge_atTop 1] with L hL hq
    have hL0 : 0 < L := by linarith
    have hq0 : 0 < log L := by linarith
    have hi0 : 0 ≤ 1 / L := by positivity
    have hi1 : 1 / L ≤ (1 : ℝ) := (div_le_iff₀ hL0).mpr (by linarith)
    have harg : 1 ≤ log L + 1 / L := by linarith
    have harg0 : 0 < log L + 1 / L := by linarith
    have harg2 : log L + 1 / L ≤ 2 * log L := by linarith
    rw [cutoff_div_clock hL0]
    refine ⟨div_nonneg (log_nonneg harg) hq0.le, ?_⟩
    apply div_le_div_of_nonneg_right _ hq0.le
    calc
      log (log L + 1 / L) ≤ log (2 * log L) := log_le_log harg0 harg2
      _ = _ := log_mul (by norm_num) hq0.ne'
  exact squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2) hupper

/-- The displayed majorant tends to zero by genuine log/sqrt limits. -/
private theorem compactError_tendsto_zero {eps M : ℝ} (heps : 0 < eps) :
    Tendsto (compactError eps M) atTop (𝓝 0) := by
  have hfour : Tendsto (fun L : ℝ => 2 / (eps ^ (4 : ℕ) * L)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (2 : ℝ))).div_atTop
      (tendsto_id.const_mul_atTop (pow_pos heps 4))
  have hthree : Tendsto (fun L : ℝ => 2 / (eps ^ (3 : ℕ) * sqrt L)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (2 : ℝ))).div_atTop
      (tendsto_sqrt_atTop.const_mul_atTop (pow_pos heps 3))
  have hconst : Tendsto (fun L : ℝ =>
      (1 + 3 * max (|log eps|) (|log M|)) / log L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have h := (hfour.add hthree).add (hconst.add log_cutoff_ratio_zero)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with L
  dsimp [compactError]
  ring

/-- One threshold works for every real p in the whole rescaled interval. -/
private theorem eventual_compact_gap_majorant {eps M : ℝ} (heps : 0 < eps) (hM : eps < M) :
    ∀ᶠ L : ℝ in atTop, ∀ p : ℝ,
      eps * sqrt L ≤ p → p ≤ M * sqrt L →
      |L * integerGap p (g L) - min (L / p ^ (2 : ℕ)) (1 / 2)| ≤
        compactError eps M L := by
  filter_upwards [eventual_compact_chamber heps hM] with L hL
  intro p hlo hhi
  obtain ⟨hp, hClo, hChi⟩ := hL.2 p hlo hhi
  exact finite_compact_majorant heps hM hL.1 hp hlo hhi hClo hChi

private lemma price_pos {L : ℝ} (hL : 1 < L) : 0 < g L :=
  div_pos (by norm_num) (mul_pos (by linarith) (log_pos hL))

/-- The factor two comes from log(c*sqrt(L))/log(L) -> 1/2. -/
private theorem prime_count_sqrt_scale {c : ℝ} (hc : 0 < c) :
    Tendsto (fun L : ℝ =>
      primeCount (c * sqrt L) * log L / sqrt L)
      atTop (𝓝 (2 * c)) := by
  have hcount := PrimeBoundarySecondOrder.pi_normalized.comp (tendsto_sqrt_atTop.const_mul_atTop hc)
  have hratio := (tendsto_const_nhds (x := c)).div
    (EulerLayerRootCorrection.log_sqrt_scale hc) (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have h := hcount.mul hratio
  have hlimit : (1 : ℝ) * (c / (1 / 2)) = 2 * c := by ring
  rw [hlimit] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_sqrt_atTop.const_mul_atTop hc).eventually (eventually_gt_atTop (1 : ℝ))]
    with L hL1 hcs
  have hs : 0 < sqrt L := sqrt_pos.mpr (by linarith)
  have hq : log L ≠ 0 := (log_pos hL1).ne'
  have hcq : log (c * sqrt L) ≠ 0 := (log_pos hcs).ne'
  change log (c * sqrt L) * primeCount (c * sqrt L) / (c * sqrt L) *
      (c / (log (c * sqrt L) / log L)) = _
  field_simp [hc.ne', hs.ne', hq, hcq]

private lemma primeInterval_eq_sdiff (y z : ℝ) :
    primeInterval y z = Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
  ext p
  by_cases hp : p.Prime <;>
    simp [primeInterval, Nat.mem_primesLE, hp, not_le, and_comm]

private lemma primeInterval_card {y z : ℝ} (hyz : y ≤ z) :
    ((primeInterval y z).card : ℝ) =
      primeCount z - primeCount y := by
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊z⌋₊ := by
    intro p hp
    obtain ⟨hpy, hpP⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpy.trans (Nat.floor_mono hyz), hpP⟩
  rw [primeCount, primeCount, primeInterval_eq_sdiff, card_sdiff_of_subset hsub,
    Nat.cast_sub (card_le_card hsub),
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]

/-- Actual finite prime shells, with no assumed measure convergence. -/
private theorem prime_interval_count_sqrt_scale {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) :
    Tendsto (fun L : ℝ => ((primeInterval (a * sqrt L) (b * sqrt L)).card : ℝ) *
      log L / sqrt L) atTop (𝓝 (2 * (b - a))) := by
  have h := (prime_count_sqrt_scale hb).sub (prime_count_sqrt_scale ha)
  have heq : 2 * b - 2 * a = 2 * (b - a) := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with L
  rw [primeInterval_card (mul_le_mul_of_nonneg_right hab (sqrt_nonneg L))]
  ring

/-- Every small-prime exponent, however large its floor, obeys this bound. -/
private theorem prime_gap_head_bound {L : ℝ} (hL : 1 < L) (y : ℝ) :
    (∑ p ∈ Nat.primesLE ⌊y⌋₊, integerGap (p : ℝ) (g L)) ≤
      g L * θ y := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE ⌊y⌋₊, g L * log (p : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hpP := (Nat.mem_primesLE.mp hp).2
      exact (integer_gap_global_bounds (by exact_mod_cast hpP.one_lt)
        (price_pos hL)).2.1
    _ = _ := by rw [Chebyshev.theta_eq_sum_primesLE, mul_sum]

/-- In particular the actual small-prime contribution vanishes as eps -> 0,
uniformly in all of its higher integer chambers. -/
private theorem eventual_small_prime_gap_bound {eps eta : ℝ} (heps : 0 < eps) (heta : 0 < eta) :
    ∀ᶠ L : ℝ in atTop,
      sqrt L * log L *
        (∑ p ∈ Nat.primesLE ⌊eps * sqrt L⌋₊, integerGap (p : ℝ) (g L)) <
          eps + eta := by
  have htheta := (EulerLayerRootCorrection.theta_sqrt_scale heps).eventually_lt_const
    (show eps < eps + eta by linarith)
  filter_upwards [htheta, eventually_gt_atTop (1 : ℝ)] with L ht hL
  have hs : 0 < sqrt L := sqrt_pos.mpr (by linarith)
  have hq : 0 < log L := log_pos hL
  have h := mul_le_mul_of_nonneg_left (prime_gap_head_bound hL (eps * sqrt L))
    (mul_nonneg hs.le hq.le)
  have heq : sqrt L * log L * (g L * θ (eps * sqrt L)) =
      θ (eps * sqrt L) / sqrt L := by
    dsimp [g]
    field_simp [hs.ne', hq.ne', show L ≠ 0 by linarith]
    rw [sq_sqrt (show 0 ≤ L by linarith)]
  rw [heq] at h
  exact h.trans_lt ht

/-- An explicit majorant for the entire actual large-prime tail; no chamber
condition or integer-optimality premise is required. -/
private theorem prime_gap_tail_bound {L y z rho : ℝ} (hL : 1 < L) (hy : 1 < y) (hyz : y ≤ z)
    (hrho : 0 ≤ rho)
    (htheta : ∀ t ∈ Set.Icc y z,
      (1 - rho) * t ≤ θ t ∧ θ t ≤ (1 + rho) * t) :
    (∑ p ∈ primeInterval y z, integerGap (p : ℝ) (g L)) ≤
      (1 - (y ^ (2 : ℕ))⁻¹)⁻¹ * ((1 + 3 * rho) / (y * log y)) := by
  have hy0 : 0 < y := by linarith
  have hy2 : 1 < y ^ (2 : ℕ) := one_lt_pow₀ hy (by norm_num)
  have hiy : (y ^ (2 : ℕ))⁻¹ < 1 := (inv_lt_one₀ (pow_pos hy0 _)).mpr hy2
  have hd : 0 < 1 - (y ^ (2 : ℕ))⁻¹ := by linarith
  calc
    _ ≤ ∑ p ∈ primeInterval y z,
        (1 - (y ^ (2 : ℕ))⁻¹)⁻¹ * ((1 : ℝ) / (p : ℝ) ^ 2) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
      have hpy := (mem_Ioc.mp hpI).1
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
      have hp0 : (0 : ℝ) < p := by linarith
      have hyp : y < (p : ℝ) := by
        by_contra! h
        exact (Nat.not_le_of_lt hpy) (Nat.le_floor h)
      have hip : ((p : ℝ) ^ 2)⁻¹ ≤ (y ^ (2 : ℕ))⁻¹ := by
        apply (inv_le_inv₀ (pow_pos hp0 _) (pow_pos hy0 _)).mpr
        nlinarith
      have hp2 : 1 < (p : ℝ) ^ 2 := one_lt_pow₀ hp1 (by norm_num)
      have hu : ((p : ℝ) ^ 2)⁻¹ < 1 := (inv_lt_one₀ (pow_pos hp0 _)).mpr hp2
      have hlog := (log_deficit_bounds (inv_pos.mpr (pow_pos hp0 _)).le hu).2
      have hinv : (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ ≤ (1 - (y ^ (2 : ℕ))⁻¹)⁻¹ :=
        (inv_le_inv₀ (by linarith) hd).mpr (by linarith)
      have hmajor := mul_le_mul_of_nonneg_left hinv
        (inv_nonneg.mpr (sq_nonneg (p : ℝ)))
      have hgap := (integer_gap_global_bounds hp1 (price_pos hL)).2.2
      exact hgap.trans (hlog.trans (by simpa [div_eq_mul_inv, mul_comm] using hmajor))
    _ = (1 - (y ^ (2 : ℕ))⁻¹)⁻¹ *
        (∑ p ∈ primeInterval y z, (1 : ℝ) / (p : ℝ) ^ 2) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (ActualPriceRecordPrimeStructure.finite_theta_abel_upper hy hyz hrho htheta)
      (inv_pos.mpr hd).le

/-- Discharges the finite theta premise from the genuine unconditional PNT.
Thresholds precede all cutoffs and the unrelated free price clock L. -/
private theorem eventual_prime_gap_tail_bound {rho : ℝ} (hrho : 0 < rho) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ L y z : ℝ, 1 < L → Y ≤ y → y ≤ z →
      (∑ p ∈ primeInterval y z, integerGap (p : ℝ) (g L)) ≤
        (1 - (y ^ (2 : ℕ))⁻¹)⁻¹ * ((1 + 3 * rho) / (y * log y)) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (EulerLayerRootCorrection.prime_number_limits.2.eventually
      (Metric.ball_mem_nhds (1 : ℝ) hrho))
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro L y z hL hYy hyz
  have hy : 1 < y := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    ((le_max_right T 2).trans hYy)
  apply prime_gap_tail_bound hL hy hyz hrho.le
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith : 0 < y) ht.1
  have herr : |θ t / t - 1| < rho := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      hT t ((le_max_left T 2).trans (hYy.trans ht.1))
  obtain ⟨hl, hu⟩ := abs_lt.mp herr
  constructor
  · exact (le_div_iff₀ ht0).mp (by linarith : 1 - rho ≤ θ t / t)
  · exact (div_le_iff₀ ht0).mp (by linarith : θ t / t ≤ 1 + rho)

private theorem scaled_log_endpoint {c : ℝ} (hc : 0 < c) :
    Tendsto (fun L : ℝ => sqrt L * log L / (c * sqrt L * log (c * sqrt L)))
      atTop (𝓝 (2 / c)) := by
  have h := ((EulerLayerRootCorrection.log_sqrt_scale hc).inv₀
    (by norm_num : (1 / 2 : ℝ) ≠ 0)).div_const c
  norm_num only [one_div, inv_inv] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_sqrt_atTop.const_mul_atTop hc).eventually (eventually_gt_atTop (1 : ℝ))]
    with L hL hcs
  have hs : sqrt L ≠ 0 := (sqrt_pos.mpr (by linarith : 0 < L)).ne'
  have hq : log L ≠ 0 := (log_pos hL).ne'
  have hcq : log (c * sqrt L) ≠ 0 := (log_pos hcs).ne'
  field_simp
  <;> ring

private theorem scaled_log_endpoint_extra {c : ℝ} (hc : 0 < c)
    (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun L : ℝ =>
      sqrt L * log L / (c * sqrt L * log (c * sqrt L) ^ (n + 1))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun L : ℝ => log (c * sqrt L)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_sqrt_atTop.const_mul_atTop hc)
  have hinv : Tendsto (fun L : ℝ => (log (c * sqrt L))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have h := (scaled_log_endpoint hc).mul (hinv.pow n)
  simp only [zero_pow hn, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_sqrt_atTop.const_mul_atTop hc).eventually (eventually_gt_atTop (1 : ℝ))]
    with L hL hcs
  have hs : sqrt L ≠ 0 := (sqrt_pos.mpr (by linarith : 0 < L)).ne'
  have hcq : log (c * sqrt L) ≠ 0 := (log_pos hcs).ne'
  rw [pow_succ]
  field_simp
  <;> ring

/-- The exact finite prime shell has the endpoint correction 2/a - 2/b.
This supplies the decreasing branch of min(x^-2,1/2) on a compact interval. -/
private theorem prime_square_shell_sqrt_scale {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) :
    Tendsto (fun L : ℝ => sqrt L * log L *
      (∑ p ∈ primeInterval (a * sqrt L) (b * sqrt L), (1 : ℝ) / (p : ℝ) ^ 2))
      atTop (𝓝 (2 * (1 / a - 1 / b))) := by
  obtain ⟨Y, hY, htail⟩ := PrimeSquareTail.prime_square_tail_logarithmic_refinements
  let S : ℝ → ℝ := fun L =>
    squareSum (a * sqrt L) (b * sqrt L)
  let A : ℝ → ℝ := fun L =>
    1 / (a * sqrt L * log (a * sqrt L)) -
      1 / (a * sqrt L * log (a * sqrt L) ^ 2)
  let B : ℝ → ℝ := fun L =>
    1 / (b * sqrt L * log (b * sqrt L)) -
      1 / (b * sqrt L * log (b * sqrt L) ^ 2)
  let R : ℝ → ℝ := fun L => sqrt L * log L * (S L - A L + B L)
  have hbound : ∀ᶠ L : ℝ in atTop, |R L| ≤
      2 * (sqrt L * log L / (a * sqrt L * log (a * sqrt L) ^ 3)) +
        5 * (sqrt L * log L / (a * sqrt L * log (a * sqrt L) ^ 9)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (tendsto_sqrt_atTop.const_mul_atTop ha).eventually (eventually_ge_atTop Y)]
      with L hL hYa
    have hs : 0 ≤ sqrt L * log L := mul_nonneg (sqrt_nonneg _) (log_pos hL).le
    have htail' := (htail (a * sqrt L) (b * sqrt L) hYa
      (mul_le_mul_of_nonneg_right hab (sqrt_nonneg L))).1
    have hmul := mul_le_mul_of_nonneg_left htail' hs
    have hR : |R L| = sqrt L * log L * |S L - A L + B L| := by
      dsimp [R]
      rw [abs_mul, abs_of_nonneg hs]
    rw [hR]
    dsimp [S, A, B, squareSum, primeInterval]
    convert hmul using 1 <;> ring
  have hmajor : Tendsto (fun L : ℝ =>
      2 * (sqrt L * log L / (a * sqrt L * log (a * sqrt L) ^ 3)) +
        5 * (sqrt L * log L / (a * sqrt L * log (a * sqrt L) ^ 9))) atTop (𝓝 0) := by
    convert ((scaled_log_endpoint_extra ha 2 (by norm_num)).const_mul 2).add
      ((scaled_log_endpoint_extra ha 8 (by norm_num)).const_mul 5) using 1 <;> norm_num
  have habs : Tendsto (fun L => |R L|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun L => abs_nonneg (R L))) hbound hmajor
  have hR : Tendsto R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hA : Tendsto (fun L => sqrt L * log L * A L) atTop (𝓝 (2 / a)) := by
    have h := (scaled_log_endpoint ha).sub (scaled_log_endpoint_extra ha 1 (by norm_num))
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [] with L
    dsimp [A]
    ring
  have hB : Tendsto (fun L => sqrt L * log L * B L) atTop (𝓝 (2 / b)) := by
    have h := (scaled_log_endpoint hb).sub (scaled_log_endpoint_extra hb 1 (by norm_num))
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [] with L
    dsimp [B]
    ring
  have h := (hR.add hA).sub hB
  have heq : (0 : ℝ) + 2 / a - 2 / b = 2 * (1 / a - 1 / b) := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with L
  dsimp [R, S, squareSum]
  ring

/-- The exact limiting profile after multiplying the literal gap by `L`. -/
private def profile (L p : ℝ) : ℝ := min (L / p ^ (2 : ℕ)) (1 / 2)

private def tau : ℝ := Real.sqrt 2

private lemma tau_pos : 0 < tau := by
  dsimp [tau]
  positivity

private lemma tau_sq : tau ^ (2 : ℕ) = 2 := by
  dsimp [tau]
  exact sq_sqrt (by norm_num)

private lemma primeInterval_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    primeInterval a c = primeInterval a b ∪ primeInterval b c := by
  classical
  have hfa : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hbc' : ⌊b⌋₊ ≤ ⌊c⌋₊ := Nat.floor_mono hbc
  ext p
  simp only [primeInterval, mem_filter, mem_Ioc, mem_union]
  by_cases hp : p.Prime <;> simp only [hp, and_true]
  · constructor
    · intro h
      by_cases hpb : p ≤ ⌊b⌋₊
      · exact Or.inl ⟨h.1, hpb⟩
      · exact Or.inr ⟨Nat.lt_of_not_ge hpb, h.2⟩
    · intro h
      rcases h with h | h
      · exact ⟨h.1, h.2.trans hbc'⟩
      · exact ⟨lt_of_le_of_lt hfa h.1, h.2⟩
  · simp

private lemma profile_left {L p : ℝ} (hL : 0 < L) (hp : 1 < p)
    (hpc : p ≤ tau * Real.sqrt L) :
    profile L p = 1 / 2 := by
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hp0 : 0 < p := by linarith
  have hp2 : p ^ (2 : ℕ) ≤ (tau * Real.sqrt L) ^ (2 : ℕ) := by
    gcongr
  have hsq : (tau * Real.sqrt L) ^ (2 : ℕ) = 2 * L := by
    rw [mul_pow, tau_sq, Real.sq_sqrt hL.le]
  have hhalf : (1 / 2 : ℝ) ≤ L / p ^ (2 : ℕ) := by
    apply (le_div_iff₀ (pow_pos hp0 2)).2
    nlinarith [hp2, hsq]
  dsimp [profile]
  exact min_eq_right hhalf

private lemma profile_right {L p : ℝ} (hL : 0 < L)
    (hp : tau * Real.sqrt L < (p : ℝ)) :
    profile L p = L / p ^ (2 : ℕ) := by
  have hp0 : 0 < p := by
    have : 0 < tau * Real.sqrt L := mul_pos tau_pos (Real.sqrt_pos.mpr hL)
    linarith
  have hp2 : (tau * Real.sqrt L) ^ (2 : ℕ) < p ^ (2 : ℕ) := by
    gcongr
    all_goals exact mul_nonneg tau_pos.le (sqrt_nonneg L)
  have hsq : (tau * Real.sqrt L) ^ (2 : ℕ) = 2 * L := by
    rw [mul_pow, tau_sq, Real.sq_sqrt hL.le]
  have hhalf : L / p ^ (2 : ℕ) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (pow_pos hp0 2)).2
    nlinarith [hp2, hsq]
  dsimp [profile]
  exact min_eq_left hhalf.le

private lemma profile_shell_split {eps M L : ℝ}
    (heM : tau < M) (hepsτ : eps ≤ tau) (hL : 0 < L) :
    (∑ p ∈ primeInterval (eps * Real.sqrt L) (M * Real.sqrt L),
        profile L (p : ℝ)) =
      (1 / 2 : ℝ) * (primeInterval (eps * Real.sqrt L) (tau * Real.sqrt L)).card +
        L * (∑ p ∈ primeInterval (tau * Real.sqrt L) (M * Real.sqrt L),
          (1 : ℝ) / (p : ℝ) ^ (2 : ℕ)) := by
  classical
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have h₁ : eps * Real.sqrt L ≤ tau * Real.sqrt L :=
    mul_le_mul_of_nonneg_right hepsτ hs
  have h₂ : tau * Real.sqrt L ≤ M * Real.sqrt L :=
    mul_le_mul_of_nonneg_right heM.le hs
  have hu := primeInterval_union h₁ h₂
  have hdis : Disjoint (primeInterval (eps * Real.sqrt L) (tau * Real.sqrt L))
      (primeInterval (tau * Real.sqrt L) (M * Real.sqrt L)) := by
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    exact (Nat.not_lt_of_ge (mem_Ioc.mp (mem_filter.mp hp₁).1).2)
      (mem_Ioc.mp (mem_filter.mp hp₂).1).1
  have hleft : ∀ p ∈ primeInterval (eps * sqrt L) (tau * sqrt L),
      profile L (p : ℝ) = 1 / 2 := by
    intro p hp
    obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
    have hpupper : (p : ℝ) ≤ (⌊tau * sqrt L⌋₊ : ℝ) := by
      exact_mod_cast (mem_Ioc.mp hpI).2
    exact profile_left hL hp1 (hpupper.trans (Nat.floor_le (mul_nonneg tau_pos.le hs)))
  have hright : ∀ p ∈ primeInterval (tau * sqrt L) (M * sqrt L),
      profile L (p : ℝ) = L * (1 / (p : ℝ) ^ (2 : ℕ)) := by
    intro p hp
    have hpgt : tau * sqrt L < (p : ℝ) := by
      by_contra! h
      exact (not_le_of_gt (mem_Ioc.mp (mem_filter.mp hp).1).1) (Nat.le_floor h)
    rw [profile_right hL hpgt, div_eq_mul_inv, one_div]
  rw [hu, sum_union hdis, sum_congr rfl hleft, sum_congr rfl hright,
    sum_const, nsmul_eq_mul, mul_comm (_ : ℝ) (1 / 2), mul_sum]

/-- The profile shell has the exact limit obtained by the two genuine finite
prime suppliers; the split assigns the equality point to the constant branch. -/
private theorem profile_shell_limit {eps M : ℝ} (heps : 0 < eps)
    (hepsτ : eps < tau) (heM : tau < M) :
    Tendsto (fun L : ℝ => log L / sqrt L *
      (∑ p ∈ primeInterval (eps * sqrt L) (M * sqrt L), profile L (p : ℝ)))
      atTop (𝓝 (2 * sqrt 2 - eps - 2 / M)) := by
  have hsq := prime_square_shell_sqrt_scale tau_pos
    (lt_of_lt_of_le tau_pos (le_of_lt heM)) heM.le
  have hsplit : ∀ᶠ L : ℝ in atTop,
      (∑ p ∈ primeInterval (eps * sqrt L) (M * sqrt L), profile L (p : ℝ)) =
        (1 / 2 : ℝ) * (primeInterval (eps * sqrt L) (tau * sqrt L)).card +
          L * (∑ p ∈ primeInterval (tau * sqrt L) (M * sqrt L),
            (1 : ℝ) / (p : ℝ) ^ (2 : ℕ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    exact profile_shell_split heM hepsτ.le hL
  have hcount' : Tendsto (fun L : ℝ =>
      (log L / sqrt L) * ((1 / 2 : ℝ) *
        (primeInterval (eps * sqrt L) (tau * sqrt L)).card)) atTop
      (𝓝 (tau - eps)) := by
    have hc := prime_interval_count_sqrt_scale heps tau_pos hepsτ.le
    have hc' := hc.mul_const (1 / 2 : ℝ)
    have heq : (2 * (tau - eps)) * (1 / 2 : ℝ) = tau - eps := by ring
    rw [heq] at hc'
    apply hc'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
    ring
  have hsq' : Tendsto (fun L : ℝ =>
      log L / sqrt L * (L *
        (∑ p ∈ primeInterval (tau * sqrt L) (M * sqrt L),
          (1 : ℝ) / (p : ℝ) ^ (2 : ℕ)))) atTop (𝓝 (2 * (1 / tau - 1 / M))) := by
    have h := hsq
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hs : 0 < sqrt L := sqrt_pos.mpr hL
    have hs2 : (sqrt L) ^ (2 : ℕ) = L := sq_sqrt hL.le
    have hscale : log L / sqrt L * L = sqrt L * log L := by
      apply (div_mul_eq_mul_div _ _ _).trans
      apply (div_eq_iff hs.ne').mpr
      calc
        log L * L = log L * (sqrt L) ^ 2 := by rw [hs2]
        _ = _ := by ring
    simp only [← mul_assoc, hscale]
  have h := hcount'.add hsq'
  have heq : (tau - eps) + 2 * (1 / tau - 1 / M) =
      2 * sqrt 2 - eps - 2 / M := by
    have hτ : 2 / tau = tau := by
      apply (div_eq_iff tau_pos.ne').mpr
      rw [← pow_two, tau_sq]
    change (tau - eps) + 2 * (1 / tau - 1 / M) = 2 * tau - eps - 2 / M
    calc
      _ = tau - eps + 2 / tau - 2 / M := by ring
      _ = _ := by rw [hτ]; ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [hsplit, eventually_gt_atTop (0 : ℝ)] with L hsplitL hL
  rw [hsplitL]
  ring

private lemma compact_error_sum_bound {eps M : ℝ} (heps : 0 < eps) (heM : eps < M) :
    ∀ᶠ L : ℝ in atTop,
      |(log L / sqrt L) *
        (∑ p ∈ primeInterval (eps * sqrt L) (M * sqrt L),
          (L * integerGap (p : ℝ) (g L) - profile L (p : ℝ)))| ≤
      |((primeInterval (eps * sqrt L) (M * sqrt L)).card : ℝ) * log L / sqrt L| *
        compactError eps M L := by
  filter_upwards [eventual_compact_gap_majorant heps heM,
    eventually_gt_atTop (1 : ℝ)] with L hbound hL
  have hs : 0 < sqrt L := sqrt_pos.mpr (by linarith)
  have hq : 0 < log L := log_pos hL
  let S := primeInterval (eps * sqrt L) (M * sqrt L)
  let a : ℝ := log L / sqrt L
  have ha : 0 ≤ a := div_nonneg hq.le hs.le
  calc
    |a * (∑ p ∈ S, (L * integerGap (p : ℝ) (g L) - profile L (p : ℝ)))| =
        |a| * |∑ p ∈ S, (L * integerGap (p : ℝ) (g L) - profile L (p : ℝ))| := by rw [abs_mul]
    _ ≤ |a| * (∑ p ∈ S, |L * integerGap (p : ℝ) (g L) - profile L (p : ℝ)|) := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ |a| * ((S.card : ℝ) * compactError eps M L) := by
      gcongr
      simp only [← nsmul_eq_mul, ← sum_const]
      apply sum_le_sum
      intro p hp
      have hpI := (mem_filter.mp hp).1
      obtain ⟨hplower, hpupper⟩ := mem_Ioc.mp hpI
      have hplower' : eps * sqrt L < (p : ℝ) := by
        have hfloor : (⌊eps * sqrt L⌋₊ : ℝ) < p := by exact_mod_cast hplower
        exact (Nat.lt_floor_add_one _).trans_le (by
          have : ⌊eps * sqrt L⌋₊ + 1 ≤ p := Nat.succ_le_iff.mpr hplower
          exact_mod_cast this)
      have hpupper' : (p : ℝ) ≤ M * sqrt L := by
        have hfloor : (p : ℝ) ≤ (⌊M * sqrt L⌋₊ : ℝ) := by exact_mod_cast hpupper
        exact hfloor.trans (Nat.floor_le (mul_nonneg (heps.trans heM).le (sqrt_nonneg L)))
      exact hbound (p : ℝ) hplower'.le hpupper'
    _ = |(S.card : ℝ) * log L / sqrt L| * compactError eps M L := by
      have hcard : 0 ≤ (S.card : ℝ) * log L / sqrt L := by positivity
      rw [abs_of_nonneg ha, abs_of_nonneg hcard]
      dsimp [a]
      ring

private lemma compact_error_sum_zero {eps M : ℝ} (heps : 0 < eps) (heM : eps < M) :
    Tendsto (fun L : ℝ => (log L / sqrt L) *
      (∑ p ∈ primeInterval (eps * sqrt L) (M * sqrt L),
        (L * integerGap (p : ℝ) (g L) - profile L (p : ℝ))))
      atTop (𝓝 0) := by
  have hc := prime_interval_count_sqrt_scale heps (heps.trans heM)
    (le_of_lt heM)
  have hcabs : Tendsto (fun L : ℝ =>
      |((primeInterval (eps * sqrt L) (M * sqrt L)).card : ℝ) * log L / sqrt L|)
      atTop (𝓝 |2 * (M - eps)|) := by
    have h := hc.abs
    apply h.congr'
    filter_upwards [] with L
    ring_nf
  have hprod := hcabs.mul (compactError_tendsto_zero heps (M := M))
  have hbound := compact_error_sum_bound heps heM
  have habs : Tendsto (fun L : ℝ => |(log L / sqrt L) *
      (∑ p ∈ primeInterval (eps * sqrt L) (M * sqrt L),
        (L * integerGap (p : ℝ) (g L) - profile L (p : ℝ)))|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun L => abs_nonneg _)) hbound
    simpa using hprod
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

/-- The actual integer gap over a fixed compact shell has the profile limit. -/
private theorem actual_compact_gap_limit {eps M : ℝ} (heps : 0 < eps)
    (hepsτ : eps < tau) (heM : tau < M) :
    Tendsto (fun L : ℝ => sqrt L * log L *
      (∑ p ∈ primeInterval (eps * sqrt L) (M * sqrt L),
        integerGap (p : ℝ) (g L))) atTop
      (𝓝 (2 * sqrt 2 - eps - 2 / M)) := by
  have hp := profile_shell_limit heps hepsτ heM
  have hz := compact_error_sum_zero heps (lt_trans hepsτ heM)
  have h := hp.add hz
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  have hs : 0 < sqrt L := sqrt_pos.mpr (by linarith)
  have hs2 : (sqrt L) ^ (2 : ℕ) = L := sq_sqrt (by linarith)
  symm
  let S := primeInterval (eps * sqrt L) (M * sqrt L)
  let f : ℕ → ℝ := fun p => integerGap (p : ℝ) (g L)
  have hscale : log L / sqrt L * L = sqrt L * log L := by
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hs.ne').mpr
    calc
      log L * L = log L * (sqrt L) ^ 2 := by rw [hs2]
      _ = _ := by ring
  change sqrt L * log L * (∑ p ∈ S, f p) =
    log L / sqrt L * (∑ p ∈ S, profile L (p : ℝ)) +
    log L / sqrt L * (∑ p ∈ S, (L * f p - profile L (p : ℝ)))
  rw [← mul_add, ← sum_add_distrib]
  have hsum : (∑ p ∈ S, (profile L (p : ℝ) + (L * f p - profile L (p : ℝ)))) =
      L * (∑ p ∈ S, f p) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    ring
  rw [hsum, ← mul_assoc, hscale]

private lemma prime_support_partition {eps M L : ℝ}
    (heM : eps ≤ M) (hLM : M * sqrt L ≤ L) :
    (∑ p ∈ Nat.primesLE ⌊L⌋₊, integerGap (p : ℝ) (g L)) =
      (∑ p ∈ Nat.primesLE ⌊eps * sqrt L⌋₊, integerGap (p : ℝ) (g L)) +
      (∑ p ∈ primeInterval (eps * sqrt L) (M * sqrt L),
        integerGap (p : ℝ) (g L)) +
      (∑ p ∈ primeInterval (M * sqrt L) L, integerGap (p : ℝ) (g L)) := by
  have hsub {a b : ℝ} (hab : a ≤ b) :
      Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊b⌋₊ :=
    Nat.primesLE_mono (Nat.floor_mono hab)
  have hsmall := hsub (mul_le_mul_of_nonneg_right heM (sqrt_nonneg L))
  have hlarge := hsub hLM
  rw [primeInterval_eq_sdiff, primeInterval_eq_sdiff]
  rw [add_comm (∑ p ∈ Nat.primesLE ⌊eps * sqrt L⌋₊, _), sum_sdiff hsmall]
  rw [add_comm, sum_sdiff hlarge]

private lemma prime_sum_nonneg {L : ℝ} (hL : 1 < L) {S : Finset ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    0 ≤ ∑ p ∈ S, integerGap (p : ℝ) (g L) := by
  have hlam : 0 < g L := by
    dsimp [g]
    exact div_pos (by norm_num) (mul_pos (by linarith) (log_pos hL))
  apply Finset.sum_nonneg
  intro p hp
  exact (integer_gap_global_bounds (by exact_mod_cast (hprime p hp).one_lt) hlam).1

private lemma large_tail_majorant_limit {M rho : ℝ} (hM : 0 < M) (hrho : 0 ≤ rho) :
    Tendsto (fun L : ℝ => sqrt L * log L *
        ((1 - ((M * sqrt L) ^ (2 : ℕ))⁻¹)⁻¹ *
        ((1 + 3 * rho) / (M * sqrt L * log (M * sqrt L))))) atTop
      (𝓝 (2 * (1 + 3 * rho) / M)) := by
  have hscale := scaled_log_endpoint hM
  have hsqrt : Tendsto (fun L : ℝ => (M * sqrt L) ^ (2 : ℕ)) atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_sqrt_atTop.const_mul_atTop hM)
  have hinv : Tendsto (fun L : ℝ => ((M * sqrt L) ^ (2 : ℕ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hfac : Tendsto (fun L : ℝ =>
      (1 - ((M * sqrt L) ^ (2 : ℕ))⁻¹)⁻¹) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    have h' := h.inv₀ (by norm_num)
    simpa using h'
  have h := hfac.mul (hscale.const_mul (1 + 3 * rho))
  have heq : (1 : ℝ) * ((1 + 3 * rho) * (2 / M)) = 2 * (1 + 3 * rho) / M := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_sqrt_atTop.const_mul_atTop hM).eventually (eventually_gt_atTop (1 : ℝ))]
    with L hL hML
  have hs : 0 < sqrt L := sqrt_pos.mpr (by linarith)
  have hq : 0 < log L := log_pos hL
  have hm : 0 < M * sqrt L := mul_pos hM hs
  field_simp [hs.ne', hM.ne', hq.ne', (log_pos hML).ne']

private lemma eventual_large_tail_bound {M rho eta : ℝ} (hM : 0 < M)
    (hrho : 0 < rho) (heta : 0 < eta) :
    ∀ᶠ L : ℝ in atTop, 1 < L → M * sqrt L ≤ L →
      sqrt L * log L *
        (∑ p ∈ primeInterval (M * sqrt L) L,
          integerGap (p : ℝ) (g L)) <
      2 * (1 + 3 * rho) / M + eta := by
  have hlim := large_tail_majorant_limit hM hrho.le
  have hlt := hlim.eventually_lt_const
    (show 2 * (1 + 3 * rho) / M < 2 * (1 + 3 * rho) / M + eta by linarith)
  obtain ⟨Y, hY, htail⟩ := eventual_prime_gap_tail_bound hrho
  filter_upwards [hlt, (tendsto_sqrt_atTop.const_mul_atTop hM).eventually_ge_atTop Y]
    with L hbound hYL
  intro hL hLM
  have htail' := htail L (M * sqrt L) L hL hYL hLM
  have hbound' := mul_le_mul_of_nonneg_left htail'
    (mul_nonneg (sqrt_nonneg L) (log_pos hL).le)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbound'.trans_lt hbound

/-- The actual-prime sum follows from the compact profile and two tail bounds. -/
theorem actual_prime_gap_limit :
    Tendsto (fun L : ℝ => sqrt L * log L *
      (∑ p ∈ Nat.primesLE ⌊L⌋₊, integerGap (p : ℝ) (g L)))
      atTop (𝓝 (2 * sqrt 2)) := by
  refine Metric.tendsto_nhds.2 ?_
  intro eta heta
  let eps : ℝ := min (sqrt 2 / 4) (eta / 8)
  let M : ℝ := max (2 * sqrt 2) (32 / eta)
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hepsτ : eps < tau := by
    dsimp [eps, tau]
    exact (min_le_left _ _).trans_lt (by linarith [sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)])
  have hM : tau < M := by
    dsimp [M, tau]
    exact lt_of_lt_of_le (by linarith [sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]) (le_max_left _ _)
  have hMpos : 0 < M := tau_pos.trans hM
  have hepsbound : eps ≤ eta / 8 := min_le_right _ _
  have hMbound : 32 ≤ eta * M := by
    simpa only [mul_comm] using (div_le_iff₀ heta).mp (le_max_right (2 * sqrt 2) (32 / eta))
  have htail : 8 / M ≤ eta / 4 := (div_le_iff₀ hMpos).mpr (by nlinarith [hMbound])
  have hshellLower : 2 / M ≤ eta / 16 := (div_le_iff₀ hMpos).mpr (by nlinarith [hMbound])
  have hsmall := eventual_small_prime_gap_bound (eta := eta / 8) heps (by positivity)
  have hlarge := eventual_large_tail_bound (rho := 1) (eta := eta / 8) hMpos
    (by norm_num) (by positivity)
  have hcompact := Metric.tendsto_nhds.1 (actual_compact_gap_limit heps hepsτ hM)
    (eta / 8) (by positivity)
  filter_upwards [hsmall, hlarge, hcompact, eventually_gt_atTop (1 : ℝ),
    tendsto_sqrt_atTop.eventually_ge_atTop M] with L hsmall hlarge hcompact hL hsqrt
  have hs : 0 < sqrt L := sqrt_pos.mpr (by linarith)
  have hMle : M * sqrt L ≤ L := by
    simpa only [← pow_two, sq_sqrt (show 0 ≤ L by linarith)] using
      mul_le_mul_of_nonneg_right hsqrt hs.le
  have hpart := prime_support_partition (hepsτ.le.trans hM.le) hMle
  have hnorm := mul_nonneg hs.le (log_pos hL).le
  have hhead_nonneg := mul_nonneg hnorm (prime_sum_nonneg hL
    (S := Nat.primesLE ⌊eps * sqrt L⌋₊) (fun p hp => (Nat.mem_primesLE.mp hp).2))
  have htail_nonneg := mul_nonneg hnorm (prime_sum_nonneg hL
    (S := primeInterval (M * sqrt L) L) (fun p hp => (mem_filter.mp hp).2))
  have hlargeBound := hlarge hL hMle
  norm_num at hlargeBound
  rw [Real.dist_eq] at hcompact ⊢
  obtain ⟨hcompactLower, hcompactUpper⟩ := abs_lt.mp hcompact
  rw [hpart, mul_add, mul_add]
  have hnonneg : 0 ≤ 2 / M := by positivity
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end D5.S3.Arith.Robin.PriceRecord.ActualRoundingFullLimit
