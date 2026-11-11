/- GID: D5/S3/Arith/Robin/PriceRecord/ActualRecordCriticalResidual
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualRecordCriticalResidual
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Complete actual nonfirst-layer loss vanishes uniformly in literal record prices. -/

import D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The finite complete-loss estimates supply the asymptotic residual on the
original integer logarithmic clock, uniformly in the original record price. -/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual

open Finset Real Filter
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
  (record_mass_limits record_log_envelope record_layer_ratio record_second_own_clock_limit)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (theta_error_log_power)

/- Fixed endpoints are taken AFTER fixing δ. These limits concern real X,
not primes in an assumed short interval. -/
private theorem tube_endpoint_limits (s : ℝ) :
    Tendsto (fun X : ℝ => secondTubePoint X s) atTop atTop ∧
    Tendsto (fun X : ℝ => secondTubePoint X s / sqrt X) atTop (𝓝 (sqrt 2)) ∧
    Tendsto (fun X : ℝ => log X / log (secondTubePoint X s)) atTop (𝓝 2) := by
  have ha : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have hu : Tendsto (fun X : ℝ => sqrt 2 + s / log X) atTop (𝓝 (sqrt 2)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop tendsto_log_atTop)
  have ht : Tendsto (fun X : ℝ => secondTubePoint X s) atTop atTop := by
    simpa only [secondTubePoint, mul_comm] using hu.pos_mul_atTop ha tendsto_sqrt_atTop
  have hr : Tendsto (fun X : ℝ => secondTubePoint X s / sqrt X)
      atTop (𝓝 (sqrt 2)) := by
    apply hu.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    dsimp [secondTubePoint]
    field_simp [(sqrt_pos.mpr hX).ne'] <;> ring
  have hlog : Tendsto (fun X : ℝ => log (secondTubePoint X s) / log X)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have hh := (hu.log ha.ne').div_atTop tendsto_log_atTop
    have hh' := hh.add_const (1 / 2 : ℝ)
    simp only [zero_add] at hh'
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hu.eventually (eventually_gt_nhds ha)] with X hX huX
    rw [secondTubePoint, log_mul (sqrt_pos.mpr (by linarith)).ne' huX.ne',
      log_sqrt (by linarith : 0 ≤ X)]
    field_simp [(log_pos hX).ne'] <;> ring
  refine ⟨ht, hr, ?_⟩
  convert hlog.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0) using 1 <;> simp [inv_div]

private theorem theta_error_at_tube (s : ℝ) :
    Tendsto (fun X : ℝ => (log X / sqrt X) *
      (Chebyshev.theta (secondTubePoint X s) - secondTubePoint X s))
      atTop (𝓝 0) := by
  obtain ⟨ht, hr, hlogs⟩ := tube_endpoint_limits s
  have he := (theta_error_log_power 1).tendsto_div_nhds_zero.comp ht
  have hh := (he.mul hr).mul hlogs
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), ht.eventually_gt_atTop 1] with X hX htX
  dsimp only [Function.comp_def]
  simp only [pow_one]
  field_simp [(show secondTubePoint X s ≠ 0 by linarith),
    (log_pos htX).ne', (sqrt_pos.mpr (by linarith : 0 < X)).ne'] <;> ring

private theorem second_expansion_error_limit (K : ℝ) :
    Tendsto (fun X : ℝ => secondExpansionError X K) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun X : ℝ => log X / sqrt X) atTop (𝓝 0) := by
    simpa only [rpow_one, sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hfirst : Tendsto (fun X : ℝ => (4 * K ^ 2 + 2 * K / sqrt 2) / log X)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hsecond := hsmall.const_mul (12 / sqrt (2 : ℝ) ^ 3)
  have hh := hfirst.add hsecond
  simp only [mul_zero, add_zero] at hh
  exact hh.congr (fun X => by unfold secondExpansionError; ring)

/-- G1: fixed δ, explicit compact error, geometry, and BOTH global N=1
theta errors imply the actual finite analytic hypotheses eventually. -/
private theorem fixed_tube_eventually {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop,
      1 < X ∧
      2 * (|secondTubeCenter| + 1) ≤ sqrt 2 * log X ∧
      secondExpansionError X (|secondTubeCenter| + 1) ≤ δ / (2 * sqrt 2) ∧
      sqrt X < secondTubePoint X (secondTubeCenter - δ) ∧
      |Chebyshev.theta (secondTubePoint X (secondTubeCenter - δ)) -
        secondTubePoint X (secondTubeCenter - δ)| ≤ δ * sqrt X / (2 * log X) ∧
      |Chebyshev.theta (secondTubePoint X (secondTubeCenter + δ)) -
        secondTubePoint X (secondTubeCenter + δ)| ≤ δ * sqrt X / (2 * log X) := by
  have ha : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have ha1 : 1 < sqrt (2 : ℝ) := by
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hu : Tendsto (fun X : ℝ => sqrt 2 + (secondTubeCenter - δ) / log X)
      atTop (𝓝 (sqrt 2)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop tendsto_log_atTop)
  have htheta (s : ℝ) : ∀ᶠ X : ℝ in atTop,
      |Chebyshev.theta (secondTubePoint X s) - secondTubePoint X s| ≤
        δ * sqrt X / (2 * log X) := by
    have he := (Metric.tendsto_nhds.mp (theta_error_at_tube s)) (δ / 2) (by positivity)
    filter_upwards [eventually_gt_atTop (1 : ℝ), he] with X hX heX
    have hL : 0 < log X := log_pos hX
    have hr : 0 < sqrt X := sqrt_pos.mpr (by linarith)
    have hh : (log X / sqrt X) *
        |Chebyshev.theta (secondTubePoint X s) - secondTubePoint X s| ≤ δ / 2 := by
      simpa only [Real.dist_eq, sub_zero, abs_mul, abs_div,
        abs_of_pos hL, abs_of_pos hr] using heX.le
    have hh' : log X *
        |Chebyshev.theta (secondTubePoint X s) - secondTubePoint X s| ≤ δ / 2 * sqrt X := by
      exact (div_le_iff₀ hr).mp (by simpa only [div_mul_eq_mul_div] using hh)
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hL)).mpr
    nlinarith
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_log_atTop.eventually_ge_atTop (2 * (|secondTubeCenter| + 1) / sqrt 2),
    (second_expansion_error_limit (|secondTubeCenter| + 1)).eventually
      (eventually_lt_nhds (show 0 < δ / (2 * sqrt 2) by positivity)),
    hu.eventually (eventually_gt_nhds ha1),
    htheta (secondTubeCenter - δ), htheta (secondTubeCenter + δ)]
      with X hX hlarge hrem hgeo hlo hhi
  refine ⟨hX, ?_, hrem.le, ?_, hlo, hhi⟩
  · simpa only [mul_comm] using (div_le_iff₀ ha).mp hlarge
  · unfold secondTubePoint
    exact lt_mul_of_one_lt_right (sqrt_pos.mpr (by linarith : 0 < X)) hgeo

/-- Bounded P bounds X for the original record, uniformly in its price. -/
private theorem record_prime_escape {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ x, 2 ≤ m x) (hmu : ∀ x, 0 < mu x)
    (hrecord : ∀ x k, 0 < k → k < m x →
      goldenResourceObjective (mu x) k < goldenResourceObjective (mu x) (m x))
    (hX : Tendsto (fun x => log (m x : ℝ)) l atTop) :
    Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop := by
  apply tendsto_atTop.mpr
  intro A
  let B : ℝ := max A 2
  have hB2 : 2 ≤ B := le_max_right _ _
  have hB0 : 0 < B := by linarith
  have hlogB : 0 < log (4 * B ^ 2) := log_pos (by nlinarith)
  filter_upwards [hX.eventually_ge_atTop (B * log (4 * B ^ 2) + 2)] with x hx
  by_contra! hsmall
  have hpB : (largestPrime (m x) : ℝ) ≤ B := hsmall.le.trans (le_max_left _ _)
  have hP2 : (2 : ℝ) ≤ largestPrime (m x) := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by have := hm x; omega : m x ≠ 1)
    exact_mod_cast hp.two_le.trans
      (le_sup (f := id) (hp.mem_primeFactors hpd (by have := hm x; omega : m x ≠ 0)))
  have hp0 : (0 : ℝ) ≤ largestPrime (m x) := by linarith
  have hlogle : log (4 * (largestPrime (m x) : ℝ) ^ 2) ≤ log (4 * B ^ 2) :=
    log_le_log (by positivity)
      (by nlinarith [pow_le_pow_left₀ hp0 hpB 2])
  have hmass := record_log_envelope (hm x) (hmu x) (hrecord x)
  have hbounded : log (m x : ℝ) ≤ B * log (4 * B ^ 2) := hmass.trans
    ((mul_le_mul_of_nonneg_left hlogle hp0).trans
      (mul_le_mul_of_nonneg_right hpB hlogB.le))
  linarith

/-- G2: the COMPLETE higher finite envelope, at the critical normalization,
tends to zero on every record family whose ORIGINAL logarithmic clock escapes.
R is chosen from X, not postulated as a prime/exponent cap. -/
private theorem higher_layer_negligible {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ x, 2 ≤ m x) (hmu : ∀ x, 0 < mu x)
    (hrecord : ∀ x k, 0 < k → k < m x →
      goldenResourceObjective (mu x) k < goldenResourceObjective (mu x) (m x))
    (hX : Tendsto (fun x => log (m x : ℝ)) l atTop)
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => sqrt (log (m x : ℝ)) * log (log (m x : ℝ)) ^ 3 *
      completeHigherLayerLoss (log (m x : ℝ)) (m x)) l (𝓝 0) := by
  let X : α → ℝ := fun x => log (m x : ℝ)
  let P : α → ℝ := fun x => largestPrime (m x)
  let Q : α → ℝ := fun x => layerPrime (m x) 3
  let R : α → ℝ := fun x => (X x * log (X x) / log 2) ^ (1 / 3 : ℝ)
  let E : α → ℝ := fun x => sqrt (X x) * log (X x) ^ 3 *
    (2 * R x / P x + referencePrice (X x) * (Q x * log (4 * P x ^ 2)))
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2le : log (2 : ℝ) ≤ 1 := by
    linarith [log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hL : Tendsto (fun x => log (X x)) l atTop := tendsto_log_atTop.comp hX
  have hXP : Tendsto (fun x => X x / P x) l (𝓝 1) :=
    (record_mass_limits m mu hm hmu hrecord hP).2.2.1
  have hQ3 : Tendsto (fun x => Q x ^ 3 / P x) l (𝓝 3) :=
    record_layer_ratio m mu hm hmu hrecord hP 3 (by norm_num)
  have hsmall : Tendsto (fun x => log (X x) / X x ^ (1 / 4 : ℝ)) l (𝓝 0) := by
    simpa only [rpow_one, Function.comp_def] using
      ((isLittleO_log_rpow_rpow_atTop (1 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero.comp hX)
  have hmajor : Tendsto (fun x => 8 * (log (X x) ^ 3 / X x ^ (1 / 12 : ℝ)))
      l (𝓝 0) := by
    have hh := ((isLittleO_log_rpow_rpow_atTop (3 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 12)).tendsto_div_nhds_zero.comp hX).const_mul 8
    simpa only [rpow_natCast, rpow_ofNat, Function.comp_def, mul_zero] using hh
  have hregime : ∀ᶠ x in l,
      1 < X x ∧ 1 ≤ R x ∧ R x < P x ∧
      X x * log (X x) = log 2 * R x ^ 3 ∧
      0 ≤ E x ∧ E x ≤ 8 * (log (X x) ^ 3 / X x ^ (1 / 12 : ℝ)) := by
    filter_upwards [hX.eventually_gt_atTop 4, hL.eventually_ge_atTop 1,
      hP.eventually_gt_atTop 0,
      hXP.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hXP.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)),
      hQ3.eventually (eventually_lt_nhds (by norm_num : (3 : ℝ) < 4)),
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hX).eventually_ge_atTop 8,
      hsmall.eventually (eventually_lt_nhds hlog2)]
        with x hx hLx hp hlow hhigh hq hpow hlogs
    change 4 < X x at hx
    change 0 < P x at hp
    change 8 ≤ X x ^ (1 / 4 : ℝ) at hpow
    have hx0 : 0 < X x := by linarith
    have hL0 : 0 < log (X x) := by linarith
    have hcomp : X x / 2 ≤ P x ∧ P x ≤ 2 * X x := by
      constructor
      · have hh := (div_lt_iff₀ hp).mp hhigh
        linarith
      · have hh := (lt_div_iff₀ hp).mp hlow
        linarith
    let C : ℝ := X x ^ (5 / 12 : ℝ)
    have hC0 : 0 ≤ C := rpow_nonneg hx0.le _
    have hCcube : C ^ 3 = X x * X x ^ (1 / 4 : ℝ) := by
      dsimp [C]
      rw [← rpow_mul_natCast hx0.le]
      have he : (5 / 12 : ℝ) * (3 : ℕ) = 1 + (1 / 4 : ℝ) := by norm_num
      rw [he, rpow_add hx0, rpow_one]
    have hbase : 0 < X x * log (X x) / log 2 := by positivity
    have hR0 : 0 ≤ R x := rpow_nonneg hbase.le _
    have hRcube : R x ^ 3 = X x * log (X x) / log 2 := by
      dsimp [R]
      rw [← rpow_mul_natCast hbase.le]
      norm_num
    have hclock : X x * log (X x) = log 2 * R x ^ 3 := by
      rw [hRcube]
      field_simp [hlog2.ne'] <;> ring
    have hR1 : 1 ≤ R x := by
      have hb : 1 ≤ X x * log (X x) / log 2 := by
        apply (le_div_iff₀ hlog2).mpr
        nlinarith [mul_le_mul_of_nonneg_left hLx hx0.le]
      have hh := rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hb
        (by norm_num : (0 : ℝ) ≤ 1 / 3)
      simpa only [one_rpow] using hh
    have hRC : R x ≤ C := by
      have hb : log (X x) / log 2 ≤ X x ^ (1 / 4 : ℝ) := by
        apply (div_le_iff₀ hlog2).mpr
        have hh := (div_lt_iff₀ (rpow_pos_of_pos hx0 (1 / 4 : ℝ))).mp hlogs
        linarith
      have hh : R x ^ 3 ≤ C ^ 3 := by
        rw [hRcube, hCcube, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hb hx0.le
      by_contra! hnot
      exact (not_lt_of_ge hh) (pow_lt_pow_left₀ hnot hC0 (by norm_num : (3 : ℕ) ≠ 0))
    have hQC : Q x ≤ C := by
      have hh : Q x ^ 3 ≤ C ^ 3 := by
        rw [hCcube]
        have hq' : Q x ^ 3 < 4 * P x := (div_lt_iff₀ hp).mp hq
        calc
          Q x ^ 3 ≤ 4 * P x := hq'.le
          _ ≤ 8 * X x := by linarith only [hcomp.2]
          _ ≤ X x * X x ^ (1 / 4 : ℝ) := by
            nlinarith only [mul_le_mul_of_nonneg_left hpow hx0.le]
      by_contra! hnot
      exact (not_lt_of_ge hh) (pow_lt_pow_left₀ hnot hC0 (by norm_num : (3 : ℕ) ≠ 0))
    have hCsqrt : C ≤ sqrt (X x) := by
      rw [sqrt_eq_rpow]
      exact rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : (5 / 12 : ℝ) ≤ 1 / 2)
    have hsqrt : sqrt (X x) < X x / 2 := by
      have hr2 : 2 < sqrt (X x) := by
        nlinarith [sq_sqrt hx0.le, sqrt_nonneg (X x)]
      nlinarith [sq_sqrt hx0.le,
        mul_pos (sqrt_pos.mpr hx0) (sub_pos.mpr hr2)]
    have hRP : R x < P x := (hRC.trans hCsqrt).trans_lt (hsqrt.trans_le hcomp.1)
    have hlogB0 : 0 ≤ log (4 * P x ^ 2) := by
      apply log_nonneg
      nlinarith [hcomp.1]
    have hlogB : log (4 * P x ^ 2) ≤ 4 * log (X x) := by
      have hb : log (4 * P x ^ 2) ≤ log (16 * X x ^ 2) :=
        log_le_log (by positivity) (by
          nlinarith [pow_le_pow_left₀ hp.le hcomp.2 2])
      have h16 : log (16 : ℝ) ≤ 2 * log (X x) := by
        have hh := log_le_log (by norm_num : (0 : ℝ) < 16)
          (show 16 ≤ X x ^ 2 by nlinarith)
        simpa only [log_pow, Nat.cast_ofNat] using hh
      rw [log_mul (by norm_num : (16 : ℝ) ≠ 0) (pow_ne_zero 2 hx0.ne'), log_pow] at hb
      norm_num only [Nat.cast_ofNat] at hb
      linarith only [hb, h16]
    have hbound : 2 * R x / P x + referencePrice (X x) * (Q x * log (4 * P x ^ 2)) ≤
        8 * C / X x := by
      have hfirst : 2 * R x / P x ≤ 4 * C / X x := by
        apply (div_le_div_iff₀ hp hx0).mpr
        nlinarith [mul_le_mul_of_nonneg_left hcomp.1 (show 0 ≤ 4 * C by positivity),
          mul_le_mul_of_nonneg_right hRC hx0.le]
      have hsecond : referencePrice (X x) * (Q x * log (4 * P x ^ 2)) ≤ 4 * C / X x := by
        have hb : Q x * log (4 * P x ^ 2) ≤ C * (4 * log (X x)) :=
          (mul_le_mul_of_nonneg_right hQC hlogB0).trans
            (mul_le_mul_of_nonneg_left hlogB hC0)
        have hh := mul_le_mul_of_nonneg_left hb (reference_price_pos (by linarith : 1 < X x)).le
        convert hh using 1 <;> unfold referencePrice <;> field_simp [hx0.ne', hL0.ne'] <;> ring
      calc
        _ ≤ 4 * C / X x + 4 * C / X x := add_le_add hfirst hsecond
        _ = 8 * C / X x := by ring
    have hscale : 0 ≤ sqrt (X x) * log (X x) ^ 3 := by positivity
    have hnorm : sqrt (X x) * log (X x) ^ 3 * (8 * C / X x) =
        8 * (log (X x) ^ 3 / X x ^ (1 / 12 : ℝ)) := by
      have he : sqrt (X x) * C * X x ^ (1 / 12 : ℝ) = X x := by
        dsimp [C]
        rw [sqrt_eq_rpow, ← rpow_add hx0, ← rpow_add hx0]
        norm_num
      field_simp [hx0.ne', (rpow_pos_of_pos hx0 (1 / 12 : ℝ)).ne']
      nlinarith [congrArg (fun z : ℝ => 8 * log (X x) ^ 3 * z) he]
    refine ⟨by linarith, hR1, hRP, hclock, ?_, ?_⟩
    · dsimp [E]
      exact mul_nonneg hscale (add_nonneg (by positivity)
        (mul_nonneg (reference_price_pos (by linarith : 1 < X x)).le
          (mul_nonneg (Nat.cast_nonneg _) hlogB0)))
    · dsimp [E]
      exact (mul_le_mul_of_nonneg_left hbound hscale).trans_eq hnorm
  -- The actual finite envelope itself tends to zero; no assumed loss bound.
  have hEnv : Tendsto E l (𝓝 0) := squeeze_zero'
    (hregime.mono fun _ h => h.2.2.2.2.1)
    (hregime.mono fun _ h => h.2.2.2.2.2) hmajor
  apply squeeze_zero' _ _ hEnv
  · filter_upwards [hregime] with x hx
    have hfin := finite_complete_higher_layer_bound hx.1 (hm x) (hmu x) (hrecord x)
      hx.2.1 hx.2.2.1 hx.2.2.2.1.le
    exact mul_nonneg (mul_nonneg (sqrt_nonneg _) (pow_nonneg (log_nonneg hx.1.le) 3)) hfin.1
  · filter_upwards [hregime] with x hx
    have hfin := finite_complete_higher_layer_bound hx.1 (hm x) (hmu x) (hrecord x)
      hx.2.1 hx.2.2.1 hx.2.2.2.1.le
    exact mul_le_mul_of_nonneg_left hfin.2.2
      (mul_nonneg (sqrt_nonneg _) (pow_nonneg (log_nonneg hx.1.le) 3))

/-- Uniform critical residual beyond the COMPLETE first layer, on the literal
original integer and every arbitrary positive original record price. The one
threshold precedes BOTH m and mu. No first-layer or total-defect bound is assumed. -/
theorem actual_record_critical_residual :
    ∀ ε : ℝ, 0 < ε → ∃ X0 : ℝ, 1 < X0 ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective mu k < goldenResourceObjective mu m) →
      X0 ≤ log (m : ℝ) →
      let X := log (m : ℝ)
      0 ≤ sqrt X * log X ^ 3 * (actualDefect X m - completeFirstLayerLoss X m) ∧
      sqrt X * log X ^ 3 * (actualDefect X m - completeFirstLayerLoss X m) < ε := by
  intro ε hε
  classical
  let a : ℝ := sqrt 2
  let δ : ℝ := min 1 (sqrt (a * ε / 36))
  have ha : 0 < a := sqrt_pos.mpr (by norm_num)
  have hb : 0 < a * ε / 36 := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (sqrt_pos.mpr hb)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδsq : δ ^ 2 ≤ a * ε / 36 := by
    have hle : δ ≤ sqrt (a * ε / 36) := min_le_right _ _
    have hh := pow_le_pow_left₀ hδ.le hle 2
    simpa only [sq_sqrt hb.le] using hh
  have hbudget : 9 * δ ^ 2 / a ≤ ε / 4 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧
    ∀ k : ℕ, 0 < k → k < v.1 →
      goldenResourceObjective v.2 k < goldenResourceObjective v.2 v.1}
  let m : S → ℕ := fun x => x.1.1
  let mu : S → ℝ := fun x => x.1.2
  let X : S → ℝ := fun x => log (m x : ℝ)
  let l : Filter S := comap X atTop
  have hX : Tendsto X l atTop := tendsto_comap
  have hm (x : S) : 2 ≤ m x := x.2.1
  have hmu (x : S) : 0 < mu x := x.2.2.1
  have hrecord (x : S) (k : ℕ) : 0 < k → k < m x →
      goldenResourceObjective (mu x) k < goldenResourceObjective (mu x) (m x) := x.2.2.2 k
  have hP := record_prime_escape m mu hm hmu hrecord hX
  have hQ := record_second_own_clock_limit m mu hm hmu hrecord hP
  have hQtube := (Metric.tendsto_nhds.mp hQ) δ hδ
  have hthird := higher_layer_negligible m mu hm hmu hrecord hX hP
  have hthirdSmall := (Metric.tendsto_nhds.mp hthird) (ε / 2) (by positivity)
  -- δ was fixed before this real analytic tail and before the record tails.
  have hanalytic := hX.eventually (fixed_tube_eventually hδ)
  have hall : ∀ᶠ x in l,
      0 ≤ sqrt (X x) * log (X x) ^ 3 *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) ∧
      sqrt (X x) * log (X x) ^ 3 *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) < ε := by
    filter_upwards [hanalytic, hQtube, hthirdSmall] with x hx hqx htx
    obtain ⟨hx1, hlarge, hrem, hA, hθlo, hθhi⟩ := hx
    have hL : 0 < log (X x) := log_pos hx1
    have hr : 0 < sqrt (X x) := sqrt_pos.mpr (by linarith)
    have hq : |log (X x) * ((layerPrime (m x) 2 : ℝ) / sqrt (X x) - sqrt 2) -
        secondTubeCenter| < δ := by
      simpa only [Real.dist_eq, secondTubeCenter, sub_neg_eq_add, X, m] using hqx
    have hQlo : secondTubePoint (X x) (secondTubeCenter - δ) < (layerPrime (m x) 2 : ℝ) := by
      have hh : (secondTubeCenter - δ) / log (X x) <
          (layerPrime (m x) 2 : ℝ) / sqrt (X x) - sqrt 2 := by
        apply (div_lt_iff₀ hL).mpr
        nlinarith [(abs_lt.mp hq).1]
      have hh' : sqrt 2 + (secondTubeCenter - δ) / log (X x) <
          (layerPrime (m x) 2 : ℝ) / sqrt (X x) := by linarith
      have hh'' := (lt_div_iff₀ hr).mp hh'
      simpa only [secondTubePoint, mul_comm] using hh''
    have hQhi : (layerPrime (m x) 2 : ℝ) < secondTubePoint (X x) (secondTubeCenter + δ) := by
      have hh : (layerPrime (m x) 2 : ℝ) / sqrt (X x) - sqrt 2 <
          (secondTubeCenter + δ) / log (X x) := by
        apply (lt_div_iff₀ hL).mpr
        nlinarith [(abs_lt.mp hq).2]
      have hh' : (layerPrime (m x) 2 : ℝ) / sqrt (X x) <
          sqrt 2 + (secondTubeCenter + δ) / log (X x) := by linarith
      have hh'' := (div_lt_iff₀ hr).mp hh'
      simpa only [secondTubePoint, mul_comm] using hh''
    have hsecond := finite_actual_second_layer_tube_bound hx1 (by have := hm x; omega : 1 ≤ m x)
      hδ hδ1 (price_record_prime_structure (hm x) (hmu x) (hrecord x)).1
      hlarge hrem hA hQlo hQhi hθlo hθhi
    have hscale : 0 ≤ sqrt (X x) * log (X x) ^ 3 := by positivity
    have hD0 : 0 ≤ sqrt (X x) * log (X x) ^ 3 * completeHigherLayerLoss (X x) (m x) :=
      mul_nonneg hscale (sum_nonneg fun p _ => sum_nonneg fun j _ =>
        layer_loss_nonneg (X x) (m x) p j)
    have hDsmall : sqrt (X x) * log (X x) ^ 3 * completeHigherLayerLoss (X x) (m x) < ε / 2 := by
      exact (le_abs_self _).trans_lt (by
        simpa only [Real.dist_eq, sub_zero, X, m] using htx)
    have hid : sqrt (X x) * log (X x) ^ 3 *
        (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x)) =
        sqrt (X x) * log (X x) ^ 3 *
          (actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x) -
            completeHigherLayerLoss (X x) (m x)) +
        sqrt (X x) * log (X x) ^ 3 * completeHigherLayerLoss (X x) (m x) := by ring
    rw [hid]
    constructor
    · exact add_nonneg hsecond.1 hD0
    · have hsecond' := hsecond.2
      change _ ≤ 9 * δ ^ 2 / a at hsecond'
      linarith
  -- Filter extraction selects ONE own-X threshold before any record pair.
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  refine ⟨max B 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn price hprice hrec hlarge
  let x : S := ⟨(n, price), hn, hprice, hrec⟩
  have hx := hB (log (n : ℝ)) ((le_max_left B 2).trans hlarge) x rfl
  simpa only [X, m] using hx

end D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
