/- GID: D5/S3/Midline/HeatLayers/GoldenHeatLayers
   generality: I
   mirror-B: D5/B/S3/Midline/HeatLayers/GoldenHeatLayers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden heat layers have decreasing abscissae tending to zero. -/

import Mathlib
import D5.S3.Analytic.GoldenEulerBeta
import D5.S3.Midline.GoldenHeatSpectrum
import D5.S3.Midline.UniversalHeatTrace

/- Provenance: Native proof over pinned mathlib. -/
/- SEARCH RECEIPT (2026-08-14): searched the repository D5 tree for
   `o5_beta_strictMono`, `goldenLayer`, `golden_layer`, layerwise summability,
   and reciprocal `o5Beta` abscissae. Miss: no layer-family result existed;
   `GoldenSpectralMarker.golden_spectral_marker` was only the `k = 0`
   reciprocal identity, while `GoldenHeatBoundary.golden_heat_boundary_divergent`
   treated the full product spectrum through its `k = 0` subfamily. Reused the
   frozen declarations `o5_beta_closed_form`, `o5_beta_power_law`,
   `o5_beta_growth`, `goldenSpectrum`, and `BoundaryDivergentAbscissa`.
   Searched pinned mathlib for `StrictMono`, `strictMono_nat_of_lt_succ`,
   `Int.fract_nonneg`, and `Int.fract_lt_one` (all hits); for prime-series
   criteria (hits: `Nat.Primes.summable_rpow` and
   `Nat.Primes.not_summable_one_div`); for reciprocal order (hit:
   `one_div_lt_one_div_of_lt`; miss: no directly applicable theorem packaging
   this `o5Beta` reciprocal family as `StrictAnti`); and for reciprocal limits
   (hits: `tendsto_natCast_atTop_atTop`, `tendsto_atTop_mono`,
   `Filter.Tendsto.inv_tendsto_atTop`,
   `tendsto_one_div_atTop_nhds_zero_nat`; miss: no theorem specialized to an
   `o5Beta` denominator). All hits used below rather than reproved. -/

namespace D5.S3.Midline.HeatLayers.GoldenHeatLayers

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Midline.GoldenHeatSpectrum
open D5.S3.Midline.UniversalHeatTrace
open Filter

noncomputable section

/-- The prime-indexed `k`-th layer of the golden heat spectrum. -/
noncomputable def goldenLayer (k : Nat) : Nat.Primes → Real := fun p =>
  goldenSpectrum (p, k)

/-- The golden Euler exponents increase strictly with their natural index. -/
theorem o5_beta_strictMono : StrictMono o5Beta := by
  apply strictMono_nat_of_lt_succ
  intro v
  rw [o5_beta_closed_form, o5_beta_closed_form]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_one : 1 < Real.sqrt 5 := by nlinarith
  norm_num [Nat.cast_add, Nat.cast_succ] at ⊢
  nlinarith [Int.fract_nonneg (((v : Real) + 1) * Real.goldenRatio),
    Int.fract_lt_one (((v : Real) + 1 + 1) * Real.goldenRatio)]

private theorem o5Beta_succ_pos (k : Nat) : 0 < o5Beta (k + 1) := by
  have hfirst : 0 < o5Beta 1 := by
    rw [o5_beta_power_law.1]
    positivity
  exact lt_of_lt_of_le hfirst
    (o5_beta_strictMono.monotone (Nat.succ_le_succ (Nat.zero_le k)))

private theorem prime_real_pos (p : Nat.Primes) : 0 < (p : Real) := by
  exact_mod_cast p.prop.pos

private theorem exp_neg_goldenLayer (k : Nat) (sigma : Real)
    (p : Nat.Primes) :
    Real.exp (-sigma * goldenLayer k p) =
      (p : Real) ^ (-sigma * o5Beta (k + 1)) := by
  rw [Real.rpow_def_of_pos (prime_real_pos p)]
  simp only [goldenLayer, goldenSpectrum]
  congr 1
  ring

private theorem golden_layer_summable_iff (k : Nat) (sigma : Real) :
    Summable (fun p : Nat.Primes => Real.exp (-sigma * goldenLayer k p)) ↔
      -sigma * o5Beta (k + 1) < -1 := by
  simp_rw [exp_neg_goldenLayer]
  exact Nat.Primes.summable_rpow

private theorem golden_layer_boundary_term (k : Nat) (p : Nat.Primes) :
    Real.exp (-(1 / o5Beta (k + 1)) * goldenLayer k p) =
      1 / (p : Real) := by
  rw [exp_neg_goldenLayer]
  have hexponent : -(1 / o5Beta (k + 1)) * o5Beta (k + 1) = -1 := by
    field_simp [ne_of_gt (o5Beta_succ_pos k)]
  rw [hexponent, Real.rpow_neg_one, one_div]

/-- Every layer has boundary-divergent abscissa equal to the reciprocal of its
golden Euler exponent. -/
theorem golden_layer_boundary_divergent (k : Nat) :
    BoundaryDivergentAbscissa (goldenLayer k) (1 / o5Beta (k + 1)) := by
  have hbeta : 0 < o5Beta (k + 1) := o5Beta_succ_pos k
  constructor
  · constructor
    · intro sigma hsigma
      rw [golden_layer_summable_iff]
      have hproduct : 1 < sigma * o5Beta (k + 1) :=
        (div_lt_iff₀ hbeta).mp hsigma
      linarith
    · intro sigma hsigma
      rw [golden_layer_summable_iff]
      have hproduct : sigma * o5Beta (k + 1) < 1 :=
        (lt_div_iff₀ hbeta).mp hsigma
      linarith
  · intro hsum
    have hone : Summable (fun p : Nat.Primes => 1 / (p : Real)) :=
      (summable_congr (golden_layer_boundary_term k)).mp hsum
    exact Nat.Primes.not_summable_one_div hone

/-- Layer convergence abscissae strictly decrease with the layer index. -/
theorem golden_layer_abscissa_strictAnti :
    StrictAnti (fun k : Nat => 1 / o5Beta (k + 1)) := by
  intro a b hab
  exact one_div_lt_one_div_of_lt (o5Beta_succ_pos a)
    (o5_beta_strictMono (Nat.add_lt_add_right hab 1))

/-- The layer convergence abscissae tend to zero. -/
theorem golden_layer_abscissa_tendsto_zero :
    Filter.Tendsto (fun k : Nat => 1 / o5Beta (k + 1))
      Filter.atTop (nhds 0) := by
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
  have hphi_inv : 0 < 1 / Real.goldenRatio := by positivity
  have hlower (k : Nat) : (k : Real) ≤ o5Beta (k + 1) := by
    apply le_trans _ (o5_beta_growth (k + 1))
    have hk : 0 ≤ (k : Real) := by positivity
    norm_num [Nat.cast_add]
    nlinarith
  have hbeta_atTop :
      Filter.Tendsto (fun k : Nat => o5Beta (k + 1))
        Filter.atTop Filter.atTop :=
    tendsto_atTop_mono hlower
      (tendsto_natCast_atTop_atTop (R := Real))
  convert hbeta_atTop.inv_tendsto_atTop using 1
  ext k
  simp only [Pi.inv_apply, one_div]

/-- Every excited layer lies strictly to the left of the full heat trace's
ground-layer abscissa. -/
theorem golden_excited_layer_abscissa_lt (k : Nat) (hk : 0 < k) :
    1 / o5Beta (k + 1) < 1 / Real.goldenRatio ^ 2 := by
  simpa only [Nat.zero_add, o5_beta_power_law.1] using
    (golden_layer_abscissa_strictAnti hk)

end

end D5.S3.Midline.HeatLayers.GoldenHeatLayers
