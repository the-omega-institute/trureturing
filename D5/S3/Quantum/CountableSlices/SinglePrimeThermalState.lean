/- GID: D5/S3/Quantum/CountableSlices/SinglePrimeThermalState
   generality: I
   mirror-B: D5/B/S3/Quantum/CountableSlices/SinglePrimeThermalState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalized geometric prime spectra have closed entropy and explicit degenerations. -/

import Mathlib
import D5.S3.Analytic.Zeta.PrimeMarginalEntropy
import D5.S3.Analytic.Zeta.EulerLogBridge

/- Library-search audit trail (2026-08-25): `tsum_geometric_of_lt_one` and
   `hasSum_geometric_of_lt_one` were found in pinned mathlib and are used for normalization.
   `Real.rpow` positivity, order, logarithm, and asymptotic lemmas were found and used.
   No `PMF.geometric` declaration was found; the deprecated `ProbabilityTheory.geometricPMF`
   was found, but this module constructs the PMF directly from the normalized spectrum.
   Searches for `lp`, `Matrix.trace`, and `ContinuousLinearMap.trace` found only finite or
   unrelated APIs; no countable trace-class operator API was found. The finite-dimensional
   `ZetaThermalStatePinchingFixed` module uses `Fin d` matrices and is not applicable.
   `PrimeExponentLaw` supplies a different zeta marginal, while `PrimeMarginalEntropy`
   supplies the reusable generic geometric entropy closed form. `EulerLogBridge` supplies
   the existing zeta entropy decomposition used for modal additivity.

   Strength choice: this is the spectral-sequence formalization of the countable diagonal
   model, not a trace-class operator construction. The hypotheses are audited below: only
   `1 < p` and `0 < s` are used to obtain `0 < p^(-s) < 1`; primality is not load-bearing.
   The endpoint `s = 0`, base `p = 1`, negative temperature, zero slot, and the limit
   `s -> infinity` are all recorded explicitly. The restricted tensor product theorem is
   intentionally not formalized.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Filter Topology

namespace D5.S3.Quantum.CountableSlices.SinglePrimeThermalState

open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
open D5.S3.Analytic.Zeta.EulerLogBridge
open D5.S3.Analytic.ZetaGibbs

noncomputable section

/-- Definition 140.1 represented by its diagonal occupation-number spectrum. -/
def singlePrimeThermalState (p : ℕ) (s : ℝ) : ℕ → ℝ :=
  fun k => (1 - (p : ℝ) ^ (-s)) * ((p : ℝ) ^ (-s)) ^ k

private lemma ratio_bounds (p : ℕ) (s : ℝ) (hp : 1 < p) (hs : 0 < s) :
    0 < (p : ℝ) ^ (-s) ∧ (p : ℝ) ^ (-s) < 1 := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
  exact ⟨Real.rpow_pos_of_pos (by positivity) _,
    Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)⟩

/-- Every spectral weight is nonnegative in the positive-temperature regime. -/
theorem singlePrimeThermalState_nonneg (p : ℕ) (s : ℝ) (hp : 1 < p) (hs : 0 < s)
    (k : ℕ) : 0 ≤ singlePrimeThermalState p s k := by
  rw [singlePrimeThermalState]
  exact mul_nonneg (sub_nonneg.mpr (ratio_bounds p s hp hs).2.le)
    (pow_nonneg (ratio_bounds p s hp hs).1.le _)

#print axioms singlePrimeThermalState_nonneg

/-- The spectral weights sum to one; this is the explicit normalization. -/
theorem singlePrimeThermalState_tsum_eq_one (p : ℕ) (s : ℝ) (hp : 1 < p) (hs : 0 < s) :
    ∑' k : ℕ, singlePrimeThermalState p s k = 1 := by
  let q : ℝ := (p : ℝ) ^ (-s)
  have hq := ratio_bounds p s hp hs
  have hgeom : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_lt_one hq.1.le hq.2
  change ∑' k : ℕ, (1 - q) * q ^ k = 1
  rw [hgeom.tsum_mul_left, tsum_geometric_of_lt_one hq.1.le hq.2]
  exact mul_inv_cancel₀ (sub_ne_zero.mpr hq.2.ne')

#print axioms singlePrimeThermalState_tsum_eq_one

/-- The zero-occupation term is the vacuum weight `1 - p^(-s)`. -/
theorem singlePrimeThermalState_zero_slot (p : ℕ) (s : ℝ) :
    singlePrimeThermalState p s 0 = 1 - (p : ℝ) ^ (-s) := by
  simp [singlePrimeThermalState]

#print axioms singlePrimeThermalState_zero_slot

/-- A positive-temperature spectrum is a PMF on occupation numbers. -/
def singlePrimeThermalPMF (p : ℕ) (s : ℝ) (hp : 1 < p) (hs : 0 < s) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (singlePrimeThermalState p s k), by
    have hstate : Summable (singlePrimeThermalState p s) := by
      let q : ℝ := (p : ℝ) ^ (-s)
      have hq := ratio_bounds p s hp hs
      have hgeom : Summable (fun k : ℕ => q ^ k) :=
        summable_geometric_of_lt_one hq.1.le hq.2
      change Summable (fun k : ℕ => (1 - q) * q ^ k)
      exact hgeom.mul_left _
    apply (ENNReal.summable.hasSum_iff).2
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun k => singlePrimeThermalState_nonneg p s hp hs k) hstate]
    rw [singlePrimeThermalState_tsum_eq_one p s hp hs]
    exact ENNReal.ofReal_one⟩

/-- The PMF real mass is exactly the named thermal spectrum. -/
theorem singlePrimeThermalPMF_apply (p : ℕ) (s : ℝ) (hp : 1 < p) (hs : 0 < s) (k : ℕ) :
    pmfReal (singlePrimeThermalPMF p s hp hs) k = singlePrimeThermalState p s k := by
  rw [pmfReal, singlePrimeThermalPMF]
  exact ENNReal.toReal_ofReal (singlePrimeThermalState_nonneg p s hp hs k)

#print axioms singlePrimeThermalPMF_apply

/-- The named PMF is the ratio-parameter geometric law with ratio `p^(-s)`. -/
theorem singlePrimeThermalPMF_is_geometric (p : ℕ) (s : ℝ) (hp : 1 < p) (hs : 0 < s) :
    ∀ k : ℕ, pmfReal (singlePrimeThermalPMF p s hp hs) k =
      (1 - (p : ℝ) ^ (-s)) * ((p : ℝ) ^ (-s)) ^ k := by
  intro k
  exact singlePrimeThermalPMF_apply p s hp hs k

#print axioms singlePrimeThermalPMF_is_geometric

/-- Closed Gibbs entropy formula for one prime thermal mode. -/
theorem singlePrimeThermal_entropy_eq (p : ℕ) (s : ℝ) (hp : 1 < p) (hs : 0 < s) :
    countableEntropy (singlePrimeThermalPMF p s hp hs) =
      -Real.log (1 - (p : ℝ) ^ (-s)) +
        s * Real.log p * ((p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s))) := by
  let q : ℝ := (p : ℝ) ^ (-s)
  have hq := ratio_bounds p s hp hs
  have hlog : Real.log q = -(s * Real.log (p : ℝ)) := by
    dsimp [q]
    rw [Real.log_rpow (by positivity)]
    ring
  apply geometric_entropy_eq (singlePrimeThermalPMF p s hp hs) q
    (s * Real.log (p : ℝ)) hq.1 hq.2 hlog
  intro k
  simpa [singlePrimeThermalState, q] using singlePrimeThermalPMF_apply p s hp hs k

#print axioms singlePrimeThermal_entropy_eq

/-- Modal entropy additivity for the existing zeta diagonal law. -/
theorem modal_thermal_entropy_additive (s : ℝ) (hs : 1 < s) :
    countableEntropy (zetaDist s hs) =
      ∑' p : Nat.Primes,
        countableEntropy (singlePrimeThermalPMF p.1 s p.2.one_lt (by linarith)) := by
  rw [countableEntropy_zeta_eq_tsum_prime s hs]
  apply tsum_congr
  intro p
  rw [primeExponent_entropy_eq s hs p, singlePrimeThermal_entropy_eq p.1 s p.2.one_lt
    (by linarith)]

#print axioms modal_thermal_entropy_additive

/-- The base assumption `p > 1` cannot be dropped: at `p = 1` the mass is zero. -/
theorem base_gt_one_is_necessary :
    ∑' k : ℕ, singlePrimeThermalState 1 1 k ≠ 1 := by
  simp [singlePrimeThermalState]

#print axioms base_gt_one_is_necessary

/-- The positive-temperature assumption cannot be dropped: at `s = 0` the sum is zero. -/
theorem positive_temperature_is_necessary :
    ∑' k : ℕ, singlePrimeThermalState 2 0 k ≠ 1 := by
  simp [singlePrimeThermalState]

#print axioms positive_temperature_is_necessary

/-- A negative-temperature concrete spectrum is not summable. -/
theorem negative_temperature_not_summable :
    ¬Summable (fun k : ℕ => singlePrimeThermalState 2 (-1) k) := by
  intro h
  have hzero : Tendsto (fun k : ℕ => singlePrimeThermalState 2 (-1) k) atTop (𝓝 0) :=
    Summable.tendsto_atTop_zero h
  have hpow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hbot : Tendsto (fun k : ℕ => -((2 : ℝ) ^ k)) atTop atBot := by
    apply (Filter.tendsto_neg_atTop_iff).mp
    simpa using hpow
  have hEq : (fun k : ℕ => singlePrimeThermalState 2 (-1) k) =
      (fun k : ℕ => -((2 : ℝ) ^ k)) := by
    funext k
    simp [singlePrimeThermalState]
    ring
  rw [hEq] at hzero
  exact (not_tendsto_nhds_of_tendsto_atBot hbot 0) hzero

#print axioms negative_temperature_not_summable

/-- At positive temperature, every fixed mode converges to the vacuum spectrum as `s -> ∞`. -/
theorem singlePrimeThermalState_tendsto_infinite_temperature (p : ℕ) (hp : 1 < p) (k : ℕ) :
    Tendsto (fun s : ℝ => singlePrimeThermalState p s k) atTop
      (𝓝 (if k = 0 then 1 else 0)) := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
  have hq : Tendsto (fun s : ℝ => (p : ℝ) ^ (-s)) atTop (𝓝 0) := by
    have hbase : -1 < (p : ℝ)⁻¹ := by
      have hpos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by positivity)
      linarith
    convert tendsto_rpow_atTop_of_base_lt_one ((p : ℝ)⁻¹) hbase
      (inv_lt_one_of_one_lt₀ hpR) using 1
    funext s
    exact Real.rpow_neg_eq_inv_rpow _ _
  by_cases hk : k = 0
  · subst k
    have hlim : Tendsto (fun s : ℝ => 1 - (p : ℝ) ^ (-s)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hq
    simpa [singlePrimeThermalState] using hlim
  · have hpow : Tendsto (fun s : ℝ => ((p : ℝ) ^ (-s)) ^ k) atTop (𝓝 0) := by
      simpa [zero_pow hk] using hq.pow k
    have hfactor : Tendsto (fun s : ℝ => 1 - (p : ℝ) ^ (-s)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hq
    have hprod : Tendsto
        (fun s : ℝ => (1 - (p : ℝ) ^ (-s)) * ((p : ℝ) ^ (-s)) ^ k) atTop
        (𝓝 ((1 - 0) * 0)) :=
      hfactor.mul hpow
    simpa [singlePrimeThermalState, hk] using hprod

#print axioms singlePrimeThermalState_tendsto_infinite_temperature

end

end D5.S3.Quantum.CountableSlices.SinglePrimeThermalState
