/- GID: D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryCoefficients
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact ordinary inverse coefficients of the actual composition reciprocal. -/

import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCoefficientIdentity
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Ordinary coefficient realization for the actual finite-slit reciprocal. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter Set Topology
open scoped BigOperators

namespace D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryCoefficients

/-- The original ordinary formal inverse, over the real coefficient field. -/
def ordinary (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) : PowerSeries ℝ :=
  ((PowerSeries.mk (CompositionDisk.coefficient head tail)) ^ (ell : ℕ))⁻¹

private theorem one_hasSum (z : ℂ) :
    HasSum (fun n : ℕ ↦ PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) 1 := by
  have heq : (fun n : ℕ ↦ PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) =
      (fun n : ℕ ↦ if n = 0 then (1 : ℂ) else 0) := by
    funext n
    by_cases hn : n = 0 <;> simp [hn]
  rw [heq]
  exact hasSum_ite_eq (0 : ℕ) (1 : ℂ)

private theorem mul_hasSum (p q : PowerSeries ℂ) (z a b : ℂ)
    (hp : HasSum (fun n ↦ PowerSeries.coeff n p * z ^ n) a)
    (hq : HasSum (fun n ↦ PowerSeries.coeff n q * z ^ n) b) :
    HasSum (fun n ↦ PowerSeries.coeff n (p * q) * z ^ n) (a * b) := by
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm
    hp.summable.norm hq.summable.norm).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    hp.summable.norm hq.summable.norm, hp.tsum_eq, hq.tsum_eq] at hs
  convert hs using 1
  funext n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [← hn, pow_add]
  ring

private theorem pow_hasSum (p : PowerSeries ℂ) (z a : ℂ)
    (hp : HasSum (fun n ↦ PowerSeries.coeff n p * z ^ n) a) (k : ℕ) :
    HasSum (fun n ↦ PowerSeries.coeff n (p ^ k) * z ^ n) (a ^ k) := by
  induction k with
  | zero => simpa using one_hasSum z
  | succ k ih =>
    simpa only [pow_succ] using mul_hasSum (p ^ k) p z (a ^ k) a ih hp

private theorem unique (p q : PowerSeries ℂ) (f : ℂ → ℂ)
    (hp : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n ↦ PowerSeries.coeff n p * z ^ n) (f z))
    (hq : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n ↦ PowerSeries.coeff n q * z ^ n) (f z)) :
    p = q := by
  have series (s : PowerSeries ℂ)
      (hs : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n ↦ PowerSeries.coeff n s * z ^ n) (f z)) :
      HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ PowerSeries.coeff n s)) 0 := by
    apply hasFPowerSeriesAt_iff'.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    simpa only [sub_zero, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm]
      using hs z (by simpa using hz)
  have h := (series p hp).eq_formalMultilinearSeries (series q hq)
  apply PowerSeries.ext
  intro n
  have hc := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ ↦ s.coeff n) h
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using hc

/-- Exact ordinary inverse realization and the all-composition eventual negative coefficient law. -/
theorem result (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    (∀ n : ℕ, ((PowerSeries.coeff n (ordinary head tail ell) : ℝ) : ℂ) =
      iteratedDeriv n (FiniteSlitCompositionMoments.reciprocal head tail ell) 0 /
        (n.factorial : ℂ)) ∧
    (∀ z : ℂ, ‖z‖ < 1 → HasSum
      (fun n : ℕ ↦ ((PowerSeries.coeff n (ordinary head tail ell) : ℝ) : ℂ) * z ^ n)
      (FiniteSlitCompositionMoments.reciprocal head tail ell z)) ∧
    (∀ᶠ n : ℕ in atTop, PowerSeries.coeff n (ordinary head tail ell) < 0) := by
  obtain ⟨R0, ρ, R, B, upper, _hR0, _hρ, _hρ1, _hR, _hRR0, _hRρ,
    _hB, _ha, hdisk, _hzero, _hu, _he, hi, hs, hneg⟩ :=
    FiniteSlitCoefficientIdentity.result head tail ell
  let p : PowerSeries ℝ := PowerSeries.mk (CompositionDisk.coefficient head tail)
  let pc : PowerSeries ℂ := PowerSeries.map Complex.ofRealHom p
  let c : ℕ → ℂ := fun n ↦
    iteratedDeriv n (FiniteSlitCompositionMoments.reciprocal head tail ell) 0 /
      (n.factorial : ℂ)
  let q : PowerSeries ℂ := PowerSeries.mk c
  have hp (z : ℂ) (hz : ‖z‖ < 1) : HasSum
      (fun n ↦ PowerSeries.coeff n pc * z ^ n) (CompositionDisk.normalized head tail z) := by
    simpa only [pc, p, PowerSeries.coeff_map, PowerSeries.coeff_mk, Complex.ofRealHom_eq_coe,
      CompositionDisk.normalized] using
      ((CompositionDisk.source_series head tail).2.2.1 z hz).of_norm.hasSum
  have hq (z : ℂ) (hz : ‖z‖ < 1) : HasSum
      (fun n ↦ PowerSeries.coeff n q * z ^ n)
      (FiniteSlitCompositionMoments.reciprocal head tail ell z) := by
    simpa only [q, PowerSeries.coeff_mk, c] using hs z hz
  have hmul : q * pc ^ (ell : ℕ) = 1 := by
    apply unique _ _ (fun _ ↦ 1)
    · intro z hz
      have h := mul_hasSum q (pc ^ (ell : ℕ)) z _ _ (hq z hz)
        (pow_hasSum pc z _ (hp z hz) (ell : ℕ))
      have hn := (CompositionZeroFree.result head tail).2.2.1 z hz
      rw [hdisk z hz, ← mul_pow, inv_mul_cancel₀ hn, one_pow] at h
      exact h
    · intro z _
      exact one_hasSum z
  have hp0 : PowerSeries.constantCoeff (p ^ (ell : ℕ)) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (ne_of_gt ((CompositionDisk.source_series head tail).1 0))
  have hpc0 : PowerSeries.constantCoeff (pc ^ (ell : ℕ)) ≠ 0 := by
    rw [show pc ^ (ell : ℕ) = PowerSeries.map Complex.ofRealHom (p ^ (ell : ℕ)) by
      exact (map_pow (PowerSeries.map Complex.ofRealHom) p (ell : ℕ)).symm]
    change ((PowerSeries.constantCoeff (p ^ (ell : ℕ)) : ℝ) : ℂ) ≠ 0
    exact_mod_cast hp0
  have hmap : PowerSeries.map Complex.ofRealHom ((p ^ (ell : ℕ))⁻¹) *
      pc ^ (ell : ℕ) = 1 := by
    dsimp only [pc]
    rw [← map_pow, ← map_mul, PowerSeries.inv_mul_cancel _ hp0, map_one]
  have heq : q = PowerSeries.map Complex.ofRealHom ((p ^ (ell : ℕ))⁻¹) :=
    ((PowerSeries.eq_inv_iff_mul_eq_one hpc0).mpr hmul).trans
      ((PowerSeries.eq_inv_iff_mul_eq_one hpc0).mpr hmap).symm
  have hc (n : ℕ) : ((PowerSeries.coeff n (ordinary head tail ell) : ℝ) : ℂ) = c n := by
    have h := congrArg (PowerSeries.coeff n) heq
    simpa only [q, PowerSeries.coeff_mk, PowerSeries.coeff_map,
      Complex.ofRealHom_eq_coe, p, ordinary] using h.symm
  refine ⟨hc, ?_, ?_⟩
  · intro z hz
    simpa only [hc] using hs z hz
  · filter_upwards [hneg] with n hn
    have hid := congrArg Complex.re (hi n).2.2.2.1
    have hb := (Complex.re_le_norm
      (FiniteSlitCircleDefect.outerCoefficient
        (FiniteSlitCompositionMoments.reciprocal head tail ell) R n)).trans (hi n).2.2.1
    change (c n).re = _ at hid
    rw [← hc n] at hid
    simp only [Complex.ofReal_re, Complex.add_re] at hid
    linarith

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryCoefficients
