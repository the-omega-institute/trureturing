/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineCertificateEvaluation
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Grouped affine origins certify the polynomial after the spectral substitution. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.GroupedAffineMasks
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! At degree `start + x`, affine negative rates represent powers of the two
spectral ratios and their degree powers. -/

open scoped BigOperators
open Polynomial

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

open private negativeRate
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedOrigins

private def rateMonomial (start : ℕ) (a : AffineRate) (r R : ℝ) : ℝ :=
  r^(a.1 - start*a.2) * R^a.2

noncomputable def Certificate.evaluate (c : Certificate) (start : ℕ)
    (x r t R T : ℝ) : ℝ :=
  ∑ i, (c.weight i).eval₂ (Int.castRingHom ℝ) x *
    rateMonomial start (c.rateU i) r R * rateMonomial start (c.rateV i) t T

private theorem rateMonomial_exp (start : ℕ) (a : AffineRate)
    (ha : start * a.2 ≤ a.1) (x u : ℝ) :
    rateMonomial start a (Real.exp (-u)) (Real.exp (-((start : ℝ) + x)*u)) =
      Real.exp (negativeRate a x * u) := by
  simp only [rateMonomial, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  simp only [negativeRate, Nat.cast_sub ha, Nat.cast_mul]
  ring

theorem Certificate.nonneg_evaluate_of_rows (c : Certificate) (start width digits : ℕ)
    (hu : ∀ i : c.Index, start*(c.rateU i).2 ≤ (c.rateU i).1)
    (hv : ∀ i : c.Index, start*(c.rateV i).2 ≤ (c.rateV i).1)
    (hrates : c.checkRates = true)
    (hrows : ∀ k < c.rootsU.length, c.checkRow width digits k = true)
    (hbounds : ∀ k < c.rootsU.length, ∀ l < c.rootsV.length,
      let P := c.origin k l
      P.natDegree < digits ∧
        (∀ j, -(2 : ℤ)^width ≤ P.coeff j ∧ P.coeff j < (2 : ℤ)^width))
    {x r t : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hr₁ : r ≤ 1) (ht : 0 < t) (ht₁ : t ≤ 1) :
    0 ≤ c.evaluate start x r t (r^((start : ℝ) + x)) (t^((start : ℝ) + x)) := by
  let u := -Real.log r
  let v := -Real.log t
  have hu₀ : 0 ≤ u := neg_nonneg.mpr (Real.log_nonpos hr.le hr₁)
  have hv₀ : 0 ≤ v := neg_nonneg.mpr (Real.log_nonpos ht.le ht₁)
  have h := nonneg_of_mixed_origin_masks c.weight c.rateU c.rateV c.rootsU c.rootsV
    (fun i => (c.rates_mem hrates i).1) (fun i => (c.rates_mem hrates i).2)
    (c.mixedOrigin_checks_of_rows width digits hrates hrows hbounds) x u v hx hu₀ hv₀
  have hru : r = Real.exp (-u) := by simp [u, Real.exp_log hr]
  have htv : t = Real.exp (-v) := by simp [v, Real.exp_log ht]
  have hR : r^((start : ℝ) + x) = Real.exp (-((start : ℝ) + x)*u) := by
    rw [Real.rpow_def_of_pos hr]
    congr 1
    dsimp [u]
    ring
  have hT : t^((start : ℝ) + x) = Real.exp (-((start : ℝ) + x)*v) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    dsimp [v]
    ring
  rw [hR, hT, hru, htv]
  unfold Certificate.evaluate
  simp_rw [rateMonomial_exp start _ (hu _), rateMonomial_exp start _ (hv _)]
  simpa only [Real.exp_add, mul_assoc] using h

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
