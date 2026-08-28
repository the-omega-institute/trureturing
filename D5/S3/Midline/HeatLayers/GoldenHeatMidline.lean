/- GID: D5/S3/Midline/HeatLayers/GoldenHeatMidline
   generality: I
   mirror-B: D5/B/S3/Midline/HeatLayers/GoldenHeatMidline
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unify the six exact midline characterizations of the golden heat spectrum. -/

import D5.S3.Midline.GoldenHeatBoundary
import D5.S3.Midline.UniversalHeatTrace

/- Provenance: Native assembly over frozen repository results and pinned mathlib.
   Search receipt (2026-08-26): the Midline family supplies the canonical objects
   `goldenSpectrum`, `heatCoefficient`, `heatTrace`, `halfDensityCoefficient`, and
   `KernelResonant`, together with the exact reflection, half-density, boundary,
   and resonance characterizations. No frozen declaration states all six golden
   clauses together. Pinned mathlib supplies `lp.norm_rpow_eq_tsum` for the one
   instance-specific norm calculation. No new source-object definition is made. -/

namespace D5.S3.Midline.HeatLayers.GoldenHeatMidline

open scoped ComplexConjugate

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Midline.GoldenHeatBoundary
open D5.S3.Midline.GoldenHeatSpectrum
open D5.S3.Midline.UniversalHeatTrace

noncomputable section

private theorem golden_abscissa_half :
    (1 / Real.goldenRatio ^ 2) / 2 =
      1 / (2 * Real.goldenRatio ^ 2) := by
  field_simp [ne_of_gt Real.goldenRatio_pos]

private theorem goldenSpectrum_nonnegative :
    ∀ pk : Nat.Primes × Nat, 0 ≤ goldenSpectrum pk := by
  intro pk
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_one : 1 < Real.sqrt 5 := by nlinarith
  have hbeta_growth := o5_beta_growth (pk.2 + 1)
  have hbeta : 0 < o5Beta (pk.2 + 1) := by
    have hk : 1 ≤ ((pk.2 + 1 : Nat) : ℝ) := by norm_num
    have hphi_inv : 0 < 1 / Real.goldenRatio := by positivity
    nlinarith
  have hlog : 0 < Real.log (pk.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pk.1.prop.one_lt)
  exact (mul_pos hbeta hlog).le

private theorem goldenSpectrum_nontrivial :
    ∃ pk : Nat.Primes × Nat, goldenSpectrum pk ≠ 0 := by
  let p : Nat.Primes := ⟨2, by norm_num⟩
  refine ⟨(p, 0), ne_of_gt ?_⟩
  rw [goldenSpectrum, Nat.zero_add, o5_beta_power_law.1]
  exact mul_pos (sq_pos_of_pos Real.goldenRatio_pos)
    (Real.log_pos (by norm_num))

private theorem golden_heat_norm_sq
    (σ t : ℝ) (hσ : 1 / (2 * Real.goldenRatio ^ 2) < σ) :
    let x : lp (fun _ : Nat.Primes × Nat => ℂ) 2 :=
      ⟨heatCoefficient goldenSpectrum
          ((σ : ℂ) + Complex.I * (t : ℂ)),
        (golden_heat_l2_iff
          ((σ : ℂ) + Complex.I * (t : ℂ))).2 (by simpa using hσ)⟩
    ((‖x‖ ^ 2 : ℝ) : ℂ) =
      heatTrace goldenSpectrum ((2 * σ : ℝ) : ℂ) := by
  let x : lp (fun _ : Nat.Primes × Nat => ℂ) 2 :=
    ⟨heatCoefficient goldenSpectrum
        ((σ : ℂ) + Complex.I * (t : ℂ)),
      (golden_heat_l2_iff
        ((σ : ℂ) + Complex.I * (t : ℂ))).2 (by simpa using hσ)⟩
  have hlp : ‖x‖ ^ (2 : ℝ) =
      ∑' a : Nat.Primes × Nat, ‖x a‖ ^ (2 : ℝ) := by
    exact lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) x
  have hsum : Summable (fun a : Nat.Primes × Nat =>
      Real.exp (-(2 * σ) * goldenSpectrum a)) := by
    apply golden_heat_abscissa.1 (2 * σ)
    have hσ' : (1 / Real.goldenRatio ^ 2) / 2 < σ := by
      rw [golden_abscissa_half]
      exact hσ
    linarith
  have hcoord (a : Nat.Primes × Nat) :
      ‖x a‖ ^ (2 : ℝ) = Real.exp (-(2 * σ) * goldenSpectrum a) := by
    change ‖heatCoefficient goldenSpectrum
      ((σ : ℂ) + Complex.I * (t : ℂ)) a‖ ^ (2 : ℝ) = _
    rw [heatCoefficient_norm, Real.rpow_two, pow_two, ← Real.exp_add]
    congr 1
    simp
    ring
  have hnorm : ‖x‖ ^ 2 = ∑' a : Nat.Primes × Nat,
      Real.exp (-(2 * σ) * goldenSpectrum a) := by
    calc
      ‖x‖ ^ 2 = ‖x‖ ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ = ∑' a : Nat.Primes × Nat, ‖x a‖ ^ (2 : ℝ) := hlp
      _ = ∑' a : Nat.Primes × Nat,
          Real.exp (-(2 * σ) * goldenSpectrum a) := tsum_congr hcoord
  change ((‖x‖ ^ 2 : ℝ) : ℂ) = _
  rw [hnorm, heatTrace]
  change Complex.ofRealCLM
      (∑' a : Nat.Primes × Nat,
        Real.exp (-(2 * σ) * goldenSpectrum a)) = _
  rw [Complex.ofRealCLM.map_tsum hsum]
  apply tsum_congr
  intro a
  change ((Real.exp (-(2 * σ) * goldenSpectrum a) : ℝ) : ℂ) = _
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The golden heat spectrum has one and the same midline as reflection-fixed
parameters, half-density unitary parameters, the exact L2 boundary, and
self-resonant parameters. Its labeled norm is vertical-invariant, and every
parameter has exactly the conjugate-reflection resonance partner displayed in
the final clause. -/
theorem golden_heat_sixfold_midline :
    (∀ s : ℂ,
      (s = ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ) - conj s ↔
        s.re = 1 / (2 * Real.goldenRatio ^ 2))) ∧
    (∀ s : ℂ,
      (∀ a : Nat.Primes × Nat,
        ‖halfDensityCoefficient goldenSpectrum
          (1 / Real.goldenRatio ^ 2) s a‖ = 1) ↔
        s.re = 1 / (2 * Real.goldenRatio ^ 2)) ∧
    (∀ (σ t : ℝ) (hσ : 1 / (2 * Real.goldenRatio ^ 2) < σ),
      let x : lp (fun _ : Nat.Primes × Nat => ℂ) 2 :=
        ⟨heatCoefficient goldenSpectrum
            ((σ : ℂ) + Complex.I * (t : ℂ)),
          (golden_heat_l2_iff
            ((σ : ℂ) + Complex.I * (t : ℂ))).2 (by simpa using hσ)⟩
      ((‖x‖ ^ 2 : ℝ) : ℂ) =
        heatTrace goldenSpectrum ((2 * σ : ℝ) : ℂ)) ∧
    (∀ s : ℂ,
      Memℓp (heatCoefficient goldenSpectrum s) 2 ↔
        1 / (2 * Real.goldenRatio ^ 2) < s.re) ∧
    (∀ s : ℂ,
      KernelResonant (1 / Real.goldenRatio ^ 2) s s ↔
        s.re = 1 / (2 * Real.goldenRatio ^ 2)) ∧
    (∀ s w : ℂ,
      KernelResonant (1 / Real.goldenRatio ^ 2) s w ↔
        w = ((1 / Real.goldenRatio ^ 2 : ℝ) : ℂ) - conj s) := by
  refine ⟨?_, ?_, ?_, golden_heat_l2_iff, ?_, ?_⟩
  · intro s
    have h := (reflection_center_eq_abscissa_iff
      (1 / Real.goldenRatio ^ 2) (1 / Real.goldenRatio ^ 2)).2 rfl s
    rwa [golden_abscissa_half] at h
  · intro s
    have h := half_density_unit_modulus_iff goldenSpectrum
      (1 / Real.goldenRatio ^ 2) goldenSpectrum_nonnegative
      goldenSpectrum_nontrivial s
    rwa [golden_abscissa_half] at h
  · exact golden_heat_norm_sq
  · intro s
    have h := (resonance_partner_spec
      (1 / Real.goldenRatio ^ 2) s s).2.1
    rwa [golden_abscissa_half] at h
  · intro s w
    exact (resonance_partner_spec (1 / Real.goldenRatio ^ 2) s w).1

end

end D5.S3.Midline.HeatLayers.GoldenHeatMidline
