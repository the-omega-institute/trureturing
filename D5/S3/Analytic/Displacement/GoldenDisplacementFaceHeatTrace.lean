/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace
   generality: I
   mirror-B: D5/B/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Face heat trace equals the germ product; abscissa bracketed in the golden window. -/

import D5.S1.Deficit.Displacement.GoldenContractionRadicalBound
import D5.S3.Analytic.Displacement.GoldenDisplacementComplexEulerProduct
import D5.S3.Midline.GoldenHeatSpectrum

/- Provenance: Native proof over pinned mathlib. The face identities reuse the
   repository's closed forms, prime-power hidden-product formula, and frozen
   complex germ section. The two divergence arguments reuse Mathlib's exact
   prime rpow criterion and the repository's contraction radical bound. -/

open D5.S1.Deficit.AlmostAdditivity
open D5.S1.Deficit.DoubleFaceLength
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Midline.GoldenHeatSpectrum
open D5.S3.Midline.UniversalHeatTrace
open GoldenContractionRadicalBound
open GoldenDesubstitutionClosedForms
open GoldenDesubstitutionLength
open GoldenDisplacementComplexEulerProduct
open GoldenDisplacementEulerProduct
open GoldenSubstitutionOrbit
open Filter
open scoped Topology

namespace GoldenDisplacementFaceHeatTrace

noncomputable section

/-- Expansion-face lengths, with the zero natural index shifted away. -/
noncomputable def faceLength : ℕ → ℝ := fun k => lambdaPlus (k + 1)

/-- Contraction-face lengths, with the zero natural index shifted away. -/
noncomputable def contractionLength : ℕ → ℝ := fun k => lambdaMinus (k + 1)

/-- On prime powers, the expansion-face length is exactly the golden heat spectrum. -/
theorem lambdaPlus_prime_pow_eq_goldenSpectrum (p : Nat.Primes) (k : ℕ) :
    lambdaPlus ((p : ℕ) ^ (k + 1)) = goldenSpectrum (p, k) := by
  have hne : (p : ℕ) ^ (k + 1) ≠ 0 := pow_ne_zero _ p.prop.ne_zero
  rw [lambdaPlus_eq_log_nS_sub_goldenConj_log _ hne,
    nS_prime_pow p.prop (k + 1)]
  push_cast
  simp only [goldenSpectrum]
  rw [Real.log_pow, Real.log_pow,
    o5_beta_eq_substitution_start_sub_conjugate]
  ring

/-- The positive-index complex displacement germ is the expansion-face heat coefficient. -/
theorem dTermC_germ_eq_heatCoefficient (s : ℂ) (k : ℕ) :
    dTermC s (-((Real.goldenConj : ℂ)) * s) (k + 1) =
      heatCoefficient faceLength s k := by
  have hn : k + 1 ≠ 0 := Nat.succ_ne_zero k
  have hnS : (nS (k + 1) : ℂ) ≠ 0 := by
    exact_mod_cast nS_ne_zero (k + 1)
  have hnat : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hn
  rw [dTermC, if_neg hn, heatCoefficient, faceLength,
    lambdaPlus_eq_log_nS_sub_goldenConj_log _ hn,
    Complex.cpow_def_of_ne_zero hnS, Complex.cpow_def_of_ne_zero hnat,
    ← Complex.natCast_log, ← Complex.natCast_log, ← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- The expansion-face heat trace is the convergent golden displacement germ product. -/
theorem heat_trace_eq_complex_displacement_germ_product {s : ℂ}
    (hs : 1 < Real.goldenRatio * s.re) :
    heatTrace faceLength s =
      ∏' p : Nat.Primes, (∑' e : ℕ, (p : ℂ) ^ (-s * (o5Beta e : ℂ))) := by
  have hsnonneg : 0 ≤ s.re := by
    nlinarith [Real.goldenRatio_pos]
  have hsection :
      (s + (-((Real.goldenConj : ℂ)) * s)).re = Real.goldenRatio * s.re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    rw [← Real.one_sub_goldenRatio]
    ring
  have hsum : Summable (fun n : ℕ =>
      dTermC s (-((Real.goldenConj : ℂ)) * s) n) :=
    (dterm_c_summable hsnonneg (by rwa [hsection])).of_norm
  rw [heatTrace]
  calc
    (∑' k : ℕ, Complex.exp (-s * (faceLength k : ℂ))) =
        ∑' k : ℕ, dTermC s (-((Real.goldenConj : ℂ)) * s) (k + 1) :=
      tsum_congr fun k => by
        simpa only [heatCoefficient] using (dTermC_germ_eq_heatCoefficient s k).symm
    _ = ∑' n : ℕ, dTermC s (-((Real.goldenConj : ℂ)) * s) n := by
      rw [hsum.tsum_eq_zero_add, dterm_c_zero, zero_add]
    _ = ∏' p : Nat.Primes, (∑' e : ℕ, (p : ℂ) ^ (-s * (o5Beta e : ℂ))) :=
      (complex_displacement_germ_section hs).symm

/-- Expansion-face heat is summable beyond the larger endpoint of the golden window. -/
theorem summable_faceLength_heat {σ : ℝ} (hσ : 1 / Real.goldenRatio < σ) :
    Summable (fun k => Real.exp (-σ * faceLength k)) := by
  have hσnonneg : 0 ≤ σ := by
    have hinv : 0 < 1 / Real.goldenRatio := by positivity
    linarith
  have hconv : 1 < Real.goldenRatio * σ := by
    have := (div_lt_iff₀ Real.goldenRatio_pos).mp hσ
    nlinarith
  have hsection :
      (((σ : ℂ) + (-((Real.goldenConj : ℂ)) * (σ : ℂ))).re) =
        Real.goldenRatio * σ := by
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    rw [← Real.one_sub_goldenRatio]
    ring
  have hsum := (dterm_c_summable (s := (σ : ℂ))
    (w := -((Real.goldenConj : ℂ)) * (σ : ℂ)) hσnonneg (by rwa [hsection])).comp_injective
      Nat.succ_injective
  refine hsum.congr fun k => ?_
  change ‖dTermC (σ : ℂ) (-((Real.goldenConj : ℂ)) * (σ : ℂ)) (k + 1)‖ = _
  rw [dTermC_germ_eq_heatCoefficient, heatCoefficient_norm]
  simp

/-- Expansion-face heat is not summable at or below the smaller golden endpoint. -/
theorem not_summable_faceLength_heat {σ : ℝ}
    (hσ : σ ≤ 1 / Real.goldenRatio ^ 2) :
    ¬Summable (fun k => Real.exp (-σ * faceLength k)) := by
  intro hsum
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 1) := by
    intro p q hpq
    apply Subtype.ext
    have hp := p.prop.pos
    have hq := q.prop.pos
    dsimp at hpq
    omega
  have hsub : Summable (fun p : Nat.Primes =>
      Real.exp (-σ * faceLength ((p : ℕ) - 1))) :=
    hsum.comp_injective hinj
  have hface (p : Nat.Primes) :
      faceLength ((p : ℕ) - 1) =
        Real.goldenRatio ^ 2 * Real.log (p : ℝ) := by
    have hsucc : (p : ℕ) - 1 + 1 = (p : ℕ) :=
      Nat.sub_add_cancel p.prop.one_le
    rw [faceLength, hsucc]
    simpa [goldenSpectrum, o5_beta_power_law.1] using
      lambdaPlus_prime_pow_eq_goldenSpectrum p 0
  have hrpow : Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-σ * Real.goldenRatio ^ 2)) := by
    refine hsub.congr fun p => ?_
    rw [hface, Real.rpow_def_of_pos]
    · congr 1
      ring
    · exact_mod_cast p.prop.pos
  have hexponent : -σ * Real.goldenRatio ^ 2 < -1 :=
    Nat.Primes.summable_rpow.mp hrpow
  have hphi : 0 < Real.goldenRatio ^ 2 := sq_pos_of_pos Real.goldenRatio_pos
  have hcritical : σ * Real.goldenRatio ^ 2 ≤ 1 :=
    (le_div_iff₀ hphi).mp hσ
  linarith

/-- Any heat abscissa for the expansion face lies in the honest golden window. -/
theorem faceLength_heat_abscissa_bracket {α : ℝ}
    (h : IsHeatAbscissa faceLength α) :
    1 / Real.goldenRatio ^ 2 ≤ α ∧ α ≤ 1 / Real.goldenRatio := by
  constructor
  · by_contra hbelow
    have hlt : α < 1 / Real.goldenRatio ^ 2 := lt_of_not_ge hbelow
    let σ := (α + 1 / Real.goldenRatio ^ 2) / 2
    have hασ : α < σ := by dsimp [σ]; linarith
    have hσcritical : σ ≤ 1 / Real.goldenRatio ^ 2 := by dsimp [σ]; linarith
    exact not_summable_faceLength_heat hσcritical (h.1 σ hασ)
  · by_contra habove
    have hlt : 1 / Real.goldenRatio < α := lt_of_not_ge habove
    let σ := (1 / Real.goldenRatio + α) / 2
    have hcriticalσ : 1 / Real.goldenRatio < σ := by dsimp [σ]; linarith
    have hσα : σ < α := by dsimp [σ]; linarith
    exact h.2 σ hσα (summable_faceLength_heat hcriticalσ)

/-- Contraction-face heat coefficients never form a summable sequence. -/
theorem not_summable_contraction_face_heat (s : ℂ) :
    ¬Summable (heatCoefficient contractionLength s) := by
  intro hsum
  let index : ℕ → ℕ := fun e => 2 ^ (e + 1) - 1
  have hindex : Function.Injective index := by
    intro a b hab
    have hpa : 0 < 2 ^ (a + 1) := pow_pos (by norm_num) _
    have hpb : 0 < 2 ^ (b + 1) := pow_pos (by norm_num) _
    have hpows : 2 ^ (a + 1) = 2 ^ (b + 1) := by
      dsimp [index] at hab
      omega
    have hexponents := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpows
    omega
  have hsub := hsum.comp_injective hindex
  let C : ℝ := Real.goldenRatio⁻¹ * Real.log 2
  let δ : ℝ := Real.exp (-|s.re| * C)
  have hδ : 0 < δ := Real.exp_pos _
  have hlower (e : ℕ) :
      δ ≤ ‖heatCoefficient contractionLength s (index e)‖ := by
    have hpow : 2 ^ (e + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hrad : primeRadical (2 ^ (e + 1)) = 2 := by
      rw [primeRadical, Nat.primeFactors_prime_pow (by omega) Nat.prime_two]
      simp
    have hsucc : index e + 1 = 2 ^ (e + 1) := by
      dsimp [index]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpow)
    have hbound : |contractionLength (index e)| ≤ C := by
      rw [contractionLength, hsucc]
      simpa [C, hrad] using
        (abs_lambdaMinus_le_goldenRatio_inv_log_primeRadical hpow)
    have hprod : |s.re * contractionLength (index e)| ≤ |s.re| * C := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hbound (abs_nonneg s.re)
    rw [heatCoefficient_norm]
    apply Real.exp_le_exp.mpr
    calc
      -|s.re| * C = -(|s.re| * C) := by ring
      _ ≤ -|s.re * contractionLength (index e)| := neg_le_neg hprod
      _ ≤ -s.re * contractionLength (index e) := by
        simpa only [abs_mul, abs_neg] using
          neg_abs_le (-s.re * contractionLength (index e))
  have htend : Tendsto (fun e =>
      ‖heatCoefficient contractionLength s (index e)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, norm_zero] using hsub.tendsto_atTop_zero.norm
  have hevent : ∀ᶠ e in atTop,
      ‖heatCoefficient contractionLength s (index e)‖ < δ :=
    htend.eventually_lt_const hδ
  rcases Filter.eventually_atTop.1 hevent with ⟨N, hN⟩
  exact (not_lt_of_ge (hlower N)) (hN N le_rfl)

example : faceLength 0 = lambdaPlus 1 := by rfl

end

end GoldenDisplacementFaceHeatTrace
