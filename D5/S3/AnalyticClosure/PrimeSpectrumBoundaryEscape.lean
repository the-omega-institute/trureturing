/- GID: D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normalized prime heat curve has infinite variation at its critical endpoint. -/

import Mathlib
import D5.S3.AnalyticClosure.PrimeSpectrumHeatL2

/-! The actual prime heat curve escapes every strong limit at its critical endpoint. -/

namespace D5.S3.AnalyticClosure.PrimeSpectrumBoundaryEscape

open Filter
open scoped Topology
open D5.S3.AnalyticClosure.PrimeSpectrumHeatL2
open D5.S3.AnalyticClosure.PrimeSpectrumBoundaryDivergent
open D5.S3.Midline.UniversalHeatTrace

noncomputable section

/-- The actual prime heat coefficient vector at half the real trace parameter.
The zero value outside its open Hilbert domain is only a total extension. -/
def primeHeatVector (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1)) (σ : ℝ) :
    lp (fun _ : Nat.Primes × Nat => ℂ) 2 :=
  if hσ : 1 / b0 < σ then
    ⟨heatCoefficient (primeSpectrum beta) (((σ / 2 : ℝ) : ℂ)),
      heat_coefficient_mem_of_abscissa (primeSpectrum beta) (1 / b0)
        (prime_spectrum_boundary_divergent beta b0 h0 h1 h2).1 _
        (by simp only [Complex.ofReal_re]; linarith)⟩
  else 0

private theorem prime_heat_vector_apply (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1))
    (σ : ℝ) (hσ : 1 / b0 < σ) (a : Nat.Primes × Nat) :
    primeHeatVector beta b0 h0 h1 h2 σ a =
      heatCoefficient (primeSpectrum beta) (((σ / 2 : ℝ) : ℂ)) a := by
  simp only [primeHeatVector, dite_eq_left hσ]

private theorem prime_heat_vector_norm_sq (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1))
    (σ : ℝ) (hσ : 1 / b0 < σ) :
    ‖primeHeatVector beta b0 h0 h1 h2 σ‖ ^ 2 =
      ∑' a : Nat.Primes × Nat, Real.exp (-σ * primeSpectrum beta a) := by
  calc
    _ = ‖primeHeatVector beta b0 h0 h1 h2 σ‖ ^ (2 : ℝ) := (Real.rpow_two _).symm
    _ = ∑' a : Nat.Primes × Nat,
        ‖primeHeatVector beta b0 h0 h1 h2 σ a‖ ^ (2 : ℝ) :=
      lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) _
    _ = _ := by
      apply tsum_congr
      intro a
      rw [prime_heat_vector_apply beta b0 h0 h1 h2 σ hσ a,
        heatCoefficient_norm, Real.rpow_two, pow_two, ← Real.exp_add]
      congr 1
      simp only [Complex.ofReal_re]
      ring

private theorem prime_heat_vector_ne_zero (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1))
    (σ : ℝ) (hσ : 1 / b0 < σ) :
    primeHeatVector beta b0 h0 h1 h2 σ ≠ 0 := by
  intro hz
  let a : Nat.Primes × Nat := (⟨2, by norm_num⟩, 0)
  have he := congrArg (fun x : lp (fun _ : Nat.Primes × Nat => ℂ) 2 => x a) hz
  rw [prime_heat_vector_apply beta b0 h0 h1 h2 σ hσ a] at he
  exact Complex.exp_ne_zero _ he

/-- Boundary divergence forces the actual real prime heat trace to grow
without bound from the right; the total tsum at the endpoint is not used. -/
theorem prime_spectrum_heat_trace_tendsto_atTop (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1)) :
    Tendsto (fun σ : ℝ =>
      ∑' a : Nat.Primes × Nat, Real.exp (-σ * primeSpectrum beta a))
      (𝓝[>] (1 / b0)) atTop := by
  have hab := prime_spectrum_boundary_divergent beta b0 h0 h1 h2
  apply tendsto_atTop.mpr
  intro K
  have hfinite : ∃ u : Finset (Nat.Primes × Nat),
      K < ∑ a ∈ u, Real.exp (-(1 / b0) * primeSpectrum beta a) := by
    by_contra hn
    push Not at hn
    exact hab.2 (summable_of_sum_le (fun a => (Real.exp_pos _).le) hn)
  obtain ⟨u, hu⟩ := hfinite
  have hc : Continuous (fun σ : ℝ =>
      ∑ a ∈ u, Real.exp (-σ * primeSpectrum beta a)) := by fun_prop
  have he : ∀ᶠ σ in 𝓝[>] (1 / b0),
      K < ∑ a ∈ u, Real.exp (-σ * primeSpectrum beta a) :=
    ((hc.tendsto (1 / b0)).eventually_const_lt hu).filter_mono nhdsWithin_le_nhds
  filter_upwards [he, self_mem_nhdsWithin] with σ hfin hσ
  exact hfin.le.trans ((hab.1.1 σ hσ).sum_le_tsum u
    (fun a _ => (Real.exp_pos _).le))

/-- The unnormalized prime heat vector has diverging Hilbert norm at the
critical right endpoint. -/
theorem prime_spectrum_heat_norm_tendsto_atTop (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1)) :
    Tendsto (fun σ : ℝ => ‖primeHeatVector beta b0 h0 h1 h2 σ‖)
      (𝓝[>] (1 / b0)) atTop := by
  have hs := Real.tendsto_sqrt_atTop.comp
    (prime_spectrum_heat_trace_tendsto_atTop beta b0 h0 h1 h2)
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  dsimp only [Function.comp_apply]
  rw [← prime_heat_vector_norm_sq beta b0 h0 h1 h2 σ hσ,
    Real.sqrt_sq (norm_nonneg _)]

private theorem normalized_prime_heat_coordinate_tendsto_zero
    (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1)) (a : Nat.Primes × Nat) :
    Tendsto (fun σ : ℝ =>
      NormedSpace.normalize (primeHeatVector beta b0 h0 h1 h2 σ) a)
      (𝓝[>] (1 / b0)) (𝓝 0) := by
  have hi := (prime_spectrum_heat_norm_tendsto_atTop beta b0 h0 h1 h2).inv_tendsto_atTop
  have hc : Continuous (fun σ : ℝ =>
      heatCoefficient (primeSpectrum beta) (((σ / 2 : ℝ) : ℂ)) a) := by
    unfold heatCoefficient
    fun_prop
  have hcoord : Tendsto (fun σ : ℝ =>
      heatCoefficient (primeSpectrum beta) (((σ / 2 : ℝ) : ℂ)) a)
      (𝓝[>] (1 / b0))
      (𝓝 (heatCoefficient (primeSpectrum beta) ((((1 / b0) / 2 : ℝ) : ℂ)) a)) :=
    (hc.tendsto (1 / b0)).mono_left nhdsWithin_le_nhds
  have hm := hi.smul hcoord
  simp only [zero_smul] at hm
  apply hm.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  simp only [NormedSpace.normalize, lp.coeFn_smul, Pi.smul_apply,
    prime_heat_vector_apply beta b0 h0 h1 h2 σ hσ a]
  rfl

/-- Normalization preserves unit norm while every fixed prime coordinate
vanishes, so the actual normalized vector has no strong Hilbert limit. -/
theorem prime_spectrum_normalized_heat_not_tendsto (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1))
    (x : lp (fun _ : Nat.Primes × Nat => ℂ) 2) :
    ¬ Tendsto (fun σ : ℝ =>
        NormedSpace.normalize (primeHeatVector beta b0 h0 h1 h2 σ))
      (𝓝[>] (1 / b0)) (𝓝 x) := by
  intro hx
  have hzero : x = 0 := by
    apply lp.ext
    funext a
    have he := ((lp.lipschitzWith_one_eval
      (E := fun _ : Nat.Primes × Nat => ℂ) 2 a).continuous.tendsto x).comp hx
    exact tendsto_nhds_unique he
      (normalized_prime_heat_coordinate_tendsto_zero beta b0 h0 h1 h2 a)
  have hunit : ∀ᶠ σ in 𝓝[>] (1 / b0),
      ‖NormedSpace.normalize (primeHeatVector beta b0 h0 h1 h2 σ)‖ = 1 := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact NormedSpace.norm_normalize (prime_heat_vector_ne_zero beta b0 h0 h1 h2 σ hσ)
  have hnorm : Tendsto (fun σ : ℝ =>
      ‖NormedSpace.normalize (primeHeatVector beta b0 h0 h1 h2 σ)‖)
      (𝓝[>] (1 / b0)) (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hunit] with σ hσ
    exact hσ.symm
  have heq := tendsto_nhds_unique hx.norm hnorm
  norm_num [hzero] at heq

/-- The actual normalized Hilbert curve has infinite metric variation on every
interval ending at its critical boundary. This does not assert a derivative
formula or global Riemannian completeness. -/
theorem prime_spectrum_normalized_heat_eVariationOn_eq_top
    (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1))
    (c : ℝ) (hc : 1 / b0 < c) :
    eVariationOn (fun σ : ℝ =>
      NormedSpace.normalize (primeHeatVector beta b0 h0 h1 h2 σ))
      (Set.Ioo (1 / b0) c) = ⊤ := by
  by_contra hn
  have hv : BoundedVariationOn (fun σ : ℝ =>
      NormedSpace.normalize (primeHeatVector beta b0 h0 h1 h2 σ))
      (Set.Ioo (1 / b0) c) := hn
  obtain ⟨x, hx⟩ := hv.exists_tendsto_right (1 / b0)
  have hs : Set.Ioo (1 / b0) c ∩ Set.Ioi (1 / b0) =
      Set.Iio c ∩ Set.Ioi (1 / b0) := by
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio]
    tauto
  rw [hs, nhdsWithin_inter_of_mem
    (nhdsWithin_le_nhds (Iio_mem_nhds hc))] at hx
  exact prime_spectrum_normalized_heat_not_tendsto beta b0 h0 h1 h2 x hx

#print axioms prime_spectrum_heat_trace_tendsto_atTop
#print axioms prime_spectrum_heat_norm_tendsto_atTop
#print axioms prime_spectrum_normalized_heat_not_tendsto
#print axioms prime_spectrum_normalized_heat_eVariationOn_eq_top

end

end D5.S3.AnalyticClosure.PrimeSpectrumBoundaryEscape
