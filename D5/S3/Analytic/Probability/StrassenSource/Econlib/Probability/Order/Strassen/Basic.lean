/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Convex.Basic
public import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Martingale couplings and the easy direction of Strassen's theorem

This file defines the **martingale coupling** of two real-valued probability laws and proves the
easy direction of **Strassen's theorem**: A martingale coupling whose marginals are supported on a
common compact interval witnesses the convex order between those marginals.

## Main definitions

* `IsMartingaleCoupling μ ν π` — `π : ProbDist (ℝ × ℝ)` is a martingale coupling of `μ, ν`: Its
  marginals are `μ` and `ν`, both coordinates are integrable, and the tested identity
  `∫ (y - x) · φ(x) dπ(x, y) = 0` holds for every bounded measurable `φ`.

## Main statements

* `IsMartingaleCoupling.mean_eq` — marginals of a martingale coupling have equal means.
* `IsMartingaleCoupling.convex_expect_le` — easy direction of Strassen: A martingale coupling whose
  marginals are supported on `[a, b]` implies the convex order on `[a, b]`.
* `IsMartingaleCoupling.convexOrderOnIcc` — repackages `convex_expect_le` together with equal means
  and support as `ConvexOrderOnIcc a b μ ν`.

## Notes

The hard direction (existence of a martingale coupling from the convex order) and the full
equivalence `strassen_iff` are assembled in the top-level `Econlib.Probability.Order.Strassen`.

## References

* Strassen, V. 1965. “The Existence of Probability Measures with Given Marginals.” *The Annals of
  Mathematical Statistics* 36 (2): 423–39. [https://doi.org/10.1214/aoms/1177700153](https://doi.org/10.1214/aoms/1177700153).

## Tags

strassen, convex order, martingale coupling, conditional expectation
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Econlib.Probability

/-- A **martingale coupling** of real-valued probability laws `μ, ν`: A joint law `π` on `ℝ × ℝ`
whose `Prod.fst`-marginal is `μ`, `Prod.snd`-marginal is `ν`, both coordinates are `π`-integrable,
and the second coordinate is conditionally mean-equal to the first.

The martingale condition is stated in tested form: For every bounded measurable `φ : ℝ → ℝ`,
`∫ (y - x) φ(x) dπ(x, y) = 0`. Combined with the marginal conditions, this is equivalent to
`𝔼π[Y ∣ X] = X` almost surely. -/
structure IsMartingaleCoupling (μ ν : ProbDist ℝ) (π : ProbDist (ℝ × ℝ)) : Prop where
  /-- The first marginal of `π` is `μ`. -/
  fst_marginal : ProbDist.map π Prod.fst measurable_fst = μ
  /-- The second marginal of `π` is `ν`. -/
  snd_marginal : ProbDist.map π Prod.snd measurable_snd = ν
  /-- The first coordinate has finite expectation under `π`. -/
  integrable_fst : Integrable (fun p : ℝ × ℝ => p.1) π.toMeasure
  /-- The second coordinate has finite expectation under `π`. -/
  integrable_snd : Integrable (fun p : ℝ × ℝ => p.2) π.toMeasure
  /-- Tested martingale property: For every bounded measurable `φ`, `∫ (y - x) φ(x) dπ(x, y) = 0`.
  Together with integrability of the coordinates, this encodes `𝔼[Y ∣ X] = X`. -/
  martingale : ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
    ∫ p, (p.2 - p.1) * φ p.1 ∂π.toMeasure = 0

namespace IsMartingaleCoupling

variable {μ ν : ProbDist ℝ} {π : ProbDist (ℝ × ℝ)}

/-- The first marginal of a martingale coupling, at the `Measure` level. -/
lemma fst_measure (h : IsMartingaleCoupling μ ν π) :
    π.toMeasure.fst = μ.toMeasure := by
  have heq := congrArg (fun d : ProbDist ℝ => (d : Measure ℝ)) h.fst_marginal
  simpa [Measure.fst, ProbDist.map_toMeasure] using heq

/-- The second marginal of a martingale coupling, at the `Measure` level. -/
lemma snd_measure (h : IsMartingaleCoupling μ ν π) :
    π.toMeasure.snd = ν.toMeasure := by
  have heq := congrArg (fun d : ProbDist ℝ => (d : Measure ℝ)) h.snd_marginal
  simpa [Measure.snd, ProbDist.map_toMeasure] using heq

/-- Integrability of `id` against the first marginal, deduced from `integrable_fst`. -/
lemma integrable_id_fst (h : IsMartingaleCoupling μ ν π) :
    Integrable (fun x : ℝ => x) μ.toMeasure := by
  have hmap : μ.toMeasure = Measure.map Prod.fst π.toMeasure := by rw [← h.fst_measure]; rfl
  rw [hmap]
  refine (MeasureTheory.integrable_map_measure ?_ measurable_fst.aemeasurable).mpr ?_
  · exact (measurable_id).aestronglyMeasurable
  · exact h.integrable_fst

/-- **Conditional martingale identity.** For a martingale coupling `π` of `μ, ν`, the `condKernel`
of `π` has μ-a.e. fiber mean equal to the base point. -/
lemma ae_conditional_mean_eq (h : IsMartingaleCoupling μ ν π) :
    ∀ᵐ x ∂μ.toMeasure, ∫ y, y ∂(π.toMeasure.condKernel x) = x := by
  have hfst : π.toMeasure.fst = μ.toMeasure := h.fst_measure
  set K := π.toMeasure.condKernel with hK_def
  set Φ : ℝ → ℝ := fun x => (∫ y, y ∂(K x)) - x with hΦ_def
  -- Reduce to `Φ =ᵐ[μ] 0`.
  suffices h_ae : Φ =ᵐ[μ.toMeasure] 0 by
    filter_upwards [h_ae] with x hx
    linarith [show (∫ y, y ∂(K x)) - x = 0 from hx]
  -- Φ is integrable: inner integral is integrable via `Integrable.integral_condKernel`,
  -- minus integrable `id`.
  have h_id_int : Integrable (fun x : ℝ => x) μ.toMeasure := h.integrable_id_fst
  have h_inner_int : Integrable (fun x => ∫ y, y ∂K x) μ.toMeasure := by
    rw [← hfst]; exact h.integrable_snd.integral_condKernel
  have hΦ_int : Integrable Φ μ.toMeasure := h_inner_int.sub h_id_int
  -- Apply `ae_eq_zero_of_forall_setIntegral_eq_zero` testing against every measurable set.
  refine hΦ_int.ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _ => ?_
  -- Test the martingale condition at `g = indicator_s`.
  let g : ℝ → ℝ := Set.indicator s (fun _ => (1 : ℝ))
  have hg_meas : Measurable g := (measurable_const (a := (1 : ℝ))).indicator hs
  have hg_bdd : ∃ M, ∀ x, |g x| ≤ M := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ s
    · simp [g, Set.indicator_of_mem hx]
    · simp [g, Set.indicator_of_notMem hx]
  have hmart := h.martingale g hg_meas hg_bdd
  -- Technical chain: ∫ x in s, Φ x ∂μ = ∫ p, (p.2 - p.1) * g p.1 ∂π.
  -- (1) First piece via `setIntegral_condKernel_univ_right`.
  have h_first : ∫ x in s, (∫ y, y ∂(K x)) ∂μ.toMeasure
      = ∫ p in s ×ˢ (Set.univ : Set ℝ), p.2 ∂π.toMeasure := by
    rw [← hfst]
    exact MeasureTheory.Measure.setIntegral_condKernel_univ_right (ρ := π.toMeasure) hs
      h.integrable_snd.integrableOn
  -- (2) Second piece via `setIntegral_map`.
  have h_second : ∫ x in s, x ∂μ.toMeasure
      = ∫ p in s ×ˢ (Set.univ : Set ℝ), p.1 ∂π.toMeasure := by
    have h_map : μ.toMeasure = Measure.map Prod.fst π.toMeasure := by
      rw [← hfst]; rfl
    rw [h_map, MeasureTheory.setIntegral_map (f := fun x : ℝ => x) hs
      stronglyMeasurable_id.aestronglyMeasurable measurable_fst.aemeasurable,
      ← Set.prod_univ (β := ℝ)]
  -- Pull the subtraction out of the outer setIntegral.
  have h_sub_out : ∫ x in s, Φ x ∂μ.toMeasure
      = (∫ x in s, (∫ y, y ∂(K x)) ∂μ.toMeasure) - (∫ x in s, x ∂μ.toMeasure) := by
    simp only [hΦ_def]
    exact MeasureTheory.integral_sub h_inner_int.integrableOn h_id_int.integrableOn
  -- Pull the subtraction into a single `s × univ` setIntegral, then convert to a full
  -- integral with indicator.
  have h_sub_in : (∫ p in s ×ˢ (Set.univ : Set ℝ), p.2 ∂π.toMeasure) -
        (∫ p in s ×ˢ (Set.univ : Set ℝ), p.1 ∂π.toMeasure)
      = ∫ p, (p.2 - p.1) * g p.1 ∂π.toMeasure := by
    rw [← MeasureTheory.integral_sub h.integrable_snd.integrableOn
      h.integrable_fst.integrableOn]
    have h_prod_meas : MeasurableSet (s ×ˢ (Set.univ : Set ℝ)) :=
      hs.prod MeasurableSet.univ
    rw [← MeasureTheory.integral_indicator h_prod_meas]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    simp only [g, Set.indicator]
    by_cases hps : p.1 ∈ s
    · have : p ∈ s ×ˢ (Set.univ : Set ℝ) := ⟨hps, Set.mem_univ _⟩
      simp [this, hps]
    · have : p ∉ s ×ˢ (Set.univ : Set ℝ) := fun hp => hps hp.1
      simp [this, hps]
  rw [h_sub_out, h_first, h_second, h_sub_in, hmart]

/-- Marginals of a martingale coupling have equal means. -/
lemma mean_eq (h : IsMartingaleCoupling μ ν π) :
    μ.expect id = ν.expect id := by
  -- Martingale condition at `φ ≡ 1`: ∫ (p.2 - p.1) dπ = 0.
  have hmart := h.martingale (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by simp⟩
  simp only [mul_one] at hmart
  rw [MeasureTheory.integral_sub h.integrable_snd h.integrable_fst] at hmart
  -- Identify `μ.expect id` with `∫ p, p.1 ∂π` via `fst_marginal`.
  have hμ_int : μ.expect id = ∫ p, (p : ℝ × ℝ).1 ∂π.toMeasure := by
    rw [← h.fst_marginal,
      ProbDist.expect_map π Prod.fst measurable_fst id measurable_id.aestronglyMeasurable]
    rfl
  have hν_int : ν.expect id = ∫ p, (p : ℝ × ℝ).2 ∂π.toMeasure := by
    rw [← h.snd_marginal,
      ProbDist.expect_map π Prod.snd measurable_snd id measurable_id.aestronglyMeasurable]
    rfl
  linarith [hμ_int, hν_int, hmart]

/-- **Easy direction of Strassen's theorem** (Strassen 1965). A martingale coupling whose marginals
are supported on `[a, b]` implies the convex order on `[a, b]`: `μ.expect φ ≤ ν.expect φ` for every
convex `φ` continuous on `[a, b]`. -/
lemma convex_expect_le (h : IsMartingaleCoupling μ ν π)
    {a b : ℝ} (hμ : μ.supportsOn (Icc a b)) (hν : ν.supportsOn (Icc a b))
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Icc a b) φ)
    (hφ_cont : ContinuousOn φ (Icc a b)) :
    μ.expect φ ≤ ν.expect φ := by
  -- Disintegrate `π = μ ⊗ K`, where `K = π.toMeasure.condKernel`.
  have hfst : π.toMeasure.fst = μ.toMeasure := h.fst_measure
  -- Step 2: tested martingale → a.e. conditional mean identity.
  have hmart_ae : ∀ᵐ x ∂μ.toMeasure, ∫ y, y ∂(π.toMeasure.condKernel x) = x :=
    h.ae_conditional_mean_eq
  -- Step 3: fibres are concentrated on `Icc a b` for `μ`-a.e. `x`.
  -- Follows from `hν` through the disintegration identity
  -- `∫⁻ x, (condKernel x) t ∂π.fst = π (univ × t)` at `t = (Icc a b)ᶜ`.
  have hK_supp : ∀ᵐ x ∂μ.toMeasure, (π.toMeasure.condKernel x) (Icc a b) = 1 := by
    -- `π.toMeasure.snd = ν.toMeasure` (mirror of `hfst`).
    have hsnd : π.toMeasure.snd = ν.toMeasure := h.snd_measure
    -- `π (univ ×ˢ (Icc a b)ᶜ) = 0`.
    have hπ_null : π.toMeasure (Set.univ ×ˢ ((Icc a b : Set ℝ))ᶜ) = 0 := by
      have h1 : π.toMeasure.snd ((Icc a b : Set ℝ)ᶜ) =
          π.toMeasure (Set.univ ×ˢ ((Icc a b : Set ℝ))ᶜ) := by
        rw [Measure.snd_apply measurableSet_Icc.compl]
        congr 1; ext ⟨x, y⟩; simp
      rw [← h1, hsnd, (MeasureTheory.prob_compl_eq_zero_iff measurableSet_Icc).mpr hν]
    -- Disintegration: `∫⁻ x, (condKernel x) (Icc a b)ᶜ ∂μ = 0`.
    have h_int := MeasureTheory.Measure.setLIntegral_condKernel_eq_measure_prod
      (ρ := π.toMeasure) (s := (Set.univ : Set ℝ)) (t := ((Icc a b : Set ℝ))ᶜ)
      MeasurableSet.univ measurableSet_Icc.compl
    rw [hπ_null, MeasureTheory.setLIntegral_univ, hfst] at h_int
    have h_ae_null : ∀ᵐ x ∂μ.toMeasure,
        (π.toMeasure.condKernel x) ((Icc a b : Set ℝ)ᶜ) = 0 := by
      rwa [MeasureTheory.lintegral_eq_zero_iff
        (ProbabilityTheory.Kernel.measurable_coe _ measurableSet_Icc.compl)] at h_int
    filter_upwards [h_ae_null] with x hx
    exact (MeasureTheory.prob_compl_eq_zero_iff measurableSet_Icc).mp hx
  -- Step 4: Jensen on each fibre.
  -- For `μ`-a.e. `x`, `K x` is a probability measure on `Icc a b` with mean `x`; by
  -- `ConvexOn.map_integral_le` on the closed convex set `Icc a b`, `φ x ≤ ∫ y, φ y dK(x)`.
  have hjensen : ∀ᵐ x ∂μ.toMeasure,
      φ x ≤ ∫ y, φ y ∂(π.toMeasure.condKernel x) := by
    filter_upwards [hmart_ae, hK_supp] with x hx_mean hx_supp
    haveI : IsProbabilityMeasure (π.toMeasure.condKernel x) :=
      ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure x
    have hK_ae : ∀ᵐ y ∂(π.toMeasure.condKernel x), y ∈ Icc a b := by
      rw [ae_iff]
      exact (MeasureTheory.prob_compl_eq_zero_iff measurableSet_Icc).mpr hx_supp
    -- Integrability via the indicator trick (mirrors `ProbDist.integrable_of_supportsOn_Icc`):
    -- an `IntegrableOn (Icc a b)` function is `K x`-integrable since `K x` lives on `Icc a b`.
    have mk_int : ∀ f : ℝ → ℝ, IntegrableOn f (Icc a b) (π.toMeasure.condKernel x) →
        Integrable f (π.toMeasure.condKernel x) := fun f hf => by
      have hae : (Icc a b).indicator f =ᵐ[π.toMeasure.condKernel x] f := by
        filter_upwards [hK_ae] with y hy; simp [hy]
      exact (integrable_congr hae).mp (hf.integrable_indicator measurableSet_Icc)
    have hid_int : Integrable (fun y : ℝ => y) (π.toMeasure.condKernel x) :=
      mk_int _ continuousOn_id.integrableOn_Icc
    have hφ_int : Integrable φ (π.toMeasure.condKernel x) :=
      mk_int _ hφ_cont.integrableOn_Icc
    have hJ := hφ.map_integral_le (f := fun y : ℝ => y)
      (μ := π.toMeasure.condKernel x) hφ_cont isClosed_Icc hK_ae hid_int hφ_int
    rw [hx_mean] at hJ
    exact hJ
  -- Step 5: transfer `ν.expect φ` to `∫ φ(p.2) dπ` via `snd_marginal`.
  have h_push : ν.expect φ = ∫ p : ℝ × ℝ, φ p.2 ∂π.toMeasure := by
    have hφ_aesm_ν : AEStronglyMeasurable φ ν.toMeasure := by
      have := hφ_cont.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc
        (μ := ν.toMeasure)
      rwa [Measure.restrict_eq_self_of_ae_mem
        (ν.ae_mem_of_supportsOn measurableSet_Icc hν)] at this
    have hφ_aesm_map : AEStronglyMeasurable φ
        (ProbDist.map π Prod.snd measurable_snd).toMeasure := by
      rw [h.snd_marginal]; exact hφ_aesm_ν
    conv_lhs => rw [← h.snd_marginal]
    rw [ProbDist.expect_map π Prod.snd measurable_snd φ hφ_aesm_map]
    rfl
  -- Integrability of `p ↦ φ p.2` against `π`, transferred from integrability of `φ` on `ν`.
  have hφπ_int : Integrable (fun p : ℝ × ℝ => φ p.2) π.toMeasure := by
    have hφν : Integrable φ ν.toMeasure :=
      ProbDist.integrable_of_supportsOn_Icc (d := ν) hν hφ_cont
    have hν_map : ν.toMeasure = Measure.map Prod.snd π.toMeasure := by
      rw [← ProbDist.map_toMeasure π Prod.snd measurable_snd]
      exact congrArg (fun d : ProbDist ℝ => (d : Measure ℝ)) h.snd_marginal.symm
    have hφν' : Integrable φ (Measure.map Prod.snd π.toMeasure) := hν_map ▸ hφν
    exact (integrable_map_measure hφν'.aestronglyMeasurable
      measurable_snd.aemeasurable).mp hφν'
  -- Step 6: disintegrate `∫ φ(p.2) dπ` as an iterated integral.
  have h_disint : ∫ p : ℝ × ℝ, φ p.2 ∂π.toMeasure
      = ∫ x, (∫ y, φ y ∂(π.toMeasure.condKernel x)) ∂μ.toMeasure := by
    rw [← hfst]
    exact (MeasureTheory.Measure.integral_condKernel hφπ_int).symm
  -- Integrability side conditions for `integral_mono_ae`.
  have hφμ_int : Integrable φ μ.toMeasure :=
    ProbDist.integrable_of_supportsOn_Icc (d := μ) hμ hφ_cont
  have hφK_int :
      Integrable (fun x => ∫ y, φ y ∂(π.toMeasure.condKernel x)) μ.toMeasure := by
    rw [← hfst]
    exact hφπ_int.integral_condKernel
  -- Assemble.
  calc μ.expect φ
      = ∫ x, φ x ∂μ.toMeasure := rfl
    _ ≤ ∫ x, (∫ y, φ y ∂(π.toMeasure.condKernel x)) ∂μ.toMeasure :=
        integral_mono_ae hφμ_int hφK_int hjensen
    _ = ∫ p : ℝ × ℝ, φ p.2 ∂π.toMeasure := h_disint.symm
    _ = ν.expect φ := h_push.symm

/-- A martingale coupling whose marginals are supported on `[a, b]` witnesses the convex order
`ConvexOrderOnIcc a b μ ν`, bundling equal means and the convex-expectation inequality. -/
lemma convexOrderOnIcc (h : IsMartingaleCoupling μ ν π)
    {a b : ℝ} (hμ : μ.supportsOn (Icc a b)) (hν : ν.supportsOn (Icc a b)) :
    ConvexOrderOnIcc a b μ ν := by
  refine ⟨hμ, hν, h.mean_eq, ?_⟩
  intro φ hφ hφ_cont
  exact h.convex_expect_le hμ hν φ hφ hφ_cont

end IsMartingaleCoupling

end Econlib.Probability
