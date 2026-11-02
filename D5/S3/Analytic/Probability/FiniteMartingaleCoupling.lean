/- GID: D5/S3/Analytic/Probability/FiniteMartingaleCoupling
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/FiniteMartingaleCoupling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: FiniteMartingaleCoupling for compact scalar martingale transport. -/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/econlib-strassen/LICENSE.txt.
Authors: Daniel Lyng
Ported from danlyng/Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f.
Modified for the host probability-measure API, native conditional expectation,
existing library suppliers, and a construction-oriented module organization.
-/
import D5.S3.Analytic.Convexity.FiniteMajorization
import D5.S3.Geometry.ProbabilityTransport.CostCoupling
import D5.S3.Analytic.Probability.CompactConvexOrder
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Disintegration.Integral


open MeasureTheory Set Filter Topology

section
open MeasureTheory
namespace MeasureTheory
/-- Pushforward by a measurable map commutes with a finite sum of measures:
`(∑ i ∈ s, m i).map f = ∑ i ∈ s, (m i).map f`. -/
private lemma measure_map_finset_sum {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f)
    {s : Finset ι} (m : ι → Measure α) :
    Measure.map f (∑ i ∈ s, m i) = ∑ i ∈ s, Measure.map f (m i) := by
  exact Measure.map_finset_sum hf.aemeasurable

end MeasureTheory
end

section
open MeasureTheory Set
namespace Econlib.Probability
/-- `π : ProbDist (α × β)` is a **coupling** of laws `μ : ProbDist α`, `ν : ProbDist β`: Its
`Prod.fst`-marginal equals `μ` and its `Prod.snd`-marginal equals `ν`. -/
abbrev IsCoupling {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : ProbDist α) (ν : ProbDist β) (π : ProbDist (α × β)) : Prop :=
  CostTransport.IsCoupling π.toMeasure μ.toMeasure ν.toMeasure

namespace IsCoupling

lemma fst_probability_marginal {μ ν : ProbDist ℝ} {π : ProbDist (ℝ × ℝ)}
    (h : IsCoupling μ ν π) : ProbDist.map π Prod.fst measurable_fst = μ :=
  ProbabilityMeasure.toMeasure_injective h.1

lemma snd_probability_marginal {μ ν : ProbDist ℝ} {π : ProbDist (ℝ × ℝ)}
    (h : IsCoupling μ ν π) : ProbDist.map π Prod.snd measurable_snd = ν :=
  ProbabilityMeasure.toMeasure_injective h.2


/-- A coupling of laws supported on `s` and `t` is supported on `s ×ˢ t`. -/
private lemma supportsOn_prod_set {μ ν : ProbDist ℝ} {π : ProbDist (ℝ × ℝ)}
    (hπ : IsCoupling μ ν π) {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμ : μ.supportsOn s) (hν : ν.supportsOn t) :
    π.toMeasure (s ×ˢ t) = 1 := by
  have hfst : π.toMeasure.fst = μ.toMeasure := by
    have heq := congrArg (fun d : ProbDist ℝ => (d : Measure ℝ)) hπ.fst_probability_marginal
    simpa [Measure.fst, ProbDist.map_toMeasure] using heq
  have hsnd : π.toMeasure.snd = ν.toMeasure := by
    have heq := congrArg (fun d : ProbDist ℝ => (d : Measure ℝ)) hπ.snd_probability_marginal
    simpa [Measure.snd, ProbDist.map_toMeasure] using heq
  have h_sfst : π.toMeasure (sᶜ ×ˢ (Set.univ : Set ℝ)) = 0 := by
    have hpre : (sᶜ ×ˢ (Set.univ : Set ℝ)) = Prod.fst ⁻¹' sᶜ := by
      ext ⟨x, y⟩; simp
    rw [hpre, ← Measure.fst_apply hs.compl, hfst]
    exact (MeasureTheory.prob_compl_eq_zero_iff hs).mpr hμ
  have h_stnd : π.toMeasure ((Set.univ : Set ℝ) ×ˢ tᶜ) = 0 := by
    have hpre : ((Set.univ : Set ℝ) ×ˢ tᶜ) = Prod.snd ⁻¹' tᶜ := by
      ext ⟨x, y⟩; simp
    rw [hpre, ← Measure.snd_apply ht.compl, hsnd]
    exact (MeasureTheory.prob_compl_eq_zero_iff ht).mpr hν
  have h_compl : (s ×ˢ t)ᶜ = sᶜ ×ˢ (Set.univ : Set ℝ) ∪ (Set.univ : Set ℝ) ×ˢ tᶜ := by
    ext ⟨x, y⟩; by_cases hx : x ∈ s <;> by_cases hy : y ∈ t <;> simp [hx, hy]
  have h_null : π.toMeasure (s ×ˢ t)ᶜ = 0 := by
    rw [h_compl]
    refine le_antisymm ?_ zero_le
    calc π.toMeasure (sᶜ ×ˢ (Set.univ : Set ℝ) ∪ (Set.univ : Set ℝ) ×ˢ tᶜ)
        ≤ π.toMeasure (sᶜ ×ˢ (Set.univ : Set ℝ))
            + π.toMeasure ((Set.univ : Set ℝ) ×ˢ tᶜ) := measure_union_le _ _
      _ = 0 := by rw [h_sfst, h_stnd]; simp
  exact (MeasureTheory.prob_compl_eq_zero_iff (hs.prod ht)).mp h_null

/-- A coupling with marginals concentrated on `Icc a b` is concentrated on the square. -/
lemma supportsOn_Icc_prod {a b : ℝ} {μ ν : ProbDist ℝ} {π : ProbDist (ℝ × ℝ)}
    (hπ : IsCoupling μ ν π) (hμ : μ.supportsOn (Icc a b)) (hν : ν.supportsOn (Icc a b)) :
    π.toMeasure (Icc a b ×ˢ Icc a b) = 1 :=
  hπ.supportsOn_prod_set measurableSet_Icc measurableSet_Icc hμ hν

end IsCoupling

end Econlib.Probability
end

section
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
private lemma integrable_id_fst (h : IsMartingaleCoupling μ ν π) :
    Integrable (fun x : ℝ => x) μ.toMeasure := by
  have hmap : μ.toMeasure = Measure.map Prod.fst π.toMeasure := by rw [← h.fst_measure]; rfl
  rw [hmap]
  refine (MeasureTheory.integrable_map_measure ?_ measurable_fst.aemeasurable).mpr ?_
  · exact (measurable_id).aestronglyMeasurable
  · exact h.integrable_fst

/-- **Conditional martingale identity.** For a martingale coupling `π` of `μ, ν`, the `condKernel`
of `π` has μ-a.e. fiber mean equal to the base point. -/
private lemma ae_conditional_mean_eq (h : IsMartingaleCoupling μ ν π) :
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
lemma marginal_mean_eq (h : IsMartingaleCoupling μ ν π) :
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

end IsMartingaleCoupling

end Econlib.Probability
end

section
open MeasureTheory Set Finset BigOperators

namespace Econlib.Probability

/-- A finitely-supported real-valued probability law specified by atoms and weights. -/
structure DiscreteLaw where
  /-- The number of atoms. -/
  n : ℕ
  /-- Locations of atoms. -/
  atom : Fin n → ℝ
  /-- Probability weights on each atom. -/
  weight : Fin n → ℝ
  /-- Weights are non-negative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i
  /-- Weights sum to one. -/
  weight_sum : ∑ i, weight i = 1

namespace DiscreteLaw

/-- Embedding of a discrete law into `ProbDist ℝ` as a finite weighted sum of Diracs. -/
noncomputable def toProbDist (p : DiscreteLaw) : ProbDist ℝ :=
  ⟨∑ i, ENNReal.ofReal (p.weight i) • Measure.dirac (p.atom i), by
    constructor
    simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
      Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.weight_nonneg i), p.weight_sum]
    simp⟩

@[simp] lemma toProbDist_toMeasure (p : DiscreteLaw) :
    p.toProbDist.toMeasure = ∑ i, ENNReal.ofReal (p.weight i) • Measure.dirac (p.atom i) :=
  rfl

/-- If all atoms of a discrete law lie in a measurable set `s`, then the law is supported on `s`. -/
lemma toProbDist_supportsOn_of_atoms_mem (p : DiscreteLaw) {s : Set ℝ}
    (hs : MeasurableSet s) (hatoms : ∀ i, p.atom i ∈ s) :
    p.toProbDist.supportsOn s := by
  unfold ProbDist.supportsOn
  rw [toProbDist_toMeasure]
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]
  have h_ind : ∀ i, (s.indicator (1 : ℝ → ENNReal) (p.atom i)) = 1 := fun i => by
    simp [Set.indicator_of_mem (hatoms i)]
  simp_rw [h_ind, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.weight_nonneg i), p.weight_sum,
    ENNReal.ofReal_one]

/-- The mean of the discrete law: `∑ i, weight i · atom i`. -/
noncomputable def mean (p : DiscreteLaw) : ℝ := ∑ i, p.weight i * p.atom i

/-- Jensen-form convex order for discrete laws: Every convex function gets weakly larger
expectation under `q` than under `p`. -/
def ConvexOrder (p q : DiscreteLaw) : Prop :=
  ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ →
    ∑ i, p.weight i * φ (p.atom i) ≤ ∑ j, q.weight j * φ (q.atom j)

/-- Convex order on discrete laws forces equal means: Testing against `id` and `-id` (both convex)
gives `p.mean ≤ q.mean ≤ p.mean`. -/
private lemma ConvexOrder.finite_mean_eq {p q : DiscreteLaw} (h : p.ConvexOrder q) : p.mean = q.mean := by
  have hconv_id : ConvexOn ℝ Set.univ (id : ℝ → ℝ) := convexOn_id convex_univ
  have hconv_neg : ConvexOn ℝ Set.univ (fun x : ℝ => -x) := (concaveOn_id convex_univ).neg
  have h_le : p.mean ≤ q.mean := by
    simpa [DiscreteLaw.mean] using h id hconv_id
  have h_ge : q.mean ≤ p.mean := by
    have hneg := h (fun x => -x) hconv_neg
    have hsp : ∑ i, p.weight i * (- p.atom i) = -p.mean := by
      simp [DiscreteLaw.mean, mul_neg, Finset.sum_neg_distrib]
    have hsq : ∑ j, q.weight j * (- q.atom j) = -q.mean := by
      simp [DiscreteLaw.mean, mul_neg, Finset.sum_neg_distrib]
    rw [hsp, hsq] at hneg
    linarith
  linarith

/-- Uniform-weight discrete law with `n` atoms at positions `x k`, each atom carrying weight
`1/n`. -/
noncomputable def uniform (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) : DiscreteLaw where
  n := n
  atom := x
  weight := fun _ => (1 : ℝ) / n
  weight_nonneg := fun _ => by positivity
  weight_sum := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

/-- The mean of a uniform-weight discrete law is the arithmetic mean of its atoms. -/
lemma uniform_mean {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (uniform n hn x).mean = (∑ i, x i) / n := by
  simp only [mean, uniform]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end DiscreteLaw

/-- A **bistochastic martingale matrix** transporting `p` to `q`:

* positive-weight rows are probability distributions,
* each positive-weight row's `q.atom`-average equals the corresponding `p.atom`,
* the column marginal reproduces `q.weight`.

Rows with `p.weight i = 0` are irrelevant to the transported measure
`π({(p.atom i, q.atom j)}) = p.weight i * T i j`, so we do not impose Markov or martingale
constraints on them. -/
structure BistochasticMartingaleMatrix (p q : DiscreteLaw) where
  /-- Transition probabilities: `T i j` is the conditional probability of `q.atom j` given
  `p.atom i`. -/
  T : Fin p.n → Fin q.n → ℝ
  /-- Entries are non-negative. -/
  nonneg : ∀ i j, 0 ≤ T i j
  /-- Positive-weight rows sum to one (Markov property on the transported support). -/
  row_sum : ∀ i, p.weight i ≠ 0 → ∑ j, T i j = 1
  /-- Positive-weight rows have the prescribed conditional mean. -/
  mean_eq : ∀ i, p.weight i ≠ 0 → ∑ j, T i j * q.atom j = p.atom i
  /-- Column marginal reproduces `q.weight` (pushforward to the target). -/
  col_marginal : ∀ j, ∑ i, p.weight i * T i j = q.weight j

/-- Build a `BistochasticMartingaleMatrix` from a square doubly stochastic matrix on `Fin p.n` once
the target law is reindexed to the same cardinality and both laws have uniform weights. This
isolates the remaining discrete Strassen gap to the majorization statement `D *ᵥ y = x`. -/
private lemma BistochasticMartingaleMatrix.nonempty_of_doublyStochastic
    {p q : DiscreteLaw} (hn : p.n = q.n)
    (hp_uniform : ∀ i, p.weight i = (1 : ℝ) / p.n)
    (hq_uniform : ∀ j, q.weight j = (1 : ℝ) / q.n)
    (D : Matrix (Fin p.n) (Fin p.n) ℝ)
    (hD : D ∈ doublyStochastic ℝ (Fin p.n))
    (hmean : Matrix.mulVec D (q.atom ∘ (Fin.castOrderIso hn).toEquiv) = p.atom) :
    Nonempty (BistochasticMartingaleMatrix p q) := by
  let e : Fin p.n ≃ Fin q.n := (Fin.castOrderIso hn).toEquiv
  refine ⟨{
    T := fun i j => D i (e.symm j)
    nonneg := ?_
    row_sum := ?_
    mean_eq := ?_
    col_marginal := ?_
  }⟩
  · intro i j
    simpa [e] using (nonneg_of_mem_doublyStochastic hD (i := i) (j := e.symm j))
  · intro i _
    calc
      ∑ j, D i (e.symm j)
          = ∑ j : Fin p.n, D i j := by
            simpa using (Equiv.sum_comp e.symm (fun j : Fin p.n => D i j))
      _ = 1 := sum_row_of_mem_doublyStochastic hD i
  · intro i _
    have hi_mean : Matrix.mulVec D (q.atom ∘ e) i = p.atom i := by
      simpa [e] using congrArg (fun v => v i) hmean
    calc
      ∑ j, D i (e.symm j) * q.atom j
          = ∑ j : Fin p.n, D i j * q.atom (e j) := by
            simpa using
              (Equiv.sum_comp e (fun j : Fin q.n => D i (e.symm j) * q.atom j)).symm
      _ = Matrix.mulVec D (q.atom ∘ e) i := by
        simp [Matrix.mulVec, dotProduct, e]
      _ = p.atom i := hi_mean
  · intro j
    calc
      ∑ i, p.weight i * D i (e.symm j)
          = ∑ i : Fin p.n, ((1 : ℝ) / p.n) * D i (e.symm j) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [hp_uniform i]
      _ = (1 : ℝ) / p.n * ∑ i : Fin p.n, D i (e.symm j) := by rw [← Finset.mul_sum]
      _ = (1 : ℝ) / p.n := by rw [sum_col_of_mem_doublyStochastic hD (e.symm j), mul_one]
      _ = q.weight j := by
        rw [hq_uniform j]
        simp [hn]

private lemma convexOrder_unweighted_of_uniform
    {p q : DiscreteLaw} (hn_pos : 0 < p.n) (hn : p.n = q.n)
    (hp_uniform : ∀ i, p.weight i = (1 : ℝ) / p.n)
    (hq_uniform : ∀ j, q.weight j = (1 : ℝ) / q.n)
    (h : DiscreteLaw.ConvexOrder p q) :
    ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ ->
      ∑ i, φ (p.atom i) ≤ ∑ j, φ (q.atom j) := by
  intro φ hφ
  have hcx := h φ hφ
  have hc : 0 < (1 : ℝ) / p.n := by
    positivity
  have hp_sum :
      ∑ i, p.weight i * φ (p.atom i) = ((1 : ℝ) / p.n) * ∑ i, φ (p.atom i) := by
    simp_rw [hp_uniform]
    rw [Finset.mul_sum]
  have hq_sum :
      ∑ j, q.weight j * φ (q.atom j) = ((1 : ℝ) / p.n) * ∑ j, φ (q.atom j) := by
    simp_rw [hq_uniform]
    rw [Finset.mul_sum]
    simp [hn]
  rw [hp_sum, hq_sum] at hcx
  nlinarith

private lemma sum_eq_of_uniform_mean_eq
    {p q : DiscreteLaw} (hn_pos : 0 < p.n) (hn : p.n = q.n)
    (hp_uniform : ∀ i, p.weight i = (1 : ℝ) / p.n)
    (hq_uniform : ∀ j, q.weight j = (1 : ℝ) / q.n)
    (hmean : p.mean = q.mean) :
    ∑ i, p.atom i = ∑ j, q.atom j := by
  have hp_mean :
      p.mean = ((1 : ℝ) / p.n) * ∑ i, p.atom i := by
    simp [DiscreteLaw.mean, hp_uniform, Finset.mul_sum]
  have hq_mean :
      q.mean = ((1 : ℝ) / p.n) * ∑ j, q.atom j := by
    simp [DiscreteLaw.mean, hq_uniform, Finset.mul_sum, hn]
  rw [hp_mean, hq_mean] at hmean
  have hc : 0 < (1 : ℝ) / p.n := by
    positivity
  nlinarith

/-- **Discrete Hardy–Littlewood–Pólya — uniform equal-cardinality case.** Convex-order domination
between two finitely-supported laws that carry the same number of atoms and uniform weights `1/n`
yields a bistochastic martingale matrix.

This is the case used by the compact-law construction: conditional-mean quantile atomization
produces uniform, equal-cardinality laws. The matrix-to-joint-law construction below also accepts
arbitrary nonnegative atom weights satisfying its row, column and mean constraints. -/
private theorem discrete_martingale_matrix_exists_uniform (p q : DiscreteLaw)
    (hn_pos : 0 < p.n) (hn : p.n = q.n)
    (hp_uniform : ∀ i, p.weight i = (1 : ℝ) / p.n)
    (hq_uniform : ∀ j, q.weight j = (1 : ℝ) / q.n)
    (h : DiscreteLaw.ConvexOrder p q) :
    Nonempty (BistochasticMartingaleMatrix p q) := by
  have hmean_eq : p.mean = q.mean := DiscreteLaw.ConvexOrder.finite_mean_eq h
  -- Base case: `p` has exactly one atom. Then `p.atom i = p.mean = q.mean` for the unique
  -- `i`, and `T i j := q.weight j` satisfies all four properties trivially.
  by_cases hp1 : p.n = 1
  · refine ⟨?_⟩
    -- Singleton lemma: `Fin p.n = {i}` for any `i`.
    have hsingle : ∀ i : Fin p.n, (Finset.univ : Finset (Fin p.n)) = {i} := by
      intro i
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun j _ => ?_⟩
      have hj : j.val < p.n := j.isLt
      have hi : i.val < p.n := i.isLt
      exact Fin.ext (by omega)
    have hp_weight_one : ∀ i : Fin p.n, p.weight i = 1 := fun i => by
      rw [← p.weight_sum, hsingle i, Finset.sum_singleton]
    have hp_atom_eq_mean : ∀ i : Fin p.n, p.atom i = p.mean := fun i => by
      unfold DiscreteLaw.mean
      rw [hsingle i, Finset.sum_singleton, hp_weight_one i, one_mul]
    exact {
      T := fun _ j => q.weight j
      nonneg := fun _ j => q.weight_nonneg j
      row_sum := fun _ _ => q.weight_sum
      mean_eq := fun i _ => by
        show ∑ j, q.weight j * q.atom j = p.atom i
        rw [hp_atom_eq_mean i, hmean_eq]; rfl
      col_marginal := fun j => by
        show ∑ i, p.weight i * q.weight j = q.weight j
        rw [← Finset.sum_mul, p.weight_sum, one_mul]
    }
  · -- General case (`p.n ≥ 2`): classical Hardy–Littlewood–Pólya. Requires a separate
    -- majorization theorem converting the scalar convex-order inequalities on the
    -- equally-weighted atoms into a doubly stochastic matrix acting on the target atom vector.
    let y : Fin p.n → ℝ := q.atom ∘ (Fin.castOrderIso hn).toEquiv
    -- Reindexing `y` back onto `q.atom` along the `Fin p.n ≃ Fin q.n` cast: pulls any scalar
    -- function `g` through the equivalence.
    have hy_reindex : ∀ g : ℝ → ℝ, (∑ j, g (y j)) = ∑ j : Fin q.n, g (q.atom j) := fun g => by
      dsimp [y]
      simpa using
        (Equiv.sum_comp ((Fin.castOrderIso hn).toEquiv) (fun j : Fin q.n => g (q.atom j)))
    have h_unweighted :
        ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → ∑ i, φ (p.atom i) ≤ ∑ j, φ (y j) := by
      intro φ hφ
      rw [hy_reindex φ]
      exact convexOrder_unweighted_of_uniform hn_pos hn hp_uniform hq_uniform h φ hφ
    have h_sum_eq : ∑ i, p.atom i = ∑ j, y j := by
      rw [hy_reindex (fun x => x)]
      exact sum_eq_of_uniform_mean_eq hn_pos hn hp_uniform hq_uniform hmean_eq
    have h_core :
        ∃ D : Matrix (Fin p.n) (Fin p.n) ℝ,
          D ∈ doublyStochastic ℝ (Fin p.n) ∧
            Matrix.mulVec D y = p.atom :=
      exists_doublyStochastic_mulVec_of_convex_dominates p.atom y h_unweighted h_sum_eq
    rcases h_core with ⟨D, hD, hDmean⟩
    exact BistochasticMartingaleMatrix.nonempty_of_doublyStochastic hn hp_uniform hq_uniform
      D hD (by simpa [y] using hDmean)

namespace BistochasticMartingaleMatrix

variable {p q : DiscreteLaw}

/-- Collapsing a row of the joint masses: `∑ⱼ ofReal(pᵢ · Tᵢⱼ) = ofReal pᵢ`. For an active row this
is `row_sum`; for a zero-weight row both sides vanish. Used by the total-mass proof and the first
marginal. -/
private lemma row_ofReal_sum (M : BistochasticMartingaleMatrix p q) (i : Fin p.n) :
    ∑ j, ENNReal.ofReal (p.weight i * M.T i j) = ENNReal.ofReal (p.weight i) := by
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun j _ => mul_nonneg (p.weight_nonneg i) (M.nonneg i j))]
  congr 1
  by_cases hi : p.weight i = 0
  · rw [hi]; simp
  · rw [← Finset.mul_sum, M.row_sum i hi, mul_one]

/-- The joint law `π({(p.atom i, q.atom j)}) = p.weight i · T i j`, promoted to a
`ProbDist (ℝ × ℝ)`. -/
noncomputable def toJointProbDist (M : BistochasticMartingaleMatrix p q) :
    ProbDist (ℝ × ℝ) :=
  ⟨∑ i, ∑ j, ENNReal.ofReal (p.weight i * M.T i j) •
      Measure.dirac (p.atom i, q.atom j), by
      constructor
      -- Total mass: `∑ᵢⱼ pᵢ · Tᵢⱼ = ∑ᵢ pᵢ · (∑ⱼ Tᵢⱼ) = ∑ᵢ pᵢ · 1 = 1`.
      simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
        smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
        Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
      -- Pull `ENNReal.ofReal` out of each inner sum, then over the outer sum.
      simp_rw [row_ofReal_sum M]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.weight_nonneg i),
        p.weight_sum, ENNReal.ofReal_one]⟩

@[simp] private lemma toJointProbDist_toMeasure (M : BistochasticMartingaleMatrix p q) :
    M.toJointProbDist.toMeasure
      = ∑ i, ∑ j, ENNReal.ofReal (p.weight i * M.T i j)
          • Measure.dirac (p.atom i, q.atom j) :=
  rfl

/-- The assembled coupling has `p.toProbDist` as first marginal, `q.toProbDist` as second marginal,
and satisfies the tested martingale identity. -/
lemma isMartingaleCoupling (M : BistochasticMartingaleMatrix p q) :
    IsMartingaleCoupling p.toProbDist q.toProbDist M.toJointProbDist := by
  -- Convenience: integration against the joint measure reduces to a finite double sum.
  have hnn : ∀ i j, 0 ≤ p.weight i * M.T i j := fun i j =>
    mul_nonneg (p.weight_nonneg i) (M.nonneg i j)
  -- Every strongly measurable `f` is integrable against the finitely-supported joint measure:
  -- each scaled Dirac is integrable and the measure is a finite sum of them.
  have h_integ : ∀ f : ℝ × ℝ → ℝ, StronglyMeasurable f →
      Integrable f M.toJointProbDist.toMeasure := by
    intro f hf
    rw [toJointProbDist_toMeasure]
    refine integrable_finset_sum_measure.mpr fun i _ => ?_
    refine integrable_finset_sum_measure.mpr fun j _ => ?_
    exact (integrable_dirac' hf (a := (p.atom i, q.atom j))
      ENNReal.coe_lt_top).smul_measure ENNReal.ofReal_ne_top
  -- The integral against the total measure is a double sum of pointwise values.
  have h_int : ∀ f : ℝ × ℝ → ℝ, StronglyMeasurable f →
      ∫ x, f x ∂M.toJointProbDist.toMeasure
        = ∑ i, ∑ j, p.weight i * M.T i j * f (p.atom i, q.atom j) := by
    intro f hf
    rw [toJointProbDist_toMeasure]
    -- Pull the outer `∑ i` out of the integral.
    rw [integral_finset_sum_measure (fun i _ => by
      refine integrable_finset_sum_measure.mpr (fun j _ => ?_)
      exact (integrable_dirac' hf (a := (p.atom i, q.atom j))
        ENNReal.coe_lt_top).smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- Pull the inner `∑ j` out of the integral.
    rw [integral_finset_sum_measure (fun j _ =>
      (integrable_dirac' hf (a := (p.atom i, q.atom j))
        ENNReal.coe_lt_top).smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun j _ => ?_
    -- Reduce `∫ f ∂(c • δ_x) = c.toReal • f x`.
    rw [integral_smul_measure, integral_dirac' _ _ hf,
      ENNReal.toReal_ofReal (hnn i j), smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- fst_marginal: pushforward by `Prod.fst` equals `p.toProbDist`.
    apply ProbabilityMeasure.toMeasure_injective
    change (Measure.map Prod.fst M.toJointProbDist.toMeasure) = p.toProbDist.toMeasure
    rw [toJointProbDist_toMeasure, DiscreteLaw.toProbDist_toMeasure]
    -- Push `Prod.fst` through both sums and each `c • δ_{(xᵢ,yⱼ)} = c • δ_{xᵢ}`.
    rw [MeasureTheory.measure_map_finset_sum measurable_fst]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.measure_map_finset_sum measurable_fst]
    -- Each summand: `Measure.map fst (c • δ_{(xᵢ,yⱼ)}) = c • δ_{xᵢ}`.
    simp_rw [Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_dirac' measurable_fst]
    -- Combine the inner sum: `∑ⱼ ofReal (pᵢ Tᵢⱼ) • δ_{xᵢ} = ofReal pᵢ • δ_{xᵢ}`.
    rw [← Finset.sum_smul]
    congr 1
    exact row_ofReal_sum M i
  · -- snd_marginal: pushforward by `Prod.snd` equals `q.toProbDist`.
    apply ProbabilityMeasure.toMeasure_injective
    change (Measure.map Prod.snd M.toJointProbDist.toMeasure) = q.toProbDist.toMeasure
    rw [toJointProbDist_toMeasure, DiscreteLaw.toProbDist_toMeasure]
    rw [MeasureTheory.measure_map_finset_sum measurable_snd]
    simp_rw [MeasureTheory.measure_map_finset_sum measurable_snd,
      Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_dirac' measurable_snd]
    -- Swap sums to group by `j` first.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i j), M.col_marginal j]
  · -- integrable_fst: finitely-supported measure.
    exact h_integ _ measurable_fst.stronglyMeasurable
  · -- integrable_snd: analogous.
    exact h_integ _ measurable_snd.stronglyMeasurable
  · -- martingale: expand on the discrete support, use row_sum and mean_eq.
    intro φ hφ _
    have hf : StronglyMeasurable (fun x : ℝ × ℝ => (x.2 - x.1) * φ x.1) :=
      (measurable_snd.sub measurable_fst).stronglyMeasurable.mul
        (hφ.stronglyMeasurable.comp_measurable measurable_fst)
    rw [h_int _ hf]
    -- ∑ᵢⱼ pᵢTᵢⱼ (yⱼ - xᵢ) φ(xᵢ) = ∑ᵢ pᵢ φ(xᵢ) (∑ⱼ Tᵢⱼ yⱼ - xᵢ ∑ⱼ Tᵢⱼ) = 0.
    have hi : ∀ i, ∑ j, p.weight i * M.T i j *
          ((q.atom j - p.atom i) * φ (p.atom i)) = 0 := by
      intro i
      have h_expand : ∀ j, p.weight i * M.T i j *
            ((q.atom j - p.atom i) * φ (p.atom i))
          = p.weight i * φ (p.atom i) *
            (M.T i j * q.atom j - p.atom i * M.T i j) := by
        intro j; ring
      simp_rw [h_expand]
      by_cases hi : p.weight i = 0
      · rw [hi]
        simp
      · rw [← Finset.mul_sum]
        have hS : ∑ j, (M.T i j * q.atom j - p.atom i * M.T i j) = 0 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, M.mean_eq i hi,
            M.row_sum i hi, mul_one, sub_self]
        rw [hS, mul_zero]
    simp_rw [hi]
    exact Finset.sum_const_zero

end BistochasticMartingaleMatrix

/-- Discrete Strassen — uniform equal-cardinality case: Two finitely-supported laws with equal atom
count and uniform weights `1/n`, in convex order, admit an explicit martingale coupling.

This is the special case consumed by the compact-law Strassen construction. The matrix-to-joint
assembly accepts arbitrary weights once the matrix constraints are supplied. -/
theorem DiscreteLaw.exists_martingaleCoupling_uniform (p q : DiscreteLaw)
    (hn_pos : 0 < p.n) (hn : p.n = q.n)
    (hp_uniform : ∀ i, p.weight i = (1 : ℝ) / p.n)
    (hq_uniform : ∀ j, q.weight j = (1 : ℝ) / q.n)
    (h : DiscreteLaw.ConvexOrder p q) :
    ∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling p.toProbDist q.toProbDist π := by
  obtain ⟨M⟩ := discrete_martingale_matrix_exists_uniform p q hn_pos hn hp_uniform hq_uniform h
  exact ⟨M.toJointProbDist, M.isMartingaleCoupling⟩

end Econlib.Probability
end
