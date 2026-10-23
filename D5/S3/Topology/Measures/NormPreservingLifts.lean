/- GID: D5/S3/Topology/Measures/NormPreservingLifts
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/NormPreservingLifts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Norm-preserving signed lifts share the reference weak-star limit. -/

import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.ContinuousMap.LocallyConstant
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Tactic

/-!
# Norm-preserving signed lifts on compact spaces

The functional is actual signed integration on real continuous functions. No
normed-space instance is imposed on `SignedMeasure`. Eventual fibre constancy
is tested one fixed locally constant observable at a time; the final universal
weak-star conclusion is proved rather than assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace D5.S3.Topology.Measures.NormPreservingLifts

universe u v w

lemma totalVariation_map_of_mass {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (s : SignedMeasure X)
    (p : X → Y) (hp : Measurable p)
    (hmass : (SignedMeasure.totalVariation (s.map p)) univ = s.totalVariation univ) :
    (SignedMeasure.totalVariation (s.map p)) = s.totalVariation.map p := by
  apply Measure.eq_of_le_of_measure_univ_eq
  · simpa only [SignedMeasure.totalVariation_eq_variation] using
      (VectorMeasure.variation_map_le (μ := s) (φ := p))
  · simpa only [Measure.map_apply hp MeasurableSet.univ, preimage_univ] using hmass

private lemma totalVariation_preimage_null {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (s : SignedMeasure X)
    (p : X → Y) (hp : Measurable p)
    (hmass : (SignedMeasure.totalVariation (s.map p)) univ = s.totalVariation univ)
    {V : Set Y} (hV : MeasurableSet V)
    (hnull : (SignedMeasure.totalVariation (s.map p)) Vᶜ = 0) :
    s.totalVariation (p ⁻¹' V)ᶜ = 0 := by
  rw [totalVariation_map_of_mass s p hp hmass,
    Measure.map_apply hp hV.compl, preimage_compl] at hnull
  exact hnull

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
variable [MeasurableSpace K] [BorelSpace K]

private lemma continuous_integrable (s : SignedMeasure K) (f : C(K, ℝ)) :
    s.Integrable f := by
  rw [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation]
  exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private noncomputable def signedLinear (s : SignedMeasure K) : C(K, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ᵛ x, f x ∂•s
  map_add' f g := by
    exact VectorMeasure.integral_fun_add (continuous_integrable s f) (continuous_integrable s g)
  map_smul' c f := by
    exact VectorMeasure.integral_fun_smul s (ContinuousLinearMap.lsmul ℝ ℝ) c f

private lemma signedLinear_bound (s : SignedMeasure K) (f : C(K, ℝ)) :
    ‖signedLinear s f‖ ≤ s.totalVariation.real univ * ‖f‖ := by
  have : IsFiniteMeasure s.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]; infer_instance
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := s) (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (f := fun x => f x) (C := ‖f‖)
    (Eventually.of_forall f.norm_coe_le_norm)
  simpa [signedLinear, SignedMeasure.totalVariation_eq_variation, mul_comm] using h

/-- Integration against a signed measure, as an actual continuous linear
functional on the real Banach space of continuous functions on the compact carrier. -/
noncomputable def signedFunctional (s : SignedMeasure K) : StrongDual ℝ C(K, ℝ) :=
  (signedLinear s).mkContinuous (s.totalVariation.real univ) (signedLinear_bound s)

lemma signedFunctional_norm_le (s : SignedMeasure K) :
    ‖signedFunctional s‖ ≤ s.totalVariation.real univ :=
  (signedLinear s).mkContinuous_norm_le (measureReal_nonneg) (signedLinear_bound s)

lemma apply_eq_of_supported_clopen {L : Type v} [TopologicalSpace L]
    [T2Space L] [MeasurableSpace L] [BorelSpace L]
    (p : K → L) (hp : Continuous p) {V : Set L} (hV : IsClopen V)
    (s t : SignedMeasure K) (hmap : s.map p = t.map p)
    (hs : s.totalVariation (p ⁻¹' V)ᶜ = 0)
    (ht : t.totalVariation (p ⁻¹' V)ᶜ = 0)
    {A : Set K} (hA : IsClopen A)
    (hfibre : ∀ x y, p x ∈ V → p y ∈ V → p x = p y → (x ∈ A ↔ y ∈ A)) :
    s A = t A := by
  let D : Set L := p '' (A ∩ p ⁻¹' V)
  have hD : MeasurableSet D :=
    ((hA.isClosed.inter (hV.isClosed.preimage hp)).isCompact.image hp).isClosed.measurableSet
  have hB : MeasurableSet (p ⁻¹' D) := hp.measurable hD
  have hleft : A \ p ⁻¹' D ⊆ (p ⁻¹' V)ᶜ := by
    intro x hx hxV
    exact hx.2 ⟨x, ⟨hx.1, hxV⟩, rfl⟩
  have hright : p ⁻¹' D \ A ⊆ (p ⁻¹' V)ᶜ := by
    intro x hx hxV
    obtain ⟨y, hy, hxy⟩ := hx.1
    exact hx.2 ((hfibre x y hxV hy.2 hxy.symm).mpr hy.1)
  have heq (r : SignedMeasure K) (hr : r.totalVariation (p ⁻¹' V)ᶜ = 0) :
      r A = r (p ⁻¹' D) := by
    have hzeroL : r (A \ p ⁻¹' D) = 0 :=
      r.null_of_totalVariation_zero (measure_mono_null hleft hr)
    have hzeroR : r (p ⁻¹' D \ A) = 0 :=
      r.null_of_totalVariation_zero (measure_mono_null hright hr)
    have h := VectorMeasure.of_sdiff_of_sdiff_eq_zero (v := r) hA.isClosed.measurableSet hB hzeroR
    simpa only [hzeroL, zero_add] using h.symm
  rw [heq s hs, heq t ht, ← VectorMeasure.map_apply s hp.measurable hD,
    ← VectorMeasure.map_apply t hp.measurable hD, hmap]

private lemma map_locallyConstant_eq {L : Type v} [TopologicalSpace L]
    [T2Space L] [MeasurableSpace L] [BorelSpace L]
    (p : K → L) (hp : Continuous p) {V : Set L} (hV : IsClopen V)
    (s t : SignedMeasure K) (hmap : s.map p = t.map p)
    (hs : s.totalVariation (p ⁻¹' V)ᶜ = 0)
    (ht : t.totalVariation (p ⁻¹' V)ᶜ = 0)
    (f : LocallyConstant K ℝ)
    (hfibre : ∀ x y, p x ∈ V → p y ∈ V → p x = p y → f x = f y) :
    s.map f = t.map f := by
  ext B hB
  rw [VectorMeasure.map_apply s f.continuous.measurable hB,
    VectorMeasure.map_apply t f.continuous.measurable hB]
  apply apply_eq_of_supported_clopen p hp hV s t hmap hs ht
  · constructor
    · constructor
      convert f.isLocallyConstant Bᶜ using 1
      ext x
      rfl
    · exact f.isLocallyConstant B
  · intro x y hx hy hxy
    simp only [mem_preimage, hfibre x y hx hy hxy]

private lemma integral_locallyConstant_eq {L : Type v} [TopologicalSpace L]
    [T2Space L] [MeasurableSpace L] [BorelSpace L]
    (p : K → L) (hp : Continuous p) {V : Set L} (hV : IsClopen V)
    (s t : SignedMeasure K) (hmap : s.map p = t.map p)
    (hs : s.totalVariation (p ⁻¹' V)ᶜ = 0)
    (ht : t.totalVariation (p ⁻¹' V)ᶜ = 0)
    (f : LocallyConstant K ℝ)
    (hfibre : ∀ x y, p x ∈ V → p y ∈ V → p x = p y → f x = f y) :
    signedFunctional s f.toContinuousMap = signedFunctional t f.toContinuousMap := by
  change (∫ᵛ x, f x ∂•s) = ∫ᵛ x, f x ∂•t
  have hsmap := VectorMeasure.integral_map (μ := s)
    (B := ContinuousLinearMap.lsmul ℝ ℝ) f.continuous.measurable
    (continuous_id.aestronglyMeasurable) (continuous_integrable s f.toContinuousMap)
  have htmap := VectorMeasure.integral_map (μ := t)
    (B := ContinuousLinearMap.lsmul ℝ ℝ) f.continuous.measurable
    (continuous_id.aestronglyMeasurable) (continuous_integrable t f.toContinuousMap)
  simp only [id_eq] at hsmap htmap
  rw [← hsmap, ← htmap, map_locallyConstant_eq p hp hV s t hmap hs ht f hfibre]

/-- Every choice of norm-preserving signed lifts inherits the reference weak-star
limit. The fibre condition is eventual for each fixed locally constant test;
no uniform stage over all tests is required. The index filter is arbitrary. -/
theorem arbitrary_lifts_tendsto [T2Space K] [TotallyDisconnectedSpace K]
    {L : Type v} [TopologicalSpace L] [T2Space L]
    [MeasurableSpace L] [BorelSpace L]
    {I : Type w} (l : Filter I) (p : K → L) (hp : Continuous p)
    (V : I → Set L) (hV : ∀ i, IsClopen (V i))
    (nu : I → SignedMeasure L) (s t : I → SignedMeasure K)
    (hsmap : ∀ i, (s i).map p = nu i) (htmap : ∀ i, (t i).map p = nu i)
    (hsmass : ∀ i, (s i).totalVariation univ = (nu i).totalVariation univ)
    (htmass : ∀ i, (t i).totalVariation univ = (nu i).totalVariation univ)
    (hsupport : ∀ i, (nu i).totalVariation (V i)ᶜ = 0)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ i, (nu i).totalVariation.real univ ≤ C)
    (hfibre : ∀ f : LocallyConstant K ℝ, ∀ᶠ i in l,
      ∀ x y, p x ∈ V i → p y ∈ V i → p x = p y → f x = f y)
    (F : WeakDual ℝ C(K, ℝ))
    (href : Tendsto (fun i => (signedFunctional (s i)).toWeakDual) l (𝓝 F)) :
    Tendsto (fun i => (signedFunctional (t i)).toWeakDual) l (𝓝 F) := by
  have hnormS (i : I) : ‖signedFunctional (s i)‖ ≤ C := by
    refine (signedFunctional_norm_le _).trans ?_
    simpa only [Measure.real, hsmass i] using hbound i
  have hnormT (i : I) : ‖signedFunctional (t i)‖ ≤ C := by
    refine (signedFunctional_norm_le _).trans ?_
    simpa only [Measure.real, htmass i] using hbound i
  have hsupportS (i : I) : (s i).totalVariation (p ⁻¹' V i)ᶜ = 0 := by
    apply totalVariation_preimage_null (s i) p hp.measurable
      (by rw [hsmap i, hsmass i]) (hV i).isClosed.measurableSet
    rw [hsmap i]; exact hsupport i
  have hsupportT (i : I) : (t i).totalVariation (p ⁻¹' V i)ᶜ = 0 := by
    apply totalVariation_preimage_null (t i) p hp.measurable
      (by rw [htmap i, htmass i]) (hV i).isClosed.measurableSet
    rw [htmap i]; exact hsupport i
  have hdiff (f : C(K, ℝ)) : Tendsto
      (fun i => signedFunctional (t i) f - signedFunctional (s i) f) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let A := (LocallyConstant.toContinuousMapAlgHom ℝ (X := K) (Y := ℝ)).range
    have hsep : A.SeparatesPoints :=
      LocallyConstant.separatesPoints_range_toContinuousMapAlgHom ℝ
    obtain ⟨g, hg⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints A hsep f
        (ε / (2 * C + 2)) (div_pos hε (by positivity))
    obtain ⟨a, ha⟩ := g.property
    change a.toContinuousMap = (g : C(K, ℝ)) at ha
    have hnear : ‖f - a.toContinuousMap‖ < ε / (2 * C + 2) := by
      rw [norm_sub_rev, ha]
      exact hg
    filter_upwards [hfibre a] with i hi
    have heq := integral_locallyConstant_eq p hp (hV i) (s i) (t i)
      (by rw [hsmap i, htmap i]) (hsupportS i) (hsupportT i) a hi
    have hbT : ‖signedFunctional (t i) (f - a.toContinuousMap)‖ ≤
        C * ‖f - a.toContinuousMap‖ :=
      ((signedFunctional (t i)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hnormT i) (norm_nonneg _))
    have hbS : ‖signedFunctional (s i) (a.toContinuousMap - f)‖ ≤
        C * ‖f - a.toContinuousMap‖ := by
      simpa only [norm_sub_rev] using
        ((signedFunctional (s i)).le_opNorm (a.toContinuousMap - f)).trans
          (mul_le_mul_of_nonneg_right (hnormS i) (norm_nonneg _))
    have hsplit : signedFunctional (t i) f - signedFunctional (s i) f =
        signedFunctional (t i) (f - a.toContinuousMap) +
        signedFunctional (s i) (a.toContinuousMap - f) := by
      simp only [map_sub]
      rw [heq]
      ring
    rw [dist_zero_right, hsplit]
    calc
      _ ≤ ‖signedFunctional (t i) (f - a.toContinuousMap)‖ +
          ‖signedFunctional (s i) (a.toContinuousMap - f)‖ := norm_add_le _ _
      _ ≤ 2 * C * ‖f - a.toContinuousMap‖ := by linarith
      _ < ε := by
        have hnorm : 0 ≤ ‖f - a.toContinuousMap‖ := norm_nonneg _
        have hscaled := (lt_div_iff₀ (by positivity : 0 < 2 * C + 2)).mp hnear
        nlinarith
  apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
  intro f
  change Tendsto (fun i => signedFunctional (t i) f) l (𝓝 (F f))
  have hrefF := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp href) f
  change Tendsto (fun i => signedFunctional (s i) f) l (𝓝 (F f)) at hrefF
  have hsum := (hdiff f).add hrefF
  simpa only [zero_add, sub_add_cancel] using hsum

end D5.S3.Topology.Measures.NormPreservingLifts
