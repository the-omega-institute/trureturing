/- GID: D5/S3/Topology/Measures/SignedGrothendieckCriterion
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedGrothendieckCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed density and dual-transfer bridges for the disjoint-variation criterion. -/

import D5.S3.Topology.Measures.SignedRieszRepresentation
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Signed bridges for a disjoint-variation sufficient criterion

The common finite controlling measure is not assumed regular. The density map
uses the actual L1–L∞ pairing. Its weak limit receives a regular signed
representative from signed Riesz representation, independently of the
regularity of a particular density measure. The full raw splitting and the
outer sufficient criterion are not asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace D5.S3.Topology.Measures.SignedGrothendieckCriterion

universe u

section Density
variable {X : Type u} [MeasurableSpace X]

private def commonMeasure (s : ℕ → SignedMeasure X) : Measure X :=
  (Measure.sum fun n => (s n).totalVariation).toFinite

private instance commonMeasure_finite (s : ℕ → SignedMeasure X) :
    IsFiniteMeasure (commonMeasure s) := by
  dsimp [commonMeasure, SignedMeasure.totalVariation_zero]
  infer_instance

private lemma commonMeasure_ac (s : ℕ → SignedMeasure X) (n : ℕ) :
    (s n).totalVariation ≪ commonMeasure s := by
  exact (Measure.absolutelyContinuous_sum_right (μs := fun n => (s n).totalVariation) n
    (Measure.AbsolutelyContinuous.refl (s n).totalVariation)).trans
      (absolutelyContinuous_toFinite _)

private lemma commonMeasure_vector_ac (s : ℕ → SignedMeasure X) (n : ℕ) :
    s n ≪ᵥ (commonMeasure s).toENNRealVectorMeasure := by
  apply (SignedMeasure.absolutelyContinuous_ennreal_iff _ _).mpr
  simpa using commonMeasure_ac s n

private lemma commonMeasure_zero : commonMeasure (fun _ => (0 : SignedMeasure X)) = 0 := by
  simp [commonMeasure, SignedMeasure.totalVariation_zero]

private def rnL1 (s : SignedMeasure X) (μ : Measure X) : Lp ℝ 1 μ :=
  (s.integrable_rnDeriv μ).toL1 (s.rnDeriv μ)

private lemma density_mass (μ : Measure X) (q : X → ℝ) (hq : Integrable q μ) :
    (SignedMeasure.totalVariation (μ.withDensityᵥ q)).real univ = ‖hq.toL1 q‖ := by
  rw [SignedMeasure.totalVariation_eq_variation, Measure.variation_withDensityᵥ hq,
    Measure.real, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, Integrable.norm_toL1_eq_lintegral_enorm]

private lemma rnL1_reconstruct (s : SignedMeasure X) (μ : Measure X) [IsFiniteMeasure μ]
    (h : s ≪ᵥ μ.toENNRealVectorMeasure) :
    μ.withDensityᵥ (s.rnDeriv μ) = s :=
  s.withDensityᵥ_rnDeriv_eq μ h

private lemma rnL1_norm (s : SignedMeasure X) (μ : Measure X) [IsFiniteMeasure μ]
    (h : s ≪ᵥ μ.toENNRealVectorMeasure) :
    ‖rnL1 s μ‖ = s.totalVariation.real univ := by
  change ‖(s.integrable_rnDeriv μ).toL1 (s.rnDeriv μ)‖ = _
  rw [← density_mass μ _ (s.integrable_rnDeriv μ), rnL1_reconstruct s μ h]

private lemma density_indicator_restrict (μ : Measure X) (q : X → ℝ)
    (hq : Integrable q μ) {E : Set X} (hE : MeasurableSet E) :
    μ.withDensityᵥ (E.indicator q) = (μ.withDensityᵥ q).restrict E := by
  ext A hA
  rw [withDensityᵥ_apply (hq.indicator hE) hA,
    VectorMeasure.restrict_apply _ hE hA,
    withDensityᵥ_apply hq (hA.inter hE), setIntegral_indicator hE]

private lemma rnL1_indicator_restrict (s : SignedMeasure X) (μ : Measure X)
    [IsFiniteMeasure μ] (h : s ≪ᵥ μ.toENNRealVectorMeasure)
    {E : Set X} (hE : MeasurableSet E) :
    μ.withDensityᵥ (E.indicator (s.rnDeriv μ)) = s.restrict E := by
  rw [density_indicator_restrict μ _ (s.integrable_rnDeriv μ) hE,
    rnL1_reconstruct s μ h]

private lemma restriction_mass (s : SignedMeasure X) (μ : Measure X)
    [IsFiniteMeasure μ] (h : s ≪ᵥ μ.toENNRealVectorMeasure)
    {E : Set X} (hE : MeasurableSet E) :
    (SignedMeasure.totalVariation (s.restrict E)).real univ =
      ‖((s.integrable_rnDeriv μ).indicator hE).toL1 (E.indicator (s.rnDeriv μ))‖ := by
  rw [← rnL1_indicator_restrict s μ h hE]
  exact density_mass μ _ _

private lemma signed_restrict_add_compl (s : SignedMeasure X)
    {E : Set X} (hE : MeasurableSet E) :
    s.restrict E + s.restrict Eᶜ = s ∧
      (SignedMeasure.totalVariation (s.restrict E)).real univ +
        (SignedMeasure.totalVariation (s.restrict Eᶜ)).real univ = s.totalVariation.real univ := by
  letI : IsFiniteMeasure s.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  refine ⟨VectorMeasure.restrict_add_restrict_compl hE, ?_⟩
  simp only [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_restrict hE,
    VectorMeasure.variation_restrict hE.compl, measureReal_restrict_apply_univ]
  exact measureReal_add_measureReal_compl hE

private lemma common_rn_data (s : ℕ → SignedMeasure X) :
    (∀ n, (commonMeasure s).withDensityᵥ ((s n).rnDeriv (commonMeasure s)) = s n) ∧
    (∀ n, rnL1 (s n) (commonMeasure s) =ᵐ[commonMeasure s]
      (s n).rnDeriv (commonMeasure s)) ∧
    (∀ n, ‖rnL1 (s n) (commonMeasure s)‖ = (s n).totalVariation.real univ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact rnL1_reconstruct _ _ (commonMeasure_vector_ac s n)
  · intro n
    exact ((s n).integrable_rnDeriv _).coeFn_toL1
  · intro n
    exact rnL1_norm _ _ (commonMeasure_vector_ac s n)

private lemma common_rn_bounded (s : ℕ → SignedMeasure X)
    (hb : ∃ B : ℝ, ∀ n, (s n).totalVariation.real univ ≤ B) :
    ∃ B : ℝ, ∀ n, ‖rnL1 (s n) (commonMeasure s)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨B, fun n => ?_⟩
  rw [(common_rn_data s).2.2 n]
  exact hB n

end Density

section Compact
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

private lemma restriction_regular (s : SignedMeasure K) (hs : s.totalVariation.Regular)
    {E : Set K} (hE : MeasurableSet E) : (SignedMeasure.totalVariation (s.restrict E)).Regular := by
  letI : s.totalVariation.Regular := hs
  rw [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_restrict hE,
    ← SignedMeasure.totalVariation_eq_variation]
  exact Measure.Regular.restrict_of_measure_ne_top (measure_ne_top _ _)

private def densityToDual (μ : Measure K) [IsFiniteMeasure μ] :
    Lp ℝ 1 μ →L[ℝ] StrongDual ℝ C(K, ℝ) :=
  ((ContinuousLinearMap.compL ℝ C(K, ℝ) (Lp ℝ ∞ μ) ℝ).flip
    (ContinuousMap.toLp ∞ μ ℝ)).comp
      ((ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ 1 ∞)

private lemma densityToDual_apply (μ : Measure K) [IsFiniteMeasure μ]
    (f : Lp ℝ 1 μ) (g : C(K, ℝ)) :
    densityToDual μ f g = ∫ x, f x * g x ∂μ := by
  change (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ 1 ∞ f
    (ContinuousMap.toLp ∞ μ ℝ g) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (μ := μ) (p := ∞) (𝕜 := ℝ) g] with x hx
  change f x * ((ContinuousMap.toLp ∞ μ ℝ g : Lp ℝ ∞ μ) x) = f x * g x
  rw [hx]


private lemma signedFunctional_density (μ : Measure K) [IsFiniteMeasure μ]
    (r : K → ℝ) (hr : Integrable r μ) (g : C(K, ℝ)) :
    NormPreservingLifts.signedFunctional (μ.withDensityᵥ r) g =
      ∫ x, r x * g x ∂μ := by
  letI := isFiniteMeasure_withDensity_ofReal hr.2
  letI := isFiniteMeasure_withDensity_ofReal hr.neg.2
  have hp : AEMeasurable (fun x => ENNReal.ofReal (r x)) μ :=
    hr.aemeasurable.ennreal_ofReal
  have hn : AEMeasurable (fun x => ENNReal.ofReal (-r x)) μ :=
    hr.neg.aemeasurable.ennreal_ofReal
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (r x) < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hnt : ∀ᵐ x ∂μ, ENNReal.ofReal (-r x) < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hgp : Integrable (fun x => (ENNReal.ofReal (r x)).toReal • g x) μ :=
    (integrable_withDensity_iff_integrable_smul₀' hp hpt).mp
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hgn : Integrable (fun x => (ENNReal.ofReal (-r x)).toReal • g x) μ :=
    (integrable_withDensity_iff_integrable_smul₀' hn hnt).mp
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hr,
    D5.S3.Topology.Measures.NormPreservingLifts.signedFunctional_sub_toSignedMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hp hpt,
    integral_withDensity_eq_integral_toReal_smul₀ hn hnt,
    ← integral_sub hgp hgn]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [smul_eq_mul, ← sub_mul]
  congr 1
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  by_cases h : 0 ≤ r x
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · have hle : r x ≤ 0 := le_of_not_ge h
    simp [max_eq_right hle, max_eq_left (neg_nonneg.mpr hle)]

private lemma densityToDual_toL1 (μ : Measure K) [IsFiniteMeasure μ]
    (q : K → ℝ) (hq : Integrable q μ) :
    densityToDual μ (hq.toL1 q) =
      NormPreservingLifts.signedFunctional (μ.withDensityᵥ q) := by
  ext g
  rw [densityToDual_apply, signedFunctional_density μ q hq]
  apply integral_congr_ae
  filter_upwards [hq.coeFn_toL1] with x hx
  rw [hx]

private lemma densityToDual_norm_le (μ : Measure K) [IsFiniteMeasure μ] :
    ‖densityToDual μ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro g
  let A := ContinuousMap.toLp ∞ μ ℝ (E := ℝ)
  have hA : ‖A g‖ ≤ ‖g‖ := by
    have hAn : ‖A‖ ≤ 1 := by
      simpa [A] using (ContinuousMap.toLp_norm_le (p := ∞) (μ := μ) (𝕜 := ℝ) (E := ℝ))
    exact (A.le_opNorm g).trans (by simpa using mul_le_mul_of_nonneg_right hAn (norm_nonneg g))
  let B := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  change ‖B.lpPairing μ 1 ∞ f (A g)‖ ≤ _
  calc
    _ = ‖L1.integral (B.holder 1 f (A g))‖ := by
      rw [L1.integral_eq]
      rfl
    _ ≤ ‖B.holder 1 f (A g)‖ := L1.norm_integral_le _
    _ ≤ ‖B‖ * ‖f‖ * ‖A g‖ := B.norm_holder_apply_apply_le _ _
    _ ≤ 1 * ‖f‖ * ‖g‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_lsmul_le
    _ = ‖f‖ * ‖g‖ := by rw [one_mul]

private lemma densityToDual_rnL1 (s : SignedMeasure K) (μ : Measure K)
    [IsFiniteMeasure μ] (h : s ≪ᵥ μ.toENNRealVectorMeasure) :
    densityToDual μ (rnL1 s μ) = NormPreservingLifts.signedFunctional s := by
  rw [rnL1, densityToDual_toL1, rnL1_reconstruct s μ h]

private lemma densityToDual_indicator (s : SignedMeasure K) (μ : Measure K)
    [IsFiniteMeasure μ] (h : s ≪ᵥ μ.toENNRealVectorMeasure)
    {E : Set K} (hE : MeasurableSet E) :
    densityToDual μ (((s.integrable_rnDeriv μ).indicator hE).toL1
      (E.indicator (s.rnDeriv μ))) =
      NormPreservingLifts.signedFunctional (s.restrict E) := by
  rw [densityToDual_toL1, rnL1_indicator_restrict s μ h hE]

private lemma weak_transfer_regular (μ : Measure K) [IsFiniteMeasure μ]
    (v : ℕ → Lp ℝ 1 μ) (vInf : Lp ℝ 1 μ)
    (hv : ∀ ψ : StrongDual ℝ (Lp ℝ 1 μ),
      Tendsto (fun n => ψ (v n)) atTop (𝓝 (ψ vInf))) :
    ∃ sInf : SignedMeasure K, sInf.totalVariation.Regular ∧
      NormPreservingLifts.signedFunctional sInf = densityToDual μ vInf ∧
      sInf.totalVariation.real univ = ‖densityToDual μ vInf‖ ∧
      ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
        Tendsto (fun n => Φ (densityToDual μ (v n))) atTop
          (𝓝 (Φ (NormPreservingLifts.signedFunctional sInf))) := by
  obtain ⟨sInf, hsInf, hrep, hnorm⟩ :=
    SignedRieszRepresentation.signed_riesz_markov_kakutani (K := K) |>.2.2
      (densityToDual μ vInf)
  refine ⟨sInf, hsInf, hrep, hnorm, ?_⟩
  intro Φ
  rw [hrep]
  exact hv (Φ.comp (densityToDual μ))

private lemma centered_uniform_bound (F : ℕ → StrongDual ℝ C(K, ℝ))
    (FInf : StrongDual ℝ C(K, ℝ))
    (hF : ∀ g : C(K, ℝ), Tendsto (fun n => F n g) atTop (𝓝 (FInf g))) :
    ∃ B : ℝ, ∀ n, ‖F n - FInf‖ ≤ B := by
  apply banach_steinhaus
  intro g
  have hg : Tendsto (fun n => (F n - FInf) g) atTop (𝓝 0) := by
    simpa using (hF g).sub_const (FInf g)
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hg).exists_norm_le
  exact ⟨B, fun n => hB _ (mem_range_self n)⟩

private lemma centered_signed_representatives (F : ℕ → StrongDual ℝ C(K, ℝ))
    (FInf : StrongDual ℝ C(K, ℝ))
    (hF : ∀ g : C(K, ℝ), Tendsto (fun n => F n g) atTop (𝓝 (FInf g))) :
    ∃ s : ℕ → SignedMeasure K,
      (∀ n, (s n).totalVariation.Regular) ∧
      (∀ n, NormPreservingLifts.signedFunctional (s n) = F n - FInf) ∧
      (∀ n, (s n).totalVariation.real univ = ‖F n - FInf‖) ∧
      (∃ B : ℝ, ∀ n, (s n).totalVariation.real univ ≤ B) ∧
      ∀ g : C(K, ℝ), Tendsto
        (fun n => NormPreservingLifts.signedFunctional (s n) g) atTop (𝓝 0) := by
  classical
  have hr := fun n =>
    (SignedRieszRepresentation.signed_riesz_markov_kakutani (K := K)).2.2 (F n - FInf)
  choose s hs hrep hnorm using hr
  obtain ⟨B, hB⟩ := centered_uniform_bound F FInf hF
  refine ⟨s, hs, hrep, hnorm, ⟨B, ?_⟩, ?_⟩
  · intro n
    rw [hnorm n]
    exact hB n
  · intro g
    simp_rw [hrep]
    simpa using (hF g).sub_const (FInf g)

private lemma weak_limit_zero_of_evaluation (v : ℕ → StrongDual ℝ C(K, ℝ))
    (vInf : StrongDual ℝ C(K, ℝ))
    (hv : ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
      Tendsto (fun n => Φ (v n)) atTop (𝓝 (Φ vInf)))
    (hzero : ∀ g : C(K, ℝ), Tendsto (fun n => v n g) atTop (𝓝 0)) :
    vInf = 0 := by
  ext g
  exact tendsto_nhds_unique (hv (NormedSpace.inclusionInDoubleDual ℝ C(K, ℝ) g))
    (hzero g)

private lemma signedFunctional_add (s t : SignedMeasure K) :
    NormPreservingLifts.signedFunctional (s + t) =
      NormPreservingLifts.signedFunctional s + NormPreservingLifts.signedFunctional t := by
  ext g
  change (∫ᵛ x, g x ∂•(s + t)) = (∫ᵛ x, g x ∂•s) + (∫ᵛ x, g x ∂•t)
  apply VectorMeasure.integral_add_vectorMeasure
  all_goals
    rw [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation]
    exact g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma signedFunctional_small (s : ℕ → SignedMeasure K)
    (hs : Tendsto (fun n => (s n).totalVariation.real univ) atTop (𝓝 0)) :
    Tendsto (fun n => NormPreservingLifts.signedFunctional (s n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => NormPreservingLifts.signedFunctional_norm_le (s n)) hs

#print axioms commonMeasure_vector_ac
#print axioms commonMeasure_zero
#print axioms common_rn_data
#print axioms common_rn_bounded
#print axioms density_indicator_restrict
#print axioms restriction_mass
#print axioms signed_restrict_add_compl
#print axioms restriction_regular
#print axioms densityToDual_apply
#print axioms densityToDual_toL1
#print axioms densityToDual_norm_le
#print axioms densityToDual_rnL1
#print axioms densityToDual_indicator
#print axioms weak_transfer_regular
#print axioms centered_uniform_bound
#print axioms centered_signed_representatives
#print axioms weak_limit_zero_of_evaluation
#print axioms signedFunctional_add
#print axioms signedFunctional_small
#check @common_rn_data
#check @restriction_mass
#check @restriction_regular
#check @densityToDual
#check @densityToDual_norm_le
#check @weak_transfer_regular
#check @centered_signed_representatives
#check @weak_limit_zero_of_evaluation
#check @Filter.tendsto_of_subseq_tendsto

end Compact
end D5.S3.Topology.Measures.SignedGrothendieckCriterion
