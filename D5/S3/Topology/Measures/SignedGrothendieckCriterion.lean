/- GID: D5/S3/Topology/Measures/SignedGrothendieckCriterion
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedGrothendieckCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed raw splitting and the full real-dual clopen oscillation criterion. -/

import D5.S3.Topology.Measures.SignedRieszRepresentation
import D5.S3.Topology.Measures.L1RawSplitting
import D5.S3.Topology.Measures.ClopenDisjointization
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Signed raw splitting and signed clopen oscillation

The common finite controlling measure is not assumed regular. The density map
uses the actual L1–L∞ pairing. Its weak limit receives a regular signed
representative from signed Riesz representation, independently of the
regularity of a particular density measure. The unconditional signed raw
splitting is consumed by the full sufficient criteria. Quantitative signed
clopen oscillation excludes a positive captured-mass limit through a fixed
TV error estimate. No CH instance of either sufficient hypothesis is supplied.
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

private lemma common_rn_bounded (s : ℕ → SignedMeasure X)
    (hb : ∃ B : ℝ, ∀ n, (s n).totalVariation.real univ ≤ B) :
    ∃ B : ℝ, ∀ n, ‖rnL1 (s n) (commonMeasure s)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨B, fun n => ?_⟩
  rw [rnL1_norm _ _ (commonMeasure_vector_ac s n)]
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
  ((((ContinuousLinearMap.compL ℝ C(K, ℝ) (Lp ℝ ∞ μ) ℝ).flip
    (ContinuousMap.toLp ∞ μ ℝ)).comp
      ((ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ 1 ∞)).toLinearMap).mkContinuous 1 (by
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
      _ = ‖f‖ * ‖g‖ := by rw [one_mul])

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


private lemma l1_restrict_rnL1 (s : SignedMeasure K) (μ : Measure K)
    [IsFiniteMeasure μ] {E : Set K} (hE : MeasurableSet E) :
    L1Restriction.restrict E hE (rnL1 s μ) =
      ((s.integrable_rnDeriv μ).indicator hE).toL1 (E.indicator (s.rnDeriv μ)) := by
  apply Lp.ext
  filter_upwards [L1Restriction.coe_restrict E hE (rnL1 s μ),
    (s.integrable_rnDeriv μ).coeFn_toL1,
    ((s.integrable_rnDeriv μ).indicator hE).coeFn_toL1] with x hx hq hi
  rw [hx, hi]
  have hqx : (rnL1 s μ : K → ℝ) x = s.rnDeriv μ x := hq
  by_cases hm : x ∈ E <;> simp [hm, hqx]

/-- Unconditional signed raw splitting on any compact Hausdorff Borel space.
The two pieces are literal restrictions of the same selected input; the
complement converges against every continuous functional on the dual. -/
theorem exists_signed_raw_restriction_splitting (s : ℕ → SignedMeasure K)
    (hs : ∀ n, (s n).totalVariation.Regular)
    (hb : ∃ B : ℝ, ∀ n, (s n).totalVariation.real univ ≤ B) :
    ∃ (j : ℕ → ℕ) (E : ℕ → Set K) (r : ℝ) (sInf : SignedMeasure K),
      StrictMono j ∧ (∀ n, MeasurableSet (E n)) ∧
      Pairwise (fun i n => Disjoint (E i) (E n)) ∧
      (∀ n, s (j n) = (s (j n)).restrict (E n) + (s (j n)).restrict (E n)ᶜ) ∧
      (∀ n, (SignedMeasure.totalVariation ((s (j n)).restrict (E n))).Regular ∧
        (SignedMeasure.totalVariation ((s (j n)).restrict (E n)ᶜ)).Regular) ∧
      (∀ n, (SignedMeasure.totalVariation ((s (j n)).restrict (E n))).real univ +
        (SignedMeasure.totalVariation ((s (j n)).restrict (E n)ᶜ)).real univ =
        (s (j n)).totalVariation.real univ) ∧
      0 ≤ r ∧ Tendsto
        (fun n => (SignedMeasure.totalVariation ((s (j n)).restrict (E n))).real univ)
        atTop (𝓝 r) ∧ sInf.totalVariation.Regular ∧
      ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
        Tendsto (fun n => Φ (NormPreservingLifts.signedFunctional
          ((s (j n)).restrict (E n)ᶜ))) atTop
          (𝓝 (Φ (NormPreservingLifts.signedFunctional sInf))) := by
  let μ := commonMeasure s
  let f (n : ℕ) := rnL1 (s n) μ
  obtain ⟨j, E, hE, v, r, hj, hdisj, _, _, hweak, hr, hmass⟩ :=
    L1RawSplitting.exists_raw_restriction_splitting μ f (common_rn_bounded s hb)
  have hnorm (n : ℕ) :
      (SignedMeasure.totalVariation ((s (j n)).restrict (E n))).real univ =
        ‖L1Restriction.restrict (E n) (hE n) (f (j n))‖ := by
    rw [l1_restrict_rnL1]
    exact restriction_mass _ _ (commonMeasure_vector_ac s (j n)) (hE n)
  have hJ (n : ℕ) : densityToDual μ
      (L1Restriction.restrict (E n)ᶜ (hE n).compl (f (j n))) =
      NormPreservingLifts.signedFunctional ((s (j n)).restrict (E n)ᶜ) := by
    rw [l1_restrict_rnL1]
    exact densityToDual_indicator _ _ (commonMeasure_vector_ac s (j n)) (hE n).compl
  obtain ⟨sInf, hsInf, _, _, hlim⟩ := weak_transfer_regular μ
    (fun n => L1Restriction.restrict (E n)ᶜ (hE n).compl (f (j n))) v hweak
  refine ⟨j, E, r, sInf, hj, hE, hdisj, ?_, ?_, ?_, hr, ?_, hsInf, ?_⟩
  · intro n
    exact (signed_restrict_add_compl (s (j n)) (hE n)).1.symm
  · intro n
    exact ⟨restriction_regular _ (hs (j n)) (hE n),
      restriction_regular _ (hs (j n)) (hE n).compl⟩
  · intro n
    exact (signed_restrict_add_compl (s (j n)) (hE n)).2
  · simpa only [hnorm] using hmass
  · intro Φ
    simpa only [hJ] using hlim Φ

/-- A disjoint-diagonal total-variation condition on all bounded regular
signed weak-star-null sequences is sufficient for the full Grothendieck
sequence implication. The norm bound on the arbitrary dual input is derived,
not assumed. This theorem does not establish the diagonal hypothesis for a
CH construction. -/
theorem weak_of_disjoint_diagonal_variation
    (H : ∀ s : ℕ → SignedMeasure K,
      (∀ n, (s n).totalVariation.Regular) →
      (∃ B : ℝ, ∀ n, (s n).totalVariation.real univ ≤ B) →
      (∀ g : C(K, ℝ), Tendsto
        (fun n => NormPreservingLifts.signedFunctional (s n) g) atTop (𝓝 0)) →
      ∀ E : ℕ → Set K, (∀ n, MeasurableSet (E n)) →
        Pairwise (fun i n => Disjoint (E i) (E n)) →
        Tendsto (fun n =>
          (SignedMeasure.totalVariation ((s n).restrict (E n))).real univ) atTop (𝓝 0))
    (F : ℕ → StrongDual ℝ C(K, ℝ)) (FInf : StrongDual ℝ C(K, ℝ))
    (hF : ∀ g : C(K, ℝ), Tendsto (fun n => F n g) atTop (𝓝 (FInf g))) :
    ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
      Tendsto (fun n => Φ (F n)) atTop (𝓝 (Φ FInf)) := by
  obtain ⟨s, hs, hrep, _, hb, hzero⟩ := centered_signed_representatives F FInf hF
  intro Φ
  have hc : Tendsto (fun n => Φ (F n - FInf)) atTop (𝓝 0) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨j, E, r, sInf, hj, hE, hdisj, hdec, _, _, _, _, _, hweak⟩ :=
      exists_signed_raw_restriction_splitting (s ∘ ns) (fun n => hs (ns n))
        (by obtain ⟨B, hB⟩ := hb; exact ⟨B, fun n => hB (ns n)⟩)
    let a (n : ℕ) := (s (ns (j n))).restrict (E n)
    let b (n : ℕ) := (s (ns (j n))).restrict (E n)ᶜ
    have hselected (g : C(K, ℝ)) : Tendsto
        (fun n => NormPreservingLifts.signedFunctional (s (ns (j n))) g)
        atTop (𝓝 0) := (hzero g).comp (hns.comp hj.tendsto_atTop)
    have hsmall : Tendsto (fun n => NormPreservingLifts.signedFunctional (a n))
        atTop (𝓝 0) := by
      apply signedFunctional_small
      exact H (fun n => s (ns (j n))) (fun n => hs (ns (j n)))
        (by obtain ⟨B, hB⟩ := hb; exact ⟨B, fun n => hB (ns (j n))⟩)
        hselected E hE hdisj
    have heq (n : ℕ) : NormPreservingLifts.signedFunctional (s (ns (j n))) =
        NormPreservingLifts.signedFunctional (a n) +
          NormPreservingLifts.signedFunctional (b n) := by
      have hd : s (ns (j n)) = a n + b n := hdec n
      rw [hd]
      exact signedFunctional_add _ _
    have hbzero (g : C(K, ℝ)) : Tendsto
        (fun n => NormPreservingLifts.signedFunctional (b n) g) atTop (𝓝 0) := by
      have hsa : Tendsto (fun n => NormPreservingLifts.signedFunctional (a n) g)
          atTop (𝓝 0) := by
        have ht := ((NormedSpace.inclusionInDoubleDual ℝ C(K, ℝ) g).continuous.tendsto
          (0 : StrongDual ℝ C(K, ℝ))).comp hsmall
        convert ht using 1 <;> rfl
      have heval (n : ℕ) : NormPreservingLifts.signedFunctional (s (ns (j n))) g -
          NormPreservingLifts.signedFunctional (a n) g =
          NormPreservingLifts.signedFunctional (b n) g := by
        rw [heq]
        simp
      simpa only [heval, sub_self] using (hselected g).sub hsa
    have hlimzero : NormPreservingLifts.signedFunctional sInf = 0 :=
      weak_limit_zero_of_evaluation (fun n => NormPreservingLifts.signedFunctional (b n))
        (NormPreservingLifts.signedFunctional sInf) hweak hbzero
    have hpa : Tendsto (fun n => Φ (NormPreservingLifts.signedFunctional (a n)))
        atTop (𝓝 0) := by
      have ht := (Φ.continuous.tendsto (0 : StrongDual ℝ C(K, ℝ))).comp hsmall
      convert ht using 1 <;> first | rfl | simp only [map_zero]
    have hpb : Tendsto (fun n => Φ (NormPreservingLifts.signedFunctional (b n)))
        atTop (𝓝 0) := by simpa only [Function.comp_apply, b, hlimzero, map_zero] using hweak Φ
    have hp (n : ℕ) : Φ (NormPreservingLifts.signedFunctional (a n)) +
        Φ (NormPreservingLifts.signedFunctional (b n)) = Φ (F (ns (j n)) - FInf) := by
      rw [← map_add, ← heq, hrep]
    exact ⟨j, by simpa only [hp, add_zero] using hpa.add hpb⟩
  simpa only [map_sub, sub_add_cancel, zero_add] using hc.add_const (Φ FInf)


private lemma signedFunctional_smul (c : ℝ) (s : SignedMeasure K) (g : C(K, ℝ)) :
    NormPreservingLifts.signedFunctional (c • s) g =
      c * NormPreservingLifts.signedFunctional s g := by
  change (∫ᵛ x, g x ∂•(c • s)) = c * (∫ᵛ x, g x ∂•s)
  simpa only [smul_eq_mul] using VectorMeasure.integral_smul_vectorMeasure
    (B := ContinuousLinearMap.lsmul ℝ ℝ) (μ := s) (fun x => g x) c

private lemma variation_smul_real (c : ℝ) (s : SignedMeasure K) (A : Set K) :
    (c • s).totalVariation.real A = |c| * s.totalVariation.real A := by
  simp only [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_smul,
    measureReal_nnreal_smul_apply, coe_nnnorm, Real.norm_eq_abs]

private lemma smul_regular (c : ℝ) (s : SignedMeasure K)
    (hs : s.totalVariation.Regular) : (c • s).totalVariation.Regular := by
  letI := hs
  rw [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_smul,
    ← SignedMeasure.totalVariation_eq_variation]
  infer_instance

private lemma signed_apply_bound (s : SignedMeasure K) (A : Set K) :
    |s A| ≤ s.totalVariation.real univ := by
  have h := VectorMeasure.norm_measure_le_variation (μ := s) (E := A)
    (by rw [← SignedMeasure.totalVariation_eq_variation]; exact measure_ne_top _ _)
  rw [← SignedMeasure.totalVariation_eq_variation, Real.norm_eq_abs] at h
  exact h.trans (measureReal_mono (subset_univ _) (measure_ne_top _ _))

private lemma signedFunctional_clopen (s : SignedMeasure K) (Z : Set K)
    (hZ : IsClopen Z) :
    NormPreservingLifts.signedFunctional s
      ⟨Z.indicator (fun _ => 1), hZ.continuous_indicator continuous_const⟩ = s Z := by
  letI : IsFiniteMeasure s.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  change (∫ᵛ x, Z.indicator (fun _ => (1 : ℝ)) x ∂•s) = s Z
  simpa using (VectorMeasure.integral_indicator_const
    (B := ContinuousLinearMap.lsmul ℝ ℝ) (μ := s) (1 : ℝ) hZ.isOpen.measurableSet)

section Oscillation
variable [ZeroDimensionalSpace K]
variable (O : ∀ t : ℕ → SignedMeasure K, ∀ W : ℕ → Set K,
    (∀ n, (t n).totalVariation.Regular) →
    (∀ n, IsClopen (W n) ∧ (W n).Nonempty) →
    Pairwise (fun i n => Disjoint (W i) (W n)) →
    (∀ n, (t n).totalVariation.real univ = 1) →
    (∀ n, (1 / 2 : ℝ) ≤ (t n).toJordanDecomposition.posPart.real univ) →
    (∀ n, (t n).totalVariation (W n)ᶜ = 0) →
    ∃ Z : Set K, IsClopen Z ∧
      {n | (1 / 6 : ℝ) ≤ t n Z}.Infinite ∧ {n | t n Z = 0}.Infinite)
include O

private lemma disjoint_norm_one_no_limit
    (v : ℕ → SignedMeasure K) (hv : ∀ n, (v n).totalVariation.Regular)
    (hnorm : ∀ n, (v n).totalVariation.real univ = 1)
    (E : ℕ → Set K) (hE : ∀ n, MeasurableSet (E n))
    (hd : Pairwise (fun i n => Disjoint (E i) (E n)))
    (hc : ∀ n, (v n).totalVariation (E n)ᶜ = 0)
    (L : StrongDual ℝ C(K, ℝ))
    (hlim : ∀ g : C(K, ℝ), Tendsto
      (fun n => NormPreservingLifts.signedFunctional (v n) g) atTop (𝓝 (L g))) : False := by
  classical
  obtain ⟨n, W, t, hn, hWd, ht, c, j, hsign, hj, hnj, hct⟩ :=
    ClopenDisjointization.exists_signed_clopen_disjointization v hv hnorm E hE hd hc
      (η := (1 / 96 : ℝ)) (by norm_num) (by norm_num)
  have hprops (k : ℕ) := ht (j k)
  obtain ⟨Z, hZ, hhigh, hzero⟩ := O (fun k => c • t (j k)) (W ∘ j)
    (fun k => smul_regular c _ (hprops k).2.2.2.2.2.2.1)
    (fun k => ⟨(hprops k).1, (hprops k).2.1⟩)
    (fun a b hab => hWd (hj.injective.ne hab))
    (fun k => by rw [(hct k).1]; exact (hprops k).2.2.2.2.2.2.2.1)
    (fun k => (hct k).2.2.1)
    (fun k => by rw [(hct k).1]; exact (hprops k).2.2.2.2.2.2.2.2.1)
  let g : C(K, ℝ) := ⟨Z.indicator (fun _ => 1), hZ.continuous_indicator continuous_const⟩
  let x : ℕ → ℝ := fun k => c * NormPreservingLifts.signedFunctional (v (n (j k))) g
  let ell : ℝ := c * L g
  have hx : Tendsto x atTop (𝓝 ell) :=
    tendsto_const_nhds.mul ((hlim g).comp hnj.tendsto_atTop)
  have herr (k : ℕ) : |(c • t (j k)) Z - x k| < (1 / 48 : ℝ) := by
    have hb := signed_apply_bound (c • t (j k) - c • v (n (j k))) Z
    have he := (hprops k).2.2.2.2.2.2.2.2.2
    obtain ⟨heq, hlt⟩ := he
    rw [(hct k).2.2.2, ← heq] at hb
    have hxk : (c • v (n (j k))) Z = x k := by
      dsimp [x, g]
      rw [smul_apply, smul_eq_mul]
      rw [signedFunctional_clopen _ Z hZ]
    rw [sub_apply, hxk] at hb
    linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx (1 / 48) (by norm_num)
  by_cases hl : ell < (1 / 12 : ℝ)
  · obtain ⟨k, hk, hNk⟩ := hhigh.exists_gt N
    have he := herr k
    have ht := hN k hNk.le
    rw [Real.dist_eq] at ht
    have hp : (1 / 6 : ℝ) ≤ (c • t (j k)) Z := hk
    have ha := (abs_lt.mp he).2
    have hb := (abs_lt.mp ht).2
    linarith
  · obtain ⟨k, hk, hNk⟩ := hzero.exists_gt N
    have he := herr k
    have ht := hN k hNk.le
    rw [Real.dist_eq] at ht
    have hz : (c • t (j k)) Z = 0 := hk
    rw [hz] at he
    have ha := (abs_lt.mp he).1
    have hb := (abs_lt.mp ht).1
    linarith

private lemma injective_no_point_limit (x : ℕ → K) (p : K)
    (hx : Function.Injective x) (hlim : Tendsto x atTop (𝓝 p)) : False := by
  have hreg (a : K) : (Measure.dirac a).Regular := by
    letI : ((Measure.dirac ()).map (fun _ : Unit => a)).InnerRegular :=
      Measure.InnerRegular.map_of_continuous continuous_const
    have hr : ((Measure.dirac ()).map (fun _ : Unit => a)).Regular := inferInstance
    simpa only [Measure.map_dirac' measurable_const] using hr
  have heval (a : K) (g : C(K, ℝ)) :
      NormPreservingLifts.signedFunctional (Measure.dirac a).toSignedMeasure g = g a := by
    simpa using NormPreservingLifts.signedFunctional_sub_toSignedMeasure
      (Measure.dirac a) 0 g
  apply disjoint_norm_one_no_limit O (fun n => (Measure.dirac (x n)).toSignedMeasure)
    (fun n => by
      rw [SignedMeasure.totalVariation_eq_variation, Measure.variation_toSignedMeasure]
      exact hreg (x n))
    (fun n => by simp [SignedMeasure.totalVariation_eq_variation, Measure.real])
    (fun n => {x n}) (fun n => measurableSet_singleton (x n))
    (fun i j hij => by simpa only [disjoint_singleton] using hx.ne hij)
    (fun n => by simp [SignedMeasure.totalVariation_eq_variation])
    (NormPreservingLifts.signedFunctional (Measure.dirac p).toSignedMeasure)
  intro g
  rw [heval p g]
  exact ((g.continuous.tendsto p).comp hlim).congr'
    (Eventually.of_forall fun n => (heval (x n) g).symm)

/-- Signed clopen oscillation forces every convergent point sequence to be
eventually equal to its limit. -/
theorem eventually_eq_of_signed_clopen_oscillation (x : ℕ → K) (p : K)
    (hlim : Tendsto x atTop (𝓝 p)) : ∀ᶠ n in atTop, x n = p := by
  classical
  have hfinite : (range x).Finite := by
    by_contra hinfinite
    let e : ℕ ↪ range x := Set.Infinite.natEmbedding (range x) hinfinite
    choose f hf using fun n => (e n).property
    have hxf : Function.Injective (x ∘ f) := by
      intro i j hij
      apply e.injective
      apply Subtype.ext
      simpa only [Function.comp_apply, hf] using hij
    have hfi : Function.Injective f := by
      intro i j hij
      apply hxf
      exact congrArg x hij
    exact injective_no_point_limit O (x ∘ f) p hxf (hlim.comp hfi.nat_tendsto_atTop)
  have hclosed : IsClosed (range x \ {p}) := hfinite.sdiff.isClosed
  have hp : p ∈ (range x \ {p})ᶜ := by simp
  filter_upwards [hlim (hclosed.isOpen_compl.mem_nhds hp)] with n hn
  by_contra hne
  exact hn ⟨mem_range_self n, hne⟩

private lemma disjoint_mass_limit_zero
    (a : ℕ → SignedMeasure K) (ha : ∀ n, (a n).totalVariation.Regular)
    (E : ℕ → Set K) (hE : ∀ n, MeasurableSet (E n))
    (hd : Pairwise (fun i n => Disjoint (E i) (E n)))
    (hc : ∀ n, (a n).totalVariation (E n)ᶜ = 0)
    (r : ℝ) (hr : 0 ≤ r)
    (hq : Tendsto (fun n => (a n).totalVariation.real univ) atTop (𝓝 r))
    (L : StrongDual ℝ C(K, ℝ))
    (hlim : ∀ g : C(K, ℝ), Tendsto
      (fun n => NormPreservingLifts.signedFunctional (a n) g) atTop (𝓝 (L g))) : r = 0 := by
  by_contra hn
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hn)
  let q : ℕ → ℝ := fun n => (a n).totalVariation.real univ
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hq.eventually (eventually_gt_nhds (show r / 2 < r by linarith)))
  let v : ℕ → SignedMeasure K := fun k => (q (k + N))⁻¹ • a (k + N)
  have hqpos (k : ℕ) : 0 < q (k + N) :=
    lt_trans (by linarith : 0 < r / 2) (hN _ (Nat.le_add_left N k))
  have htail : Tendsto (fun k : ℕ => k + N) atTop atTop :=
    (strictMono_nat_of_lt_succ (by intro k; omega)).tendsto_atTop
  apply disjoint_norm_one_no_limit O v
    (fun k => smul_regular _ _ (ha (k + N)))
    (fun k => by
      rw [variation_smul_real, abs_of_pos (inv_pos.mpr (hqpos k))]
      exact inv_mul_cancel₀ (hqpos k).ne')
    (fun k => E (k + N)) (fun k => hE (k + N))
    (fun i j hij => hd (by omega : i + N ≠ j + N))
    (fun k => by
      dsimp [v]
      rw [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_smul,
        ← SignedMeasure.totalVariation_eq_variation, Measure.smul_apply, hc, smul_zero])
    (r⁻¹ • L)
  intro g
  have hi : Tendsto (fun k => (q (k + N))⁻¹) atTop (𝓝 r⁻¹) :=
    (hq.comp htail).inv₀ hrpos.ne'
  simpa only [v, signedFunctional_smul, smul_apply, smul_eq_mul, Function.comp_apply] using
    hi.mul ((hlim g).comp htail)

/-- Quantitative signed clopen oscillation implies the full real-dual
Grothendieck sequence property. O is a property of norm-one signed measures;
no norm bound is assumed on the arbitrary dual sequence. -/
theorem weak_of_signed_clopen_oscillation
    (F : ℕ → StrongDual ℝ C(K, ℝ)) (FInf : StrongDual ℝ C(K, ℝ))
    (hF : ∀ g : C(K, ℝ), Tendsto (fun n => F n g) atTop (𝓝 (FInf g))) :
    ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
      Tendsto (fun n => Φ (F n)) atTop (𝓝 (Φ FInf)) := by
  obtain ⟨s, hs, hrep, _, hb, hzero⟩ := centered_signed_representatives F FInf hF
  intro Φ
  have hc : Tendsto (fun n => Φ (F n - FInf)) atTop (𝓝 0) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨j, E, r, sInf, hj, hE, hdisj, hdec, hreg, _, hr, hmass, _, hweak⟩ :=
      exists_signed_raw_restriction_splitting (s ∘ ns) (fun n => hs (ns n))
        (by obtain ⟨B, hB⟩ := hb; exact ⟨B, fun n => hB (ns n)⟩)
    let a (n : ℕ) := (s (ns (j n))).restrict (E n)
    let b (n : ℕ) := (s (ns (j n))).restrict (E n)ᶜ
    have hselected (g : C(K, ℝ)) : Tendsto
        (fun n => NormPreservingLifts.signedFunctional (s (ns (j n))) g)
        atTop (𝓝 0) := (hzero g).comp (hns.comp hj.tendsto_atTop)
    have heq (n : ℕ) : NormPreservingLifts.signedFunctional (s (ns (j n))) =
        NormPreservingLifts.signedFunctional (a n) +
          NormPreservingLifts.signedFunctional (b n) := by
      have hd : s (ns (j n)) = a n + b n := hdec n
      rw [hd]
      exact signedFunctional_add _ _
    have halim (g : C(K, ℝ)) : Tendsto
        (fun n => NormPreservingLifts.signedFunctional (a n) g) atTop
        (𝓝 ((-NormPreservingLifts.signedFunctional sInf) g)) := by
      have hbtest := hweak (NormedSpace.inclusionInDoubleDual ℝ C(K, ℝ) g)
      change Tendsto (fun n => NormPreservingLifts.signedFunctional (b n) g) atTop
        (𝓝 (NormPreservingLifts.signedFunctional sInf g)) at hbtest
      have ht := (hselected g).sub hbtest
      have heval (n : ℕ) : NormPreservingLifts.signedFunctional (s (ns (j n))) g -
          NormPreservingLifts.signedFunctional (b n) g =
          NormPreservingLifts.signedFunctional (a n) g := by rw [heq]; simp
      simpa only [heval, zero_sub, neg_apply] using ht
    have hrzero : r = 0 := disjoint_mass_limit_zero O a (fun n => (hreg n).1)
      E hE hdisj (fun n => by
        dsimp [a]
        rw [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_restrict (hE n),
          Measure.restrict_apply (hE n).compl]
        simp) r hr hmass (-NormPreservingLifts.signedFunctional sInf) halim
    have hsmall : Tendsto (fun n => NormPreservingLifts.signedFunctional (a n))
        atTop (𝓝 0) := signedFunctional_small a (by simpa only [a, Function.comp_apply, hrzero] using hmass)
    have hbzero (g : C(K, ℝ)) : Tendsto
        (fun n => NormPreservingLifts.signedFunctional (b n) g) atTop (𝓝 0) := by
      have hsa : Tendsto (fun n => NormPreservingLifts.signedFunctional (a n) g)
          atTop (𝓝 0) := by
        have ht := ((NormedSpace.inclusionInDoubleDual ℝ C(K, ℝ) g).continuous.tendsto
          (0 : StrongDual ℝ C(K, ℝ))).comp hsmall
        convert ht using 1 <;> rfl
      have heval (n : ℕ) : NormPreservingLifts.signedFunctional (s (ns (j n))) g -
          NormPreservingLifts.signedFunctional (a n) g =
          NormPreservingLifts.signedFunctional (b n) g := by rw [heq]; simp
      simpa only [heval, sub_self] using (hselected g).sub hsa
    have hlimzero : NormPreservingLifts.signedFunctional sInf = 0 :=
      weak_limit_zero_of_evaluation (fun n => NormPreservingLifts.signedFunctional (b n))
        (NormPreservingLifts.signedFunctional sInf) hweak hbzero
    have hpa : Tendsto (fun n => Φ (NormPreservingLifts.signedFunctional (a n)))
        atTop (𝓝 0) := by
      have ht := (Φ.continuous.tendsto (0 : StrongDual ℝ C(K, ℝ))).comp hsmall
      convert ht using 1 <;> first | rfl | simp only [map_zero]
    have hpb : Tendsto (fun n => Φ (NormPreservingLifts.signedFunctional (b n)))
        atTop (𝓝 0) := by simpa only [Function.comp_apply, b, hlimzero, map_zero] using hweak Φ
    have hp (n : ℕ) : Φ (NormPreservingLifts.signedFunctional (a n)) +
        Φ (NormPreservingLifts.signedFunctional (b n)) = Φ (F (ns (j n)) - FInf) := by
      rw [← map_add, ← heq, hrep]
    exact ⟨j, by simpa only [hp, add_zero] using hpa.add hpb⟩
  simpa only [map_sub, sub_add_cancel, zero_add] using hc.add_const (Φ FInf)

#print axioms weak_of_signed_clopen_oscillation
#print axioms eventually_eq_of_signed_clopen_oscillation
#check @eventually_eq_of_signed_clopen_oscillation
#check @weak_of_signed_clopen_oscillation
end Oscillation

#print axioms exists_signed_raw_restriction_splitting
#print axioms weak_of_disjoint_diagonal_variation
#check @exists_signed_raw_restriction_splitting
#check @weak_of_disjoint_diagonal_variation

end Compact
end D5.S3.Topology.Measures.SignedGrothendieckCriterion
