/- GID: D5/S3/Topology/Measures/SignedWeakStarCompactness
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedWeakStarCompactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact metric signed-measure sequences admit represented weak-star convergent subsequences with the same total-variation bound. -/

import D5.S3.Topology.Measures.NormPreservingLifts
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Represented weak-star subsequences for bounded signed measures

On a compact metric Borel space, a sequence of finite signed measures with a
common total-variation bound has a strictly monotone weak-star convergent
subsequence whose limit is an actual signed measure with the same bound.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace D5.S3.Topology.Measures.SignedWeakStarCompactness

universe u

variable {K : Type u} [MetricSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

noncomputable def signedPairMeasure (p : FiniteMeasure K × FiniteMeasure K) : SignedMeasure K :=
  p.1.toMeasure.toSignedMeasure - p.2.toMeasure.toSignedMeasure

noncomputable def jordanPair (s : SignedMeasure K) : FiniteMeasure K × FiniteMeasure K :=
  (⟨s.toJordanDecomposition.posPart, inferInstance⟩,
    ⟨s.toJordanDecomposition.negPart, inferInstance⟩)

noncomputable def pairWeakFunctional (p : FiniteMeasure K × FiniteMeasure K) :
    WeakDual ℝ C(K, ℝ) :=
  (NormPreservingLifts.signedFunctional (signedPairMeasure p)).toWeakDual

def pairBounded (C : ℝ≥0) : Set (FiniteMeasure K × FiniteMeasure K) :=
  {p | p.1.mass ≤ C ∧ p.2.mass ≤ C ∧ p.1.mass + p.2.mass ≤ C}

private lemma signedPairMeasure_jordanPair (s : SignedMeasure K) :
    signedPairMeasure (jordanPair s) = s := by
  simpa [signedPairMeasure, jordanPair, JordanDecomposition.toSignedMeasure]
    using s.toSignedMeasure_toJordanDecomposition

private lemma jordanPair_mass_sum (s : SignedMeasure K) :
    ((jordanPair s).1.mass + (jordanPair s).2.mass : ℝ≥0∞) = s.totalVariation univ := by
  simp [jordanPair, FiniteMeasure.mass, SignedMeasure.totalVariation,
    ENNReal.coe_add]

private lemma jordanPair_mem_pairBounded (C : ℝ) (hC : 0 ≤ C)
    (s : SignedMeasure K) (hs : s.totalVariation.real univ ≤ C) :
    jordanPair s ∈ pairBounded (C.toNNReal) := by
  have hsum : ((jordanPair s).1.mass + (jordanPair s).2.mass : ℝ≥0∞) ≤ ENNReal.ofReal C := by
    rw [jordanPair_mass_sum]
    apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
    simpa [Measure.real, ENNReal.toReal_ofReal hC] using hs
  have hsum' : (jordanPair s).1.mass + (jordanPair s).2.mass ≤ C.toNNReal := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.ofReal_eq_coe_nnreal hC] at hsum
    rw [Real.toNNReal_of_nonneg hC]
    simpa only [ENNReal.coe_add] using hsum
  exact ⟨le_trans (le_add_of_nonneg_right (by positivity)) hsum',
    le_trans (le_add_of_nonneg_left (by positivity)) hsum', hsum'⟩

private lemma continuous_pairWeakFunctional :
    Continuous (pairWeakFunctional (K := K)) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  have hEq : (fun p : FiniteMeasure K × FiniteMeasure K =>
      pairWeakFunctional p f) =
      (fun p => (∫ x, f x ∂p.1.toMeasure) - ∫ x, f x ∂p.2.toMeasure) := by
    funext p
    exact NormPreservingLifts.signedFunctional_sub_toSignedMeasure
      p.1.toMeasure p.2.toMeasure f
  rw [hEq]
  exact (FiniteMeasure.continuous_integral_continuousMap f).comp continuous_fst |>.sub
    ((FiniteMeasure.continuous_integral_continuousMap f).comp continuous_snd)

private lemma isCompact_pairBounded (C : ℝ≥0) :
    IsCompact (pairBounded (K := K) C) := by
  let A : Set (FiniteMeasure K) := {a | a.mass ≤ C}
  let q : FiniteMeasure K × FiniteMeasure K → ℝ≥0 := fun p => p.1.mass + p.2.mass
  have hA : IsCompact A := by
    simpa [A] using isCompact_setOfPred_finiteMeasure_le_of_compactSpace K C
  have hprod : IsCompact (A ×ˢ A) := hA.prod hA
  have hq : Continuous q :=
    (FiniteMeasure.continuous_mass.comp continuous_fst).add
      (FiniteMeasure.continuous_mass.comp continuous_snd)
  have hclosed : IsClosed {p | q p ≤ C} := isClosed_le hq continuous_const
  have heq : pairBounded (K := K) C = (A ×ˢ A) ∩ {p | q p ≤ C} := by
    ext p
    simp [pairBounded, A, q, and_assoc, and_left_comm, and_comm]
  rw [heq]
  exact hprod.inter_right hclosed

set_option maxHeartbeats 800000 in
theorem exists_subsequence_tendsto_signedFunctional (C : ℝ) (hC : 0 ≤ C)
    (s : ℕ → SignedMeasure K)
    (hbound : ∀ n, (s n).totalVariation.real univ ≤ C) :
    ∃ (phi : ℕ → ℕ) (μ : SignedMeasure K), StrictMono phi ∧
      μ.totalVariation.real univ ≤ C ∧
      Tendsto (fun n =>
        (NormPreservingLifts.signedFunctional (s (phi n))).toWeakDual) atTop
        (𝓝 (NormPreservingLifts.signedFunctional μ).toWeakDual) := by
  let Cnn : ℝ≥0 := C.toNNReal
  let P : Set (FiniteMeasure K × FiniteMeasure K) := pairBounded Cnn
  have hP : IsCompact P := by
    simpa [P] using isCompact_pairBounded (K := K) Cnn
  let W : Set (WeakDual ℝ C(K, ℝ)) := pairWeakFunctional '' P
  have hW : IsCompact W := hP.image continuous_pairWeakFunctional
  letI : CompactSpace W := isCompact_iff_compactSpace.mp hW
  letI : TopologicalSpace.MetrizableSpace W :=
    _root_.WeakDual.metrizable_of_isCompact ℝ C(K, ℝ) W hW
  let z : ℕ → W := fun n =>
    ⟨pairWeakFunctional (jordanPair (s n)),
      mem_image_of_mem (pairWeakFunctional (K := K))
        (jordanPair_mem_pairBounded C hC (s n) (hbound n))⟩
  obtain ⟨zlim, phi, hphi, hz⟩ := CompactSpace.tendsto_subseq z
  obtain ⟨p, hpP, hpW⟩ := zlim.property
  let μ : SignedMeasure K := signedPairMeasure p
  have hconv : Tendsto (fun n => pairWeakFunctional (jordanPair (s (phi n)))) atTop
      (𝓝 (pairWeakFunctional p)) := by
    have hz' := tendsto_subtype_rng.mp hz
    change Tendsto (fun n => pairWeakFunctional (jordanPair (s (phi n)))) atTop
      (𝓝 (zlim : WeakDual ℝ C(K, ℝ))) at hz'
    rw [← hpW] at hz'
    exact hz'
  have hμbound : μ.totalVariation.real univ ≤ C := by
    have hvar : μ.totalVariation ≤ p.1.toMeasure + p.2.toMeasure := by
      change (signedPairMeasure p).totalVariation ≤ p.1.toMeasure + p.2.toMeasure
      exact NormPreservingLifts.totalVariation_sub_toSignedMeasure_le
        p.1.toMeasure p.2.toMeasure
    have huniv : μ.totalVariation univ ≤ (p.1.toMeasure + p.2.toMeasure) univ :=
      Measure.le_iff.1 hvar univ MeasurableSet.univ
    have hpSum : p.1.mass + p.2.mass ≤ Cnn := by
      exact (show p ∈ pairBounded Cnn by simpa [P] using hpP).2.2
    have hsumP : (p.1.toMeasure + p.2.toMeasure) univ ≤ (Cnn : ℝ≥0∞) := by
      have hcoe :
          (↑(p.1.mass + p.2.mass) : ℝ≥0∞) ≤ (Cnn : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr hpSum
      simpa [Measure.add_apply, FiniteMeasure.ennreal_mass, ENNReal.coe_add] using hcoe
    rw [Measure.real]
    have hCeq : (Cnn : ℝ≥0∞).toReal = C := by
      simp [Cnn, Real.toNNReal_of_nonneg hC]
    rw [← hCeq]
    exact ENNReal.toReal_mono (by finiteness) (huniv.trans hsumP)
  refine ⟨phi, μ, hphi, hμbound, ?_⟩
  simpa [pairWeakFunctional, μ, signedPairMeasure_jordanPair] using hconv

end D5.S3.Topology.Measures.SignedWeakStarCompactness
