/- GID: D5/S3/Analytic/Probability/NoncompactStrassen
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/NoncompactStrassen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar Strassen equivalence for arbitrary real laws with finite first moments. -/

import D5.S3.Analytic.Probability.CompactStrassen
import D5.S3.Analytic.Probability.FirstMomentWeakLimit
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-! Convex order and native martingale couplings for integrable real laws. -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open Econlib.Probability

noncomputable section

namespace Econlib.Probability.NoncompactStrassen

open private IsCoupling.coupling_of_weak_limit IsMartingaleCoupling.condExp_snd_eq_fst
  from D5.S3.Analytic.Probability.CompactStrassen

private lemma tight_range_of_tendsto {μ : ProbabilityMeasure ℝ}
    {μn : ℕ → ProbabilityMeasure ℝ} (hμ : Tendsto μn atTop (𝓝 μ)) :
    IsTightMeasureSet (Set.range fun n => (μn n).toMeasure) := by
  have hc : IsCompact (closure (Set.range μn)) :=
    hμ.isCompact_insert_range.of_isClosed_subset isClosed_closure
      (closure_minimal (Set.subset_insert _ _) hμ.isCompact_insert_range.isClosed)
  convert isTightMeasureSet_of_isCompact_closure hc using 1
  ext ρ
  simp only [Set.mem_range, Set.mem_ofPred_eq, exists_exists_eq_and]

private theorem exists_martingale {μ ν : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure)
    (hν : Integrable (fun x : ℝ => x) ν.toMeasure)
    (hmean : μ.expect id = ν.expect id)
    (hstop : ∀ z : ℝ, μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z) :
    ∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling μ ν π := by
  obtain ⟨πn, hπn, hμn, hνn, htail⟩ :=
    NoncompactQuantile.exists_martingale_approximations hμ hν hmean hstop
  let μn := fun n => (DiscreteLaw.condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist
  let νn := fun n => (DiscreteLaw.condMeanAtomize ν (n + 1) (Nat.succ_pos n)).toProbDist
  have hμtight := tight_range_of_tendsto hμn
  have hνtight := tight_range_of_tendsto hνn
  have htight : IsTightMeasureSet (Set.range fun n => (πn n).toMeasure) := by
    apply IsTightMeasureSet.prodMk
    · apply hμtight.subset
      rintro ρ ⟨ρ', ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (hπn n).fst_measure.symm⟩
    · apply hνtight.subset
      rintro ρ ⟨ρ', ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (hπn n).snd_measure.symm⟩
  have hcomp : IsCompact (closure (Set.range πn)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext ρ
    simp only [Set.mem_range, Set.mem_ofPred_eq, exists_exists_eq_and]
  obtain ⟨π, _, σ, hσ, hlim⟩ := hcomp.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  have hcoup : IsCoupling μ ν π := IsCoupling.coupling_of_weak_limit
    (μ_seq := fun n => μn (σ n)) (ν_seq := fun n => νn (σ n))
    (fun n => ⟨(hπn (σ n)).fst_measure, (hπn (σ n)).snd_measure⟩)
    hlim (hμn.comp hσ.tendsto_atTop) (hνn.comp hσ.tendsto_atTop)
  have hfst : Integrable (Prod.fst : ℝ × ℝ → ℝ) π.toMeasure := by
    have hh := integrable_map_measure (g := fun x : ℝ => x)
      (f := (Prod.fst : ℝ × ℝ → ℝ))
      (μ := π.toMeasure) (by rw [hcoup.1]; exact aestronglyMeasurable_id)
      measurable_fst.aemeasurable
    rw [hcoup.1] at hh
    exact hh.mp hμ
  have hsnd : Integrable (Prod.snd : ℝ × ℝ → ℝ) π.toMeasure := by
    have hh := integrable_map_measure (g := fun x : ℝ => x)
      (f := (Prod.snd : ℝ × ℝ → ℝ))
      (μ := π.toMeasure) (by rw [hcoup.2]; exact aestronglyMeasurable_id)
      measurable_snd.aemeasurable
    rw [hcoup.2] at hh
    exact hh.mp hν
  have hcts : ∀ h : ℝ → ℝ, Continuous h → (∃ M, ∀ x, |h x| ≤ M) →
      ∫ p, (p.2 - p.1) * h p.1 ∂π.toMeasure = 0 := by
    intro h hh hb
    obtain ⟨M, hM⟩ := hb
    have hM0 : 0 ≤ M := (abs_nonneg (h 0)).trans (hM 0)
    have ht := _root_.D5.S3.Analytic.Probability.FirstMomentWeakLimit.tendsto_integral_displacement
      (πn := fun n => πn (σ n)) hlim
      (fun n => (hπn (σ n)).integrable_fst)
      (fun n => (hπn (σ n)).integrable_snd)
      hfst hsnd (fun ε hε => by
        obtain ⟨R, hR, hRn⟩ := htail ε hε
        exact ⟨R, hR, fun n => hRn (σ n)⟩) h hh ⟨M, hM0, hM⟩
    have hz : Tendsto (fun n => ∫ p, (p.2 - p.1) * h p.1 ∂(πn (σ n)).toMeasure)
        atTop (𝓝 0) := by
      have heq : (fun n => ∫ p, (p.2 - p.1) * h p.1 ∂(πn (σ n)).toMeasure) =
          fun _ => (0 : ℝ) := funext fun n =>
        (hπn (σ n)).martingale h hh.measurable ⟨M, hM⟩
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique ht hz
  refine ⟨π, hcoup.fst_probability_marginal, hcoup.snd_probability_marginal,
    hfst, hsnd, ?_⟩
  exact NoncompactQuantile.tested_measurable_of_continuous hfst hsnd hcts

/-- Scalar Strassen's theorem with finite first moments and native joint conditional expectation. -/
theorem strassen_iff (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure)
    (hν : Integrable (fun x : ℝ => x) ν.toMeasure) :
    ((∫ x, x ∂μ.toMeasure = ∫ x, x ∂ν.toMeasure) ∧
      (∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ →
        Integrable (fun x => |φ x|) μ.toMeasure →
        Integrable (fun x => |φ x|) ν.toMeasure →
        ∫ x, φ x ∂μ.toMeasure ≤ ∫ x, φ x ∂ν.toMeasure)) ↔
    ∃ π : ProbabilityMeasure (ℝ × ℝ),
      π.toMeasure.map Prod.fst = μ.toMeasure ∧
      π.toMeasure.map Prod.snd = ν.toMeasure ∧
      π.toMeasure[Prod.snd | (borel ℝ).comap Prod.fst] =ᵐ[π.toMeasure] Prod.fst := by
  constructor
  · rintro ⟨hmean, hconv⟩
    have hstop : ∀ z : ℝ, μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z := by
      intro z
      exact hconv (fun x => max (x - z) 0) (convexOn_hinge_right z)
        (Measure.stopLoss_integrable hμ z).abs (Measure.stopLoss_integrable hν z).abs
    obtain ⟨π, hπ⟩ := exists_martingale hμ hν hmean hstop
    exact ⟨π, hπ.fst_measure, hπ.snd_measure, IsMartingaleCoupling.condExp_snd_eq_fst hπ⟩
  · rintro ⟨π, hfst, hsnd, hce⟩
    have hm : ((borel ℝ).comap (Prod.fst : ℝ × ℝ → ℝ)) ≤
        (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
      (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ)).comap_le
    have hfirst : Integrable (Prod.fst : ℝ × ℝ → ℝ) π.toMeasure := by
      have hh := integrable_map_measure (g := fun x : ℝ => x)
        (f := (Prod.fst : ℝ × ℝ → ℝ)) (μ := π.toMeasure)
        (by rw [hfst]; exact aestronglyMeasurable_id) measurable_fst.aemeasurable
      rw [hfst] at hh
      exact hh.mp hμ
    have hsecond : Integrable (Prod.snd : ℝ × ℝ → ℝ) π.toMeasure := by
      have hh := integrable_map_measure (g := fun x : ℝ => x)
        (f := (Prod.snd : ℝ × ℝ → ℝ)) (μ := π.toMeasure)
        (by rw [hsnd]; exact aestronglyMeasurable_id) measurable_snd.aemeasurable
      rw [hsnd] at hh
      exact hh.mp hν
    have hfirst_int : ∫ p, p.1 ∂π.toMeasure = ∫ x, x ∂μ.toMeasure := by
      rw [← hfst]
      exact (integral_map measurable_fst.aemeasurable
        (show AEStronglyMeasurable (fun x : ℝ => x) _ from aestronglyMeasurable_id)).symm
    have hsecond_int : ∫ p, p.2 ∂π.toMeasure = ∫ x, x ∂ν.toMeasure := by
      rw [← hsnd]
      exact (integral_map measurable_snd.aemeasurable
        (show AEStronglyMeasurable (fun x : ℝ => x) _ from aestronglyMeasurable_id)).symm
    refine ⟨?_, ?_⟩
    · calc
        _ = ∫ p, p.1 ∂π.toMeasure := hfirst_int.symm
        _ = ∫ p, π.toMeasure[Prod.snd | (borel ℝ).comap Prod.fst] p ∂π.toMeasure := integral_congr_ae hce.symm
        _ = _ := (integral_condExp hm).trans hsecond_int
    · intro φ hφ hφμ hφν
      have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
      have hiμ : Integrable φ μ.toMeasure := (integrable_norm_iff hc.aestronglyMeasurable).mp (by simpa only [Real.norm_eq_abs] using hφμ)
      have hiν : Integrable φ ν.toMeasure := (integrable_norm_iff hc.aestronglyMeasurable).mp (by simpa only [Real.norm_eq_abs] using hφν)
      have hφfirst : Integrable (fun p : ℝ × ℝ => φ p.1) π.toMeasure := by
        have hh := integrable_map_measure (f := (Prod.fst : ℝ × ℝ → ℝ))
          (μ := π.toMeasure) (g := φ) hc.aestronglyMeasurable measurable_fst.aemeasurable
        rw [hfst] at hh
        exact hh.mp hiμ
      have hφsecond : Integrable (fun p : ℝ × ℝ => φ p.2) π.toMeasure := by
        have hh := integrable_map_measure (f := (Prod.snd : ℝ × ℝ → ℝ))
          (μ := π.toMeasure) (g := φ) hc.aestronglyMeasurable measurable_snd.aemeasurable
        rw [hsnd] at hh
        exact hh.mp hiν
      have hj := hφ.map_condExp_le_univ hm hc.lowerSemicontinuous hsecond hφsecond
      have hle : (fun p : ℝ × ℝ => φ p.1) ≤ᵐ[π.toMeasure]
          π.toMeasure[φ ∘ Prod.snd | (borel ℝ).comap Prod.fst] := by
        filter_upwards [hj, hce] with p hp hcp
        simpa only [Function.comp_apply, hcp] using hp
      have hb := integral_mono_ae hφfirst integrable_condExp hle
      rw [integral_condExp hm] at hb
      rw [← hfst, integral_map measurable_fst.aemeasurable hc.aestronglyMeasurable,
        ← hsnd, integral_map measurable_snd.aemeasurable hc.aestronglyMeasurable]
      exact hb

end Econlib.Probability.NoncompactStrassen
