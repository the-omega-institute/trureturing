/- GID: D5/S3/Analytic/Measure/FullSupportProfileTransfer
   generality: G
   mirror-B: D5/B/S3/Analytic/Measure/FullSupportProfileTransfer
   mirror-E: none(waiver:analytic-transfer)
   anchors: []
   utility: none
   digest: Nonnegative uniformly Lipschitz profiles with vanishing full-support integral converge pointwise and against every finite measure.
 -/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Topology

namespace D5.S3.Analytic.Measure.FullSupportProfileTransfer

variable {α : Type*} [PseudoMetricSpace α]
  [MeasurableSpace α] [OpensMeasurableSpace α]

/-!
The finite-measure conclusion is deliberately separated from the pointwise
argument.  Local finiteness is used only to obtain a positive finite open
neighbourhood around a putative gap; no compactness or optimizer exists in
this transfer.
-/
theorem tendsto_zero_of_full_support_integral
    (μ ν : Measure α) [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ]
    (M K : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (g : ℕ → α → ℝ)
    (hcont : ∀ j, Continuous (g j))
    (hnonneg : ∀ j x, 0 ≤ g j x)
    (hbound : ∀ j x, g j x ≤ M)
    (hlip : ∀ j, LipschitzWith (Real.toNNReal K) (g j))
    (hint : ∀ j, Integrable (g j) μ)
    (hμlim : Tendsto (fun j => ∫ x, g j x ∂μ) atTop (𝓝 0))
    (hνfin : ν Set.univ < ⊤) :
    (∀ x, Tendsto (fun j => g j x) atTop (𝓝 0)) ∧
      Tendsto (fun j => ∫ x, g j x ∂ν) atTop (𝓝 0) := by
  have hpoint : ∀ x, Tendsto (fun j => g j x) atTop (𝓝 0) := by
    intro x
    apply Metric.tendsto_atTop.2
    intro ε hε
    by_contra hbad
    have hfreq : ∃ᶠ j in atTop, ¬dist (g j x) 0 < ε := by
      rw [frequently_atTop]
      intro N
      by_contra hN
      push_neg at hN
      exact hbad ⟨N, hN⟩
    obtain ⟨U, hxU, hUopen, hUfin⟩ := μ.exists_isOpen_measure_lt_top x
    let δ : ℝ := ε / (2 * (K + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    let V : Set α := U ∩ Metric.ball x δ
    have hVopen : IsOpen V := hUopen.inter Metric.isOpen_ball
    have hxV : x ∈ V := ⟨hxU, Metric.mem_ball_self hδ⟩
    have hVpos : 0 < μ V := hVopen.measure_pos μ ⟨x, hxV⟩
    have hVfin : μ V < ⊤ :=
      lt_of_le_of_lt (measure_mono inter_subset_left) hUfin
    have hμreal : 0 < μ.real V := ENNReal.toReal_pos hVpos.ne' hVfin.ne
    let c : ℝ := (ε / 2) * μ.real V
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos (by linarith) hμreal
    have hsmall : ∀ᶠ j in atTop, (∫ x, g j x ∂μ) < c := by
      have ht := (Metric.tendsto_atTop.1 hμlim) c hc
      filter_upwards [Filter.eventually_atTop.2 ht] with j hj
      have hj' : |(∫ x, g j x ∂μ)| < c := by
        simpa only [Real.dist_eq, sub_zero] using hj
      exact lt_of_le_of_lt (le_abs_self _) hj'
    have hfreq' : ∃ᶠ j in atTop, ε ≤ g j x := by
      exact hfreq.mono (fun j hj => by
        have hj' : ε ≤ |g j x| := by
          simpa only [Real.dist_eq, sub_zero, not_lt] using hj
        simpa only [abs_of_nonneg (hnonneg j x)] using hj')
    obtain ⟨j, hjgap, hjsmall⟩ := (hfreq'.and_eventually hsmall).exists
    have hlower : c ≤ ∫ x, g j x ∂μ := by
      have hconst : ∀ y ∈ V, ε / 2 ≤ g j y := by
        intro y hy
        have hyd : dist y x < δ := Metric.mem_ball.mp hy.2
        have hKdist : K * dist y x ≤ ε / 2 := by
          have hmul : K * dist y x ≤ K * δ :=
            mul_le_mul_of_nonneg_left hyd.le hK
          have hδ' : K * δ ≤ ε / 2 := by
            dsimp [δ]
            field_simp
            nlinarith
          exact hmul.trans hδ'
        have hdist : |g j y - g j x| ≤ K * dist y x := by
          simpa only [Real.dist_eq, Real.coe_toNNReal', max_eq_left hK] using
            (hlip j).dist_le_mul y x
        have hsub : g j x - g j y ≤ |g j y - g j x| := by
          simpa only [abs_sub_comm] using le_abs_self (g j x - g j y)
        nlinarith
      calc
        c = (ε / 2) * μ.real V := rfl
        _ ≤ ∫ y in V, g j y ∂μ := by
          exact setIntegral_ge_of_const_le_real hVopen.measurableSet hVfin.ne
            hconst (hint j).integrableOn
        _ ≤ ∫ y, g j y ∂μ :=
          setIntegral_le_integral (hint j) (ae_of_all _ (hnonneg j))
    exact (not_lt_of_ge hlower) hjsmall
  letI : IsFiniteMeasure ν := ⟨hνfin⟩
  have hνint : Integrable (fun _ : α => M) ν := integrable_const M
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := ν) (F := g) (f := fun _ : α => 0) (fun _ : α => M)
    (fun j => (hcont j).aestronglyMeasurable) hνint
    (fun j => Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg j x)] using hbound j x))
    (Filter.Eventually.of_forall (fun x => hpoint x))
  refine ⟨hpoint, ?_⟩
  simpa only [integral_zero] using hDCT

end D5.S3.Analytic.Measure.FullSupportProfileTransfer
