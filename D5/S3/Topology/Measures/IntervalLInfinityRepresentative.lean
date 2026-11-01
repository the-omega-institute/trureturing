/- GID: D5/S3/Topology/Measures/IntervalLInfinityRepresentative
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/IntervalLInfinityRepresentative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Internal essential-supremum translations yield unique continuous representatives with a common closed-interval modulus. -/

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic

set_option autoImplicit false
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology

namespace D5.S3.Topology.Measures.IntervalLInfinityRepresentative
variable {E : Type*} [NormedAddCommGroup E]

private theorem internal_ae_pair {f : ℝ → E} (hf : StronglyMeasurable f)
    {T δ ε : ℝ} (hε : 0 ≤ ε)
    (htrans : ∀ h : ℝ, 0 < h → h < δ → h < T →
      eLpNorm (fun t => f (t+h)-f t) ∞ (volume.restrict (Ioc 0 (T-h))) <
        ENNReal.ofReal ε) :
    ∀ᵐ z ∂(volume.prod volume : Measure (ℝ × ℝ)),
      z.1 ∈ Ioc 0 T → z.2 ∈ Ioc 0 T → |z.2-z.1| < δ →
        ‖f z.2-f z.1‖ ≤ ε := by
  let P : ℝ × ℝ → Prop := fun z =>
    0 < z.2 → z.2 < δ → z.2 < T → z.1 ∈ Ioc 0 (T-z.2) →
      ‖f (z.1+z.2)-f z.1‖ ≤ ε
  have hPm : MeasurableSet {z | P z} := by
    have hn : Measurable (fun z : ℝ × ℝ => ‖f (z.1+z.2)-f z.1‖) :=
      ((hf.comp_measurable (measurable_fst.add measurable_snd)).sub
        (hf.comp_measurable measurable_fst)).norm.measurable
    dsimp [P]
    measurability
  have hP : ∀ᵐ z ∂(volume.prod volume : Measure (ℝ × ℝ)), P z := by
    apply (ae_prod_iff_ae_ae hPm).2
    -- First use the other order of Fubini, where the shift is fixed.
    rw [ae_ae_comm hPm]
    apply ae_of_all
    intro h
    by_cases hh : 0 < h ∧ h < δ ∧ h < T
    · have hm : StronglyMeasurable (fun t => f (t+h)-f t) :=
        (hf.comp_measurable (measurable_id.add_const h)).sub hf
      have hb := ae_le_eLpNormEssSup (f := fun t => f (t+h)-f t)
        (μ := volume.restrict (Ioc 0 (T-h)))
      rw [← eLpNorm_exponent_top hm.aestronglyMeasurable] at hb
      have hn := htrans h hh.1 hh.2.1 hh.2.2
      have hb' : ∀ᵐ t ∂volume, t ∈ Ioc 0 (T-h) → ‖f (t+h)-f t‖ ≤ ε := by
        apply (ae_restrict_iff' measurableSet_Ioc).1
        filter_upwards [hb] with t ht
        exact (ENNReal.ofReal_le_ofReal_iff hε).1 (by
          simpa only [← ofReal_norm] using ht.trans hn.le)
      exact hb'.mono fun t ht _ _ _ => ht
    · exact ae_of_all _ fun t ht hd hT => False.elim (hh ⟨ht,hd,hT⟩)
  have hs := (measurePreserving_prod_neg_add (volume : Measure ℝ) volume).quasiMeasurePreserving.ae hP
  have hu : ∀ᵐ z ∂(volume.prod volume : Measure (ℝ × ℝ)),
      z.1 ∈ Ioc 0 T → z.2 ∈ Ioc 0 T → z.1 < z.2 → z.2-z.1 < δ →
        ‖f z.2-f z.1‖ ≤ ε := by
    filter_upwards [hs] with z hz hx hy hxy hd
    dsimp [P] at hz
    have heq : z.1 + (-z.1+z.2) = z.2 := by ring
    rw [heq] at hz
    exact hz (by linarith) (by linarith) (by linarith [hx.1,hy.2])
      ⟨hx.1,by linarith [hy.2]⟩
  have hl := (measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := volume)).quasiMeasurePreserving.ae hu
  filter_upwards [hu,hl] with z hu hl hx hy hd
  rcases lt_trichotomy z.1 z.2 with h | h | h
  · exact hu hx hy h (lt_of_le_of_lt (le_abs_self _) hd)
  · simp only [h, sub_self, norm_zero]; exact hε
  · rw [norm_sub_rev]
    exact hl hy hx h (by rw [abs_sub_comm] at hd; exact lt_of_le_of_lt (le_abs_self _) hd)

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- A common internal essential-supremum translation bound controls averages over any two
positive-length windows whose points have separation less than the translation scale. -/
theorem local_average_consistency {f : ℝ → E} (hf : StronglyMeasurable f)
    {T δ ε : ℝ} (hε : 0 ≤ ε) (hfi : IntegrableOn f (Ioc 0 T))
    (htrans : ∀ h : ℝ, 0 < h → h < δ → h < T →
      eLpNorm (fun t => f (t+h)-f t) ∞ (volume.restrict (Ioc 0 (T-h))) <
        ENNReal.ofReal ε)
    {a b c d : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ T)
    (hclose : ∀ x ∈ Ioc a b, ∀ y ∈ Ioc c d, |y-x| < δ) :
    dist (⨍ x in Ioc a b, f x) (⨍ y in Ioc c d, f y) ≤ ε := by
  have hfa : IntegrableOn f (Ioc a b) := hfi.mono_set (Ioc_subset_Ioc ha hb)
  have hfc : IntegrableOn f (Ioc c d) := hfi.mono_set (Ioc_subset_Ioc hc hd)
  have hpair := ae_ae_of_ae_prod (internal_ae_pair hf hε htrans)
  have hrow : ∀ᵐ x ∂volume.restrict (Ioc a b),
      f x ∈ Metric.closedBall (⨍ y in Ioc c d, f y) ε := by
    filter_upwards [ae_restrict_of_ae hpair, ae_restrict_mem measurableSet_Ioc] with x hx hxa
    have hcol : ∀ᵐ y ∂volume.restrict (Ioc c d), f y ∈ Metric.closedBall (f x) ε := by
      filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem measurableSet_Ioc] with y hy hyc
      exact hy (Ioc_subset_Ioc ha hb hxa) (Ioc_subset_Ioc hc hd hyc) (hclose x hxa y hyc)
    have hmean := (convex_closedBall (f x) ε).set_average_mem isClosed_closedBall
      (by simpa using (ne_of_gt (Real.volume_Ioc_pos.mpr hcd)))
      (by simp) hcol hfc
    simpa only [Metric.mem_closedBall, dist_comm] using hmean
  exact (convex_closedBall (⨍ y in Ioc c d, f y) ε).set_average_mem isClosed_closedBall
    (by simpa using (ne_of_gt (Real.volume_Ioc_pos.mpr hab))) (by simp) hrow hfa

end D5.S3.Topology.Measures.IntervalLInfinityRepresentative
