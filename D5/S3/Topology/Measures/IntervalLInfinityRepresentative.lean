/- GID: D5/S3/Topology/Measures/IntervalLInfinityRepresentative
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/IntervalLInfinityRepresentative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Internal translations yield unique equicontinuous continuous representatives. -/

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic

/-! # Continuous representatives from internal essential-supremum translations -/

set_option autoImplicit false
open Set MeasureTheory MeasureTheory.Measure Filter Metric
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
  have hshear := (measurePreserving_prod_neg_add (volume : Measure ℝ) volume)
  have hs := hshear.quasiMeasurePreserving.ae hP
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
      simpa only [Metric.mem_closedBall, dist_eq_norm] using
        hy (Ioc_subset_Ioc ha hb hxa) (Ioc_subset_Ioc hc hd hyc) (hclose x hxa y hyc)
    have hmean := (convex_closedBall (f x) ε).set_average_mem isClosed_closedBall
      (by simpa [Real.volume_Ioc] using
        (ENNReal.ofReal_pos.mpr (sub_pos.mpr hcd)).ne')
      (by simp) hcol hfc
    simpa only [Metric.mem_closedBall, dist_comm] using hmean
  exact (convex_closedBall (⨍ y in Ioc c d, f y) ε).set_average_mem isClosed_closedBall
    (by simpa [Real.volume_Ioc] using
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne') (by simp) hrow hfa

private def window (T r x : ℝ) : Set ℝ := Ioc (max 0 (x-r)) (min T (x+r))

private noncomputable def localMean (f : ℝ → E) (T r x : ℝ) : E :=
  ⨍ t in window T r x, f t

private lemma window_pos {T r x : ℝ} (hT : 0 < T) (hr : 0 < r)
    (hx : x ∈ Icc 0 T) : max 0 (x-r) < min T (x+r) := by
  apply lt_min
  · exact max_lt hT (by linarith [hx.2])
  · exact max_lt (by linarith [hx.1]) (by linarith)

private lemma window_subset (T r x : ℝ) : window T r x ⊆ Ioc 0 T :=
  Ioc_subset_Ioc (le_max_left _ _) (min_le_left _ _)

private lemma window_distance {T r x t : ℝ} (ht : t ∈ window T r x) :
    |t-x| ≤ r := by
  have h1 : x-r < t := lt_of_le_of_lt (le_max_right _ _) ht.1
  have h2 : t ≤ x+r := le_trans ht.2 (min_le_right _ _)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private lemma localMean_close {f : ℝ → E} (hf : StronglyMeasurable f)
    {T δ ε : ℝ} (hT : 0 < T) (hε : 0 ≤ ε) (hfi : IntegrableOn f (Ioc 0 T))
    (htrans : ∀ h : ℝ, 0 < h → h < δ → h < T →
      eLpNorm (fun t => f (t+h)-f t) ∞ (volume.restrict (Ioc 0 (T-h))) <
        ENNReal.ofReal ε)
    {r s x y : ℝ} (hr : 0 < r) (hs : 0 < s) (hx : x ∈ Icc 0 T)
    (hy : y ∈ Icc 0 T) (hsmall : |y-x| + r + s < δ) :
    dist (localMean f T r x) (localMean f T s y) ≤ ε := by
  apply local_average_consistency hf hε hfi htrans (le_max_left _ _)
    (window_pos hT hr hx) (min_le_left _ _) (le_max_left _ _)
    (window_pos hT hs hy) (min_le_left _ _)
  intro u hu v hv
  have hu' := window_distance hu
  have hv' := window_distance hv
  have hsum : |v-u| ≤ |v-y| + |y-x| + |u-x| := by
    calc |v-u| = |(v-y)+(y-x)+(x-u)| := by congr 1; ring
         _ ≤ |v-y| + |y-x| + |x-u| := by
           linarith [abs_add_le (v-y) (y-x), abs_add_le ((v-y)+(y-x)) (x-u)]
         _ = _ := by rw [abs_sub_comm x u]
  linarith

private noncomputable def radius (n : ℕ) : ℝ := 1 / ((n : ℝ)+1)

private lemma radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

private lemma radius_tendsto : Tendsto radius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private lemma localMean_point_bound {f : ℝ → E} {T δ ε r x : ℝ}
    (hT : 0 < T) (hr : 0 < r) (hx : x ∈ Icc 0 T)
    (hfi : IntegrableOn f (Ioc 0 T))
    (hrow : ∀ᵐ y ∂volume, y ∈ Ioc 0 T → |y - x| < δ → ‖f y - f x‖ ≤ ε)
    (hsmall : r < δ) : dist (localMean f T r x) (f x) ≤ ε := by
  apply (convex_closedBall (f x) ε).set_average_mem isClosed_closedBall
    (by simpa only [window, Real.volume_Ioc] using
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr (window_pos hT hr hx))).ne') (by simp [window])
    ?_ (hfi.mono_set (window_subset T r x))
  filter_upwards [ae_restrict_of_ae hrow,
    ae_restrict_mem measurableSet_Ioc] with y hy hyw
  simpa only [Metric.mem_closedBall, dist_eq_norm] using
    hy (window_subset T r x hyw) ((window_distance hyw).trans_lt hsmall)

omit [NormedSpace ℝ E] [CompleteSpace E] in
private lemma internal_difference_congr_ae {f g : ℝ → E} {T h : ℝ} (hh : 0 ≤ h)
    (hfg : f =ᵐ[volume.restrict (Ioc 0 T)] g) :
    (fun t => f (t+h)-f t) =ᵐ[volume.restrict (Ioc 0 (T-h))]
      (fun t => g (t+h)-g t) := by
  have he : ∀ᵐ t ∂volume, t ∈ Ioc 0 T → f t = g t :=
    (ae_restrict_iff' measurableSet_Ioc).1 hfg
  have hs := (measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae he
  apply (ae_restrict_iff' measurableSet_Ioc).2
  filter_upwards [he,hs] with t ht hs htI
  rw [ht ⟨htI.1,by linarith [htI.2]⟩,
    hs ⟨by linarith [htI.1],by linarith [htI.2]⟩]

/-- A family of actual L-infinity classes with uniformly vanishing positive internal
translations has unique continuous representatives on the closed interval. The representatives
have a common continuity modulus, and both representation and translation norms respect AE
replacement. No common bound on the family norms is assumed. -/
theorem exists_continuous_representatives {T : ℝ} (hT : 0 < T)
    (S : Set (Lp E ∞ (volume.restrict (Ioc 0 T))))
    (htrans : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ f ∈ S, ∀ h : ℝ, 0 < h → h < δ → h < T →
        eLpNorm (fun t => f (t+h)-f t) ∞ (volume.restrict (Ioc 0 (T-h))) <
          ENNReal.ofReal ε) :
    ∃ R : S → C(Icc (0 : ℝ) T, E),
      (∀ f : S, (fun t => R f (projIcc 0 T hT.le t)) =ᵐ[volume.restrict (Ioc 0 T)]
        (f.1 : ℝ → E)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ f : S,
        ∀ x y : Icc (0 : ℝ) T, dist x y < η → dist (R f x) (R f y) < ε) ∧
      (∀ f : S, ∀ g : C(Icc (0 : ℝ) T, E),
        (fun t => g (projIcc 0 T hT.le t)) =ᵐ[volume.restrict (Ioc 0 T)] (f.1 : ℝ → E) →
          g = R f) ∧
      (∀ f : S, ∀ u : ℝ → E, u =ᵐ[volume.restrict (Ioc 0 T)] (f.1 : ℝ → E) →
        ((fun t => R f (projIcc 0 T hT.le t)) =ᵐ[volume.restrict (Ioc 0 T)] u) ∧
        ∀ h : ℝ, 0 < h → h < T →
          eLpNorm (fun t => u (t+h)-u t) ∞ (volume.restrict (Ioc 0 (T-h))) =
            eLpNorm (fun t => f.1 (t+h)-f.1 t) ∞ (volume.restrict (Ioc 0 (T-h)))) := by
  classical
  let U (f : S) (n : ℕ) (x : Icc (0 : ℝ) T) : E :=
    localMean (f.1 : ℝ → E) T (radius n) x
  have hfi (f : S) : IntegrableOn (f.1 : ℝ → E) (Ioc 0 T) :=
    MemLp.integrable le_top (Lp.memLp f.1)
  have hc (f : S) (x : Icc (0 : ℝ) T) : CauchySeq (fun n => U f n x) := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := htrans (ε/2) (by linarith)
    obtain ⟨N,hN⟩ := eventually_atTop.1
      (radius_tendsto.eventually (gt_mem_nhds (show 0 < δ/3 by linarith)))
    refine ⟨N,fun m hm n hn => ?_⟩
    apply lt_of_le_of_lt (localMean_close (Lp.stronglyMeasurable f.1) hT
      (by linarith : 0 ≤ ε/2) (hfi f) (hd f.1 f.2) (radius_pos m) (radius_pos n)
      x.2 x.2 ?_) (by linarith : ε/2 < ε)
    simp only [sub_self, abs_zero, zero_add]
    linarith [hN m hm,hN n hn]
  choose r hlim using fun f x => cauchySeq_tendsto_of_complete (hc f x)
  have hmod : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ f : S,
      ∀ x y : Icc (0 : ℝ) T, dist x y < η → dist (r f x) (r f y) < ε := by
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := htrans (ε/2) (by linarith)
    refine ⟨δ/3,by linarith,fun f x y hxy => ?_⟩
    have hxy' : |(y : ℝ)-(x : ℝ)| < δ/3 := by
      simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using hxy
    have hb : dist (r f x) (r f y) ≤ ε/2 := by
      apply le_of_tendsto ((hlim f x).dist (hlim f y))
      filter_upwards [radius_tendsto.eventually
        (gt_mem_nhds (show 0 < δ/3 by linarith))] with n hn
      exact localMean_close (Lp.stronglyMeasurable f.1) hT (by linarith) (hfi f)
        (hd f.1 f.2) (radius_pos n) (radius_pos n) x.2 y.2 (by linarith)
    exact hb.trans_lt (by linarith)
  have haek (f : S) (k : ℕ) : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      ∀ ht : t ∈ Icc (0 : ℝ) T, dist (r f ⟨t,ht⟩) (f.1 t) ≤ radius k := by
    obtain ⟨δ,hδ,hd⟩ := htrans (radius k) (radius_pos k)
    have hp := ae_ae_of_ae_prod
      (internal_ae_pair (Lp.stronglyMeasurable f.1) (radius_pos k).le (hd f.1 f.2))
    filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem measurableSet_Ioc]
      with t ht htI htc
    apply le_of_tendsto ((hlim f ⟨t,htc⟩).dist tendsto_const_nhds)
    filter_upwards [radius_tendsto.eventually (gt_mem_nhds hδ)] with n hn
    exact localMean_point_bound hT (radius_pos n) htc (hfi f)
      (ht.mono fun y hy => hy htI) hn
  have hid (f : S) : (fun t => r f (projIcc 0 T hT.le t))
      =ᵐ[volume.restrict (Ioc 0 T)] (f.1 : ℝ → E) := by
    filter_upwards [ae_all_iff.2 (haek f), ae_restrict_mem measurableSet_Ioc] with t ht htI
    have htC : t ∈ Icc (0 : ℝ) T := Ioc_subset_Icc_self htI
    rw [projIcc_of_mem hT.le htC]
    apply dist_eq_zero.mp
    apply le_antisymm ?_ dist_nonneg
    exact le_of_tendsto_of_tendsto tendsto_const_nhds radius_tendsto
      (Eventually.of_forall fun k => ht k htC)
  let R (f : S) : C(Icc (0 : ℝ) T, E) :=
    ⟨r f, (Metric.uniformContinuous_iff.2 (fun ε hε => by
      obtain ⟨η,hη,h⟩ := hmod ε hε
      exact ⟨η,hη,h f⟩)).continuous⟩
  refine ⟨R,hid,hmod,?_,?_⟩
  · intro f g hg
    have heq := hg.trans (hid f).symm
    have heq' : (fun t => g (projIcc 0 T hT.le t))
        =ᵐ[volume.restrict (Icc 0 T)] (fun t => R f (projIcc 0 T hT.le t)) :=
      (ae_restrict_congr_set (Ioc_ae_eq_Icc' (measure_singleton (0 : ℝ)))).1 heq
    have hon := eqOn_Icc_of_ae_eq volume (ne_of_lt hT) heq'
      (g.continuous.comp continuous_projIcc).continuousOn
      ((R f).continuous.comp continuous_projIcc).continuousOn
    ext x
    simpa only [projIcc_val] using hon x.2
  · intro f u hu
    refine ⟨(hid f).trans hu.symm,fun h hh _ => ?_⟩
    exact eLpNorm_congr_ae (internal_difference_congr_ae hh.le hu)

end D5.S3.Topology.Measures.IntervalLInfinityRepresentative
