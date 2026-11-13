/- GID: D5/S3/Quantum/Foundation/OriginalRowSaturation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalRowSaturation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The protected fixed-edge pure row forces both actual ball budgets and whole-cone least confirmation. -/

import D5.S3.Quantum.Foundation.OriginalBallScale
import D5.S3.Quantum.Foundation.OriginalNormalFamily
import D5.S3.Quantum.Foundation.CommonOldExclusionConfirmation
import D5.S3.Quantum.Foundation.OriginalExclusionLimits
import D5.S3.Quantum.Foundation.OriginalComparisonTopology

/-! Actual whole-exclusion collapse supplies the full fixed-edge pure row. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalRowSaturation
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces ContinuousFrameSum
open OriginalFacePolarity FixedZeroObstruction OriginalRegularHeight
open OriginalNormalFamily OriginalBallScale ExclusionWidthCompactness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The original edge-attainment join, retaining the entire original confirmer family. -/
def PureEdgeRow (p q : pure C u) : Prop :=
  ∀ s : pure C u, ∃ e : V →ₗ[ℝ] ℝ,
    confirms C u p e ∧ e q = 0 ∧ e s = comparison C u p s

/-- Actual whole-ball collapse supplies every pure input of the original edge row.
The same minimizing effect carries its actual zero into the singleton limit. -/
theorem actual_collapse_pure_edge_row
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (h3 : ReciprocalExclusionLimits.threeBallExclusions C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (p q : pure C u) (pn : ℕ → pure C u) (hp : Tendsto pn atTop (𝓝 p))
    (hcollapse : Tendsto (fun n => Metric.hausdorffDist
      (exclusion C u (pn n)) {(q : V)}) atTop (𝓝 0)) : PureEdgeRow p q := by
  classical
  have hB : exclusionBalls C u := by
    intro s
    obtain ⟨f, hi, hw⟩ := h3 s
    exact ⟨⟨3, by norm_num, f, hi, hw⟩⟩
  have hpV : Tendsto (fun n => (pn n : V)) atTop (𝓝 (p : V)) :=
    continuous_subtype_val.tendsto p |>.comp hp
  have hqD : (q : V) ∈ exclusion C u p :=
    (exclusion_limit_labels hc hs hg hB pn hpV ({(q : V)} : NonemptyCompacts V)
      hcollapse).2 p.property (mem_singleton (q : V))
  have hcommon := CommonOldExclusionConfirmation.common_old_exclusion_confirmation hc hs hg h3 hPR
  let M := CommonOldExclusionConfirmation.effectNormBound C u
  have hM : 0 ≤ M := hcommon.1.1
  intro s
  by_cases hsp : s = p
  · subst s
    obtain ⟨e, he, heq⟩ := comparison_attained hs hg p q
    have heq0 : e q = 0 := heq.symm.trans ((comparison_zero_iff hs hg p (pure_mem q)).mpr hqD)
    obtain ⟨f, hf, hself⟩ := comparison_attained hs hg p p
    exact ⟨e.toLinearMap, he, heq0, he.2.trans (hself.trans hf.2).symm⟩
  have hstrict : comparison C u p s < 1 := by
    obtain ⟨h, _, _, hf, hsingle, _⟩ :=
      ReciprocalEndpointExposure.reciprocal_endpoint_exposure hc hs hg p (fun t => (hPR p t).le)
    have hle : comparison C u p s ≤ (u-h) s :=
      csInf_le ⟨0, by rintro z ⟨f, hf', rfl⟩; exact (hf'.1 s (pure_mem s).1).1⟩ ⟨_, hf, rfl⟩
    apply hle.trans_lt
    apply lt_of_le_of_ne (by simpa [(pure_mem s).2] using (hf.1 s (pure_mem s).1).2)
    intro heq
    have hsP : (s : V) ∈ ({(p : V)} : Set V) := hsingle ▸ ⟨pure_mem s, heq⟩
    exact hsp (Subtype.ext hsP)
  have hpK : Tendsto (fun n => (⟨(pn n : V), pure_mem (pn n)⟩ : base C u))
      atTop (𝓝 (⟨(p : V), pure_mem p⟩ : base C u)) := tendsto_subtype_rng.mpr hpV
  have ht : Tendsto (fun n => comparison C u (pn n) s) atTop (𝓝 (comparison C u p s)) := by
    have h := ((hcommon.2.1 s).continuous.tendsto (⟨(p : V), pure_mem p⟩ : base C u)).comp hpK
    simpa only [Function.comp_def, hPR s] using h
  choose e he heval using fun n => comparison_attained hs hg (pn n) s
  have hsmall : ∀ᶠ n in atTop, e n s < 1 := by
    simpa only [heval] using ht.eventually (gt_mem_nhds hstrict)
  obtain ⟨f, hf, φ, hφ, hflim⟩ := (effects_compact hs hg).tendsto_subseq (fun n => (he n).1)
  have hev : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
  have hfp : f p = 1 := tendsto_nhds_unique
    ((hev.tendsto (f, (p : V))).comp (hflim.prodMk_nhds (hpV.comp hφ.tendsto_atTop)))
    (by
      change Tendsto (fun n => e (φ n) (pn (φ n))) atTop (𝓝 1)
      have hones (n : ℕ) : e (φ n) (pn (φ n)) = 1 := (he (φ n)).2
      simpa only [hones] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  have hfs : f s = comparison C u p s := tendsto_nhds_unique
    ((show Continuous (fun g : V →L[ℝ] ℝ => g s) by fun_prop).tendsto f |>.comp hflim)
    (by simpa only [Function.comp_def, heval] using ht.comp hφ.tendsto_atTop)
  have hbound : ∀ᶠ n in atTop, e n q ≤ M * Metric.hausdorffDist (exclusion C u (pn n)) {(q : V)} := by
    filter_upwards [hsmall] with n hn
    obtain ⟨z, hz, hez⟩ := CommonOldExclusionConfirmation.minimizer_has_zero hc hs (pn n)
      (pure_mem s) (he n) (heval n) hn
    have hzD : z ∈ exclusion C u (pn n) := ⟨hz, (e n).toLinearMap, he n, hez⟩
    have hd : ‖(q : V)-z‖ ≤ Metric.hausdorffDist (exclusion C u (pn n)) {(q : V)} := by
      have h := Metric.infDist_le_hausdorffDist_of_mem hzD
        (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
          ((exclusion_ball_faces hc hs hg hB).1 (pn n)).1.nonempty (singleton_nonempty (q : V))
          ((exclusion_ball_faces hc hs hg hB).1 (pn n)).2.1.isBounded isCompact_singleton.isBounded)
      simpa [Metric.infDist_singleton, dist_eq_norm, norm_sub_rev] using h
    calc
      e n q = e n ((q : V)-z) := by rw [map_sub, hez, sub_zero]
      _ ≤ ‖e n‖ * ‖(q : V)-z‖ := (le_abs_self _).trans ((e n).le_opNorm _)
      _ ≤ M * ‖(q : V)-z‖ := mul_le_mul_of_nonneg_right (hcommon.1.2.2 (e n) (he n).1) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hd hM
  have hfq : f q = 0 := le_antisymm
    (le_of_tendsto_of_tendsto
      ((show Continuous (fun g : V →L[ℝ] ℝ => g q) by fun_prop).tendsto f |>.comp hflim)
      (by simpa only [Function.comp_def, mul_zero] using (hcollapse.const_mul M).comp hφ.tendsto_atTop)
      (hφ.tendsto_atTop.eventually hbound))
    ((hf q (pure_mem q).1).1)
  exact ⟨f.toLinearMap, ⟨hf, hfp⟩, hfq, hfs⟩

/-- Actual whole-exclusion collapse saturates both original balls, and the same
ep is least on every original mixed state and the entire original cone. -/
theorem original_row_saturation
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ s : pure C u, ∃ b : ExclusionChart C u s, b.dim = 3)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (hInj : Function.Injective (fun s : pure C u => exclusion C u s))
    (p : pure C u) (a : ExclusionChart C u p) (ha : a.dim = 3)
    (ep : V →ₗ[ℝ] ℝ) (hp : ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q)
    (pn : ℕ → pure C u) (hpn : Tendsto pn atTop (𝓝 p))
    (hcollapse : Tendsto (fun n => Metric.hausdorffDist
      (exclusion C u (pn n)) {(q : V)}) atTop (𝓝 0)) :
    (∀ w : chartSpace a, ‖w‖ = 1 → extensionBudget a w = 1) ∧
    (∀ b : ExclusionChart C u q, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1) ∧
    (∀ x ∈ base C u, comparison C u p x = ep x) ∧
    (∀ f : V →ₗ[ℝ] ℝ, confirms C u p f → ∀ x ∈ C, ep x ≤ f x) ∧
    (∀ w : chartSpace a, ‖w‖ = 1 → ∀ s : pure C u, a.param w = s →
      ∀ z : chartSpace a, ‖z‖ ≤ 1 → comparison C u s (a.param z) = (1 + ⟪w,z⟫) / 2) ∧
    (∀ b : ExclusionChart C u q, ∀ w : chartSpace b, ‖w‖ = 1 →
      ∀ s : pure C u, b.param w = s → ∀ z : chartSpace b, ‖z‖ ≤ 1 →
        comparison C u s (b.param z) = (1 + ⟪w,z⟫) / 2) := by
  have hB : exclusionBalls C u := by intro s; obtain ⟨b, _⟩ := hEB3 s; exact ⟨b⟩
  have h3 : ReciprocalExclusionLimits.threeBallExclusions C u := by
    intro s
    obtain ⟨⟨d, hd, f, hi, hw⟩, heq⟩ := hEB3 s
    dsimp at heq
    subst d
    exact ⟨f, hi, hw⟩
  have hEdge := actual_collapse_pure_edge_row hc hs hg h3 hPR p q pn hpn hcollapse
  have hep : ep ∈ fullZeroConfirmers C u p := (hp ep).mpr rfl
  obtain ⟨k⟩ := original_coordinates hc hs hg hEB3 hInj p a ha ep hp
  obtain ⟨eq, hqunique, hL, hLhalf, hform, hanti, horth⟩ :=
    original_neighbor_support hc hs hg hB hInj p hep k q v hv hq
  have heq : eq ∈ fullZeroConfirmers C u q := (hqunique eq).mpr rfl
  obtain ⟨eq', huniq', hedge⟩ := original_fixed_edge hc hs hg hB hInj p hep k q v hv hq
  have heq' : eq' = eq := (hqunique eq').mp ((huniq' eq').mpr rfl)
  subst eq'
  have hqD : (q : V) ∈ exclusion C u p := hq ▸ SingleLabelNormalBody.chart_mem a hv.le
  have hpD := (exclusion_symmetric p q).mp hqD
  have hcq : confirms C u p (u - eq) := by
    refine ⟨?_, ?_⟩
    · intro x hx; have hh := heq.1.1 x hx
      constructor <;> simp only [LinearMap.sub_apply] <;> linarith
    · simp [heq.2 _ hpD, (pure_mem p).2]
  have hrow (s : pure C u) : comparison C u p s = min (ep s) ((u - eq) s) := by
    have hle (f : V →ₗ[ℝ] ℝ) (hf : confirms C u p f) : comparison C u p s ≤ f s :=
      csInf_le ⟨0, by rintro r ⟨g, hg', rfl⟩; exact (hg'.1 s (pure_mem s).1).1⟩ ⟨f, hf, rfl⟩
    apply le_antisymm (le_min (hle ep hep.1) (hle (u - eq) hcq))
    obtain ⟨e, he, heq0, hes⟩ := hEdge s
    obtain ⟨t, ht, htform⟩ := (hedge e).mp ⟨he.1, he.2, heq0⟩
    have hread := congrArg (fun f : V →ₗ[ℝ] ℝ => f s) htform
    change e s = (1-t) * ep s + t * (u s - eq s) at hread
    rw [(pure_mem s).2] at hread
    rw [← hes]
    simp only [LinearMap.sub_apply, (pure_mem s).2]
    rcases le_total (ep s) (1-eq s) with hh | hh
    · rw [min_eq_left hh]
      nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hh)]
    · rw [min_eq_right hh]
      nlinarith [mul_nonneg (show 0 ≤ 1-t by linarith [ht.2]) (sub_nonneg.mpr hh)]
  have hqr := (pure_row_positive_bridge hc hs hg p hep k q v hv hq eq heq
    _ hL hform hrow).2.2.2.2
  obtain ⟨t, ht, hth, hscale, hbudget⟩ := original_scale_and_sharp_budget hc hs hg hB hPR p a
  have hzero := (comparison_zero_iff hs hg q
    (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1).mpr hqr
  obtain ⟨_, _, _, hcomp⟩ := hscale v hv q hq
  rw [hcomp (-v) (by simpa using hv.le)] at hzero
  simp only [inner_neg_right, real_inner_self_eq_norm_sq, hv, one_pow] at hzero
  have htunit : t = 1 / 2 := by linarith
  have hbudgeta : ∀ w : chartSpace a, ‖w‖ = 1 → extensionBudget a w = 1 := by
    intro w hw
    simpa [htunit] using (hbudget w hw).2.2
  have hrpure : a.param (-v) ∈ pure C u :=
    ((chart_boundary hc hs hg hB p a).symm ▸
      (show a.param (-v) ∈ a.param '' Metric.sphere 0 1 from
        ⟨-v, by simpa using hv, rfl⟩)).2
  let r : pure C u := ⟨a.param (-v), hrpure⟩
  have hpr : comparison C u p r = 0 :=
    (comparison_zero_iff hs hg p (pure_mem r)).mpr
      (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le))
  have hbudgetq (b : ExclusionChart C u q) (w : chartSpace b) (hw : ‖w‖ = 1) :
      extensionBudget b w = 1 := by
    have hpsphere : (p : V) ∈ b.param '' Metric.sphere 0 1 := by
      rw [← chart_boundary hc hs hg hB q b]; exact ⟨hpD, p.property⟩
    have hrsphere : (r : V) ∈ b.param '' Metric.sphere 0 1 := by
      rw [← chart_boundary hc hs hg hB q b]; exact ⟨hqr, r.property⟩
    obtain ⟨d, hd, hdp⟩ := hpsphere
    obtain ⟨z, hz, hzr⟩ := hrsphere
    have hd1 : ‖d‖ = 1 := by simpa using hd
    have hz1 : ‖z‖ = 1 := by simpa using hz
    obtain ⟨tb, htb, htbh, hsb, hbb⟩ := original_scale_and_sharp_budget hc hs hg hB hPR q b
    obtain ⟨_, _, _, hcb⟩ := hsb d hd1 p hdp
    have he := hcb z hz1.le
    rw [hzr, hpr] at he
    have hi : -1 ≤ ⟪d, z⟫ := by
      have hh := abs_real_inner_le_norm d z
      rw [hd1, hz1] at hh
      exact (abs_le.mp (by simpa using hh)).1
    have htbu : tb = 1 / 2 := by nlinarith
    simpa [htbu] using (hbb w hw).2.2
  have hrho (w : chartSpace a) (hw : ‖w‖ = 1) : rho k w = 1 := by
    have hwP : a.param w ∈ pure C u :=
      ((chart_boundary hc hs hg hB p a).symm ▸
        (show a.param w ∈ a.param '' Metric.sphere 0 1 from ⟨w, by simpa using hw, rfl⟩)).2
    let s : pure C u := ⟨a.param w, hwP⟩
    obtain ⟨_, _, _, hcs⟩ := hscale w hw s rfl
    have hcs0 : comparison C u s (a.param (-w)) = 0 := by
      rw [hcs (-w) (by simpa using hw.le), htunit]
      norm_num [inner_neg_right, real_inner_self_eq_norm_sq, hw]
    have hDs := (comparison_zero_iff hs hg s
      (SingleLabelNormalBody.chart_mem a (z := -w) (by simpa using hw.le)).1).mp hcs0
    obtain ⟨_, _, _, _, _, _, ho⟩ := original_neighbor_support hc hs hg hB hInj p hep k s w hw rfl
    exact ho.mp hDs
  have heqle (s : pure C u) : eq s ≤ k.g.val s := by
    have hn := ((rho_positive_iff hc hs hg hB hInj p hep k (-v) (by simpa using hv)).2 1).mpr
      (by rw [hrho (-v) (by simpa using hv)])
    have hh := hn s (pure_mem s).1
    change 0 ≤ 1 * k.g.val s + (directionLift k (-v)).val s at hh
    simp only [map_neg, Submodule.coe_neg, neg_apply] at hh
    rw [hform s]
    nlinarith
  have hpure (s : pure C u) : comparison C u p s = ep s := by
    rw [hrow s]
    apply min_eq_left
    have hh := heqle s
    rw [k.g_value] at hh
    change eq s ≤ u s - ep s at hh
    change ep s ≤ u s - eq s
    linarith
  have hleast (f : V →ₗ[ℝ] ℝ) (hf : confirms C u p f) : ∀ x ∈ C, ep x ≤ f x := by
    have hnon : ∀ s : pure C u, 0 ≤ (f-ep) s := by
      intro s
      have hh : comparison C u p s ≤ f s := csInf_le
        ⟨0, by rintro z ⟨g, hg', rfl⟩; exact (hg'.1 s (pure_mem s).1).1⟩ ⟨f, hf, rfl⟩
      rw [hpure s] at hh
      simpa only [LinearMap.sub_apply, sub_nonneg] using hh
    intro x hx
    exact sub_nonneg.mp (nonneg_on_cone (base_compact hc hs) hs hnon x hx)
  refine ⟨hbudgeta, hbudgetq, ?_, hleast, ?_, ?_⟩
  · intro x hx
    apply le_antisymm
    · exact csInf_le ⟨0, by rintro z ⟨f, hf, rfl⟩; exact (hf.1 x hx.1).1⟩ ⟨ep, hep.1, rfl⟩
    · change ep x ≤ sInf {z : ℝ | ∃ f : V →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = z}
      apply le_csInf (show ({z : ℝ | ∃ f : V →ₗ[ℝ] ℝ,
        confirms C u p f ∧ f x = z} : Set ℝ).Nonempty from ⟨ep x, ep, hep.1, rfl⟩)
      rintro z ⟨f, hf, rfl⟩
      exact hleast f hf x hx.1
  · intro w hw s hsw z hz
    obtain ⟨_, _, _, hcs⟩ := hscale w hw s hsw
    rw [hcs z hz, htunit]
    ring
  · intro b w hw s hsw z hz
    obtain ⟨tb, htb, _, hsb, hbb⟩ := original_scale_and_sharp_budget hc hs hg hB hPR q b
    have he : 1 / (2*tb) = 1 := ((hbb w hw).2.2).symm.trans (hbudgetq b w hw)
    have htbu : tb = 1 / 2 := by
      have hh := (div_eq_iff (by positivity : 2*tb ≠ 0)).mp he
      linarith
    obtain ⟨_, _, _, hcs⟩ := hsb w hw s hsw
    rw [hcs z hz, htbu]
    ring

/-- A nonunit original budget at a uniquely fully confirmed label excludes
all actual discontinuities in the whole original pure domain. -/
theorem original_nonunit_continuity
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ s : pure C u, ∃ b : ExclusionChart C u s, b.dim = 3)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (hInj : Function.Injective (fun s : pure C u => exclusion C u s))
    (p : pure C u) (a : ExclusionChart C u p) (ha : a.dim = 3)
    (ep : V →ₗ[ℝ] ℝ) (hp : ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep)
    (v : chartSpace a) (hv : ‖v‖ = 1) (hbudget : 1 < extensionBudget a v) :
    ContinuousAt (OriginalExclusionLimits.wholeExclusion hc hs hg
      (fun s => ⟨(hEB3 s).choose⟩)) p ∧
      ∃ U : Set (pure C u), IsOpen U ∧ p ∈ U ∧ ∃ B : ℝ, 0 < B ∧
        ∀ s ∈ U, ∀ b : ExclusionChart C u s,
          ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w ≤ B := by
  have h3 : ReciprocalExclusionLimits.threeBallExclusions C u := by
    intro s
    obtain ⟨⟨d, hd, f, hi, hw⟩, heq⟩ := hEB3 s
    dsimp at heq
    subst d
    exact ⟨f, hi, hw⟩
  have hcont : ContinuousAt (OriginalExclusionLimits.wholeExclusion hc hs hg
      (fun s => ⟨(hEB3 s).choose⟩)) p := by
    by_contra hdisc
    obtain ⟨pn, hpn, q, hq, hcollapse⟩ :=
      OriginalExclusionLimits.original_discontinuity_collapse hc hs hg h3 hPR p hdisc
    have hB : exclusionBalls C u := fun s => ⟨(hEB3 s).choose⟩
    have hqS : (q : V) ∈ a.param '' Metric.sphere 0 1 := by
      rw [← chart_boundary hc hs hg hB p a]
      exact ⟨hq, q.property⟩
    obtain ⟨w, hw, hwq⟩ := hqS
    have hw1 : ‖w‖ = 1 := by simpa using hw
    have hsat := original_row_saturation hc hs hg hEB3 hPR hInj p a ha ep hp q w hw1 hwq pn hpn hcollapse
    exact (ne_of_gt hbudget) (hsat.1 v hv)
  have hreg := (OriginalExclusionLimits.original_regular_iff_continuous
    hc hs hg h3 hPR p).mpr hcont
  obtain ⟨_, _, _, _, hlocal, _, _⟩ :=
    OriginalComparisonTopology.original_common_continuity_sets hc hs hg h3 hPR p
  obtain ⟨U, hU, hpU, B, hBp, hbound⟩ := hlocal.mp hreg
  refine ⟨hcont, U, hU, hpU, B, hBp, ?_⟩
  intro s hsU b w hw
  obtain ⟨_, _, _, _, _, _, _, _, hlaw⟩ :=
    OriginalComparisonTopology.original_common_continuity_sets hc hs hg h3 hPR s
  exact (hlaw b w hw).2.2.le.trans (hbound s hsU)

/-- The original P0 condition concerns A(p), while all of F(p) remains available. -/
def uniqueFullZero (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Set (pure C u) :=
  {p | ∃ ep : V →ₗ[ℝ] ℝ, ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep}

/-- Both residual discontinuity branches retain the entire original pure domain.
In the unique-full-zero branch the same ep is least on all C, and every actual
collapse endpoint has unit budget in every whole chart. -/
theorem original_discontinuity_branches
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ s : pure C u, ∃ b : ExclusionChart C u s, b.dim = 3)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (hInj : Function.Injective (fun s : pure C u => exclusion C u s))
    (p : pure C u) (hSigma : p ∉ OriginalExclusionLimits.regularRegion C u) :
    p ∉ uniqueFullZero C u ∨
      ∃ ep : V →ₗ[ℝ] ℝ, (∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep) ∧
        (∀ b : ExclusionChart C u p, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1) ∧
        (∀ x ∈ base C u, comparison C u p x = ep x) ∧
        (∀ f : V →ₗ[ℝ] ℝ, confirms C u p f → ∀ x ∈ C, ep x ≤ f x) ∧
        (∀ (q : pure C u) (pn : ℕ → pure C u), Tendsto pn atTop (𝓝 p) →
          Tendsto (fun n => Metric.hausdorffDist (exclusion C u (pn n)) {(q : V)}) atTop (𝓝 0) →
          ∀ b : ExclusionChart C u q, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1) := by
  classical
  by_cases hp0 : p ∈ uniqueFullZero C u
  · right
    obtain ⟨ep, hep⟩ := hp0
    obtain ⟨a, ha⟩ := hEB3 p
    have hB : exclusionBalls C u := fun s => ⟨(hEB3 s).choose⟩
    have h3 : ReciprocalExclusionLimits.threeBallExclusions C u := by
      intro s
      obtain ⟨⟨d, hd, f, hi, hw⟩, heq⟩ := hEB3 s
      dsimp at heq
      subst d
      exact ⟨f, hi, hw⟩
    have hdisc : ¬ ContinuousAt (OriginalExclusionLimits.wholeExclusion hc hs hg hB) p :=
      fun h => hSigma ((OriginalExclusionLimits.original_regular_iff_continuous hc hs hg h3 hPR p).mpr h)
    obtain ⟨pn, hpn, q, hq, hcollapse⟩ :=
      OriginalExclusionLimits.original_discontinuity_collapse hc hs hg h3 hPR p hdisc
    have apply_collapse (q : pure C u) (pn : ℕ → pure C u) (hpn : Tendsto pn atTop (𝓝 p))
        (ht : Tendsto (fun n => Metric.hausdorffDist (exclusion C u (pn n)) {(q : V)}) atTop (𝓝 0)) :
        (∀ w : chartSpace a, ‖w‖ = 1 → extensionBudget a w = 1) ∧
        (∀ b : ExclusionChart C u q, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1) ∧
        (∀ x ∈ base C u, comparison C u p x = ep x) ∧
        (∀ f : V →ₗ[ℝ] ℝ, confirms C u p f → ∀ x ∈ C, ep x ≤ f x) := by
      have hqD : (q : V) ∈ exclusion C u p :=
        (exclusion_limit_labels hc hs hg hB pn (continuous_subtype_val.tendsto p |>.comp hpn)
          ({(q : V)} : NonemptyCompacts V) ht).2 p.property (mem_singleton _)
      have hqS : (q : V) ∈ a.param '' Metric.sphere 0 1 := by
        rw [← chart_boundary hc hs hg hB p a]
        exact ⟨hqD, q.property⟩
      obtain ⟨v, hv, hvq⟩ := hqS
      have hv1 : ‖v‖ = 1 := by simpa using hv
      have hsat := original_row_saturation hc hs hg hEB3 hPR hInj p a ha ep hep q v hv1 hvq pn hpn ht
      exact ⟨hsat.1, hsat.2.1, hsat.2.2.1, hsat.2.2.2.1⟩
    have hsat := apply_collapse q pn hpn hcollapse
    refine ⟨ep, hep, ?_, hsat.2.2.1, hsat.2.2.2, ?_⟩
    · intro b w hw
      obtain ⟨t, _, _, hba, hbb⟩ := original_chart_independence hc hs hg hB hPR p a b
      letI : Nonempty (Fin a.dim) := ⟨⟨0, a.dim_pos⟩⟩
      obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin a.dim)) (by norm_num : (0 : ℝ) ≤ 1)
      exact (hbb w hw).trans ((hba v hv).symm.trans (hsat.1 v hv))
    · intro q pn hpn ht
      exact (apply_collapse q pn hpn ht).2.1
  · exact Or.inl hp0

#print axioms original_discontinuity_branches

#print axioms actual_collapse_pure_edge_row
#print axioms original_nonunit_continuity

#print axioms original_row_saturation

end D5.S3.Quantum.Foundation.OriginalRowSaturation
