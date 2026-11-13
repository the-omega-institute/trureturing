/- GID: D5/S3/Quantum/Foundation/OriginalRowSaturation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalRowSaturation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The protected fixed-edge pure row forces both actual ball budgets and whole-cone least confirmation. -/

import D5.S3.Quantum.Foundation.OriginalBallScale
import D5.S3.Quantum.Foundation.OriginalNormalFamily

/-! The fixed-edge row is an explicit unjoined protected-producer dependency.
This module does not assert that an actual collapse supplies it. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalRowSaturation
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalFacePolarity FixedZeroObstruction OriginalRegularHeight
open OriginalNormalFamily OriginalBallScale ExclusionWidthCompactness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The original edge-attainment join, retaining the entire original confirmer family. -/
def PureEdgeRow (p q : pure C u) : Prop :=
  ∀ s : pure C u, ∃ e : V →ₗ[ℝ] ℝ,
    confirms C u p e ∧ e q = 0 ∧ e s = comparison C u p s

/-- From the exact fixed-edge pure row, both actual original exclusions saturate
and the same ep is least on every original mixed state and the entire cone. -/
theorem original_row_saturation
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ s : pure C u, ∃ b : ExclusionChart C u s, b.dim = 3)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (hInj : Function.Injective (fun s : pure C u => exclusion C u s))
    (p : pure C u) (a : ExclusionChart C u p) (ha : a.dim = 3)
    (ep : V →ₗ[ℝ] ℝ) (hp : ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q)
    (hEdge : PureEdgeRow p q) :
    (∀ w : chartSpace a, ‖w‖ = 1 → extensionBudget a w = 1) ∧
    (∀ b : ExclusionChart C u q, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1) ∧
    (∀ x ∈ base C u, comparison C u p x = ep x) ∧
    (∀ f : V →ₗ[ℝ] ℝ, confirms C u p f → ∀ x ∈ C, ep x ≤ f x) := by
  have hB : exclusionBalls C u := by intro s; obtain ⟨b, _⟩ := hEB3 s; exact ⟨b⟩
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
    simp only [map_neg, Submodule.coe_neg, ContinuousLinearMap.neg_apply] at hh
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
  refine ⟨hbudgeta, hbudgetq, ?_, hleast⟩
  intro x hx
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro z ⟨f, hf, rfl⟩; exact (hf.1 x hx.1).1⟩ ⟨ep, hep.1, rfl⟩
  · change ep x ≤ sInf {z : ℝ | ∃ f : V →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = z}
    apply le_csInf (show ({z : ℝ | ∃ f : V →ₗ[ℝ] ℝ,
      confirms C u p f ∧ f x = z} : Set ℝ).Nonempty from ⟨ep x, ep, hep.1, rfl⟩)
    rintro z ⟨f, hf, rfl⟩
    exact hleast f hf x hx.1

#print axioms original_row_saturation

end D5.S3.Quantum.Foundation.OriginalRowSaturation
