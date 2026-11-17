/- GID: D5/S3/Quantum/Foundation/OriginalRowSaturation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalRowSaturation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The protected fixed-edge pure row forces both actual ball budgets and whole-cone least confirmation. -/

import D5.S3.Quantum.Foundation.OriginalNormalFamily
import D5.S3.Quantum.Foundation.CommonOldExclusionConfirmation

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalComparisonTopology
open CircuitBalancedConfirmation ContinuousFrameSum ExclusionWidthCompactness
open FacetZeroGluing ExclusionBallFaces OriginalFacePolarity OriginalBallScale
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

private theorem chart_diameter_axis {p : pure C u} (a : ExclusionChart C u p) :
    ∃ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 ∧ Metric.diam (exclusion C u p) ≤ ‖a.param v - a.param (-v)‖ := by
  let E := EuclideanSpace ℝ (Fin a.dim)
  let L : E →L[ℝ] V := a.param.linear.toContinuousLinearMap
  letI : Nonempty (Fin a.dim) := ⟨⟨0, a.dim_pos⟩⟩
  have hne : (Metric.sphere (0 : E) 1).Nonempty := (NormedSpace.sphere_nonempty (E := E)).mpr (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne L.continuous.norm.continuousOn
  have hv1 : ‖v‖ = 1 := by simpa using hv
  have hbound (z : E) (hz : ‖z‖ ≤ 1) : ‖L z‖ ≤ ‖L v‖ := by
    by_cases hz0 : z = 0
    · simp [hz0]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let w : E := ‖z‖⁻¹ • z
    have hw : ‖w‖ = 1 := by
      simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z)]
      exact inv_mul_cancel₀ hn.ne'
    have heq : z = ‖z‖ • w := by simp [w, smul_smul, hn.ne']
    have hm : ‖L w‖ ≤ ‖L v‖ := hmax (by simpa using hw)
    have hmul : ‖L z‖ = ‖z‖ * ‖L w‖ := by
      calc
        ‖L z‖ = ‖L (‖z‖ • w)‖ := congrArg (fun x => ‖L x‖) heq
        _ = _ := by simp [norm_smul]
    rw [hmul]
    exact (mul_le_mul_of_nonneg_left hm hn.le).trans (mul_le_of_le_one_left (norm_nonneg _) hz)
  have hrepr (z : E) : a.param z = a.param 0 + L z := by
    simpa [L, add_comm] using congrFun a.param.decomp z
  have haxis : ‖a.param v - a.param (-v)‖ = 2 * ‖L v‖ := by
    rw [hrepr v, hrepr (-v), map_neg]
    have he : a.param 0 + L v - (a.param 0 + -L v) = (2 : ℝ) • L v := by module
    rw [he, norm_smul]
    norm_num
  refine ⟨v, hv1, ?_⟩
  rw [haxis]
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  obtain ⟨z, hz, rfl⟩ := a.whole.symm ▸ hx
  obtain ⟨w, hw, rfl⟩ := a.whole.symm ▸ hy
  have hz1 : ‖z‖ ≤ 1 := by simpa using hz
  have hw1 : ‖w‖ ≤ 1 := by simpa using hw
  have he : a.param z - a.param w = L z - L w := by rw [hrepr z, hrepr w]; abel
  rw [dist_eq_norm, he]
  exact (norm_sub_le _ _).trans (by linarith [hbound z hz1, hbound w hw1])

/-- Pure reciprocity combines the uniform original row bound on the full product of pure labels. -/
theorem pure_comparison_continuous
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) :
    Continuous (fun z : pure C u × pure C u => comparison C u z.1 z.2) := by
  let P := pure C u
  obtain ⟨L, hL, hbound⟩ := original_uniform_comparison hs hg
  have hlip : LipschitzWith ⟨2*L, by positivity⟩ (fun z : P × P => comparison C u z.1 z.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have h1 := hbound z.2 z.1 (pure_mem z.1) w.1 (pure_mem w.1)
    rw [← hPR z.1 z.2, ← hPR w.1 z.2] at h1
    have h2 := hbound w.1 z.2 (pure_mem z.2) w.2 (pure_mem w.2)
    have hf : ‖(z.1 : V)-w.1‖ ≤ dist z w := by
      calc
        _ = dist z.1 w.1 := by rw [Subtype.dist_eq, dist_eq_norm]
        _ ≤ max (dist z.1 w.1) (dist z.2 w.2) := le_max_left _ _
        _ = dist z w := Prod.dist_eq.symm
    have hsnd : ‖(z.2 : V)-w.2‖ ≤ dist z w := by
      calc
        _ = dist z.2 w.2 := by rw [Subtype.dist_eq, dist_eq_norm]
        _ ≤ max (dist z.1 w.1) (dist z.2 w.2) := le_max_right _ _
        _ = dist z w := Prod.dist_eq.symm
    change |comparison C u z.1 z.2 - comparison C u w.1 w.2| ≤ (2*L)*dist z w
    exact (abs_sub_le _ _ _).trans (by nlinarith)
  exact hlip.continuous

set_option maxHeartbeats 800000 in
-- Compact minimization elaborates the full dependent pure-pair comparison domain.
private theorem uniform_pure_gap
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ p q : pure C u, δ ≤ ‖(p : V)-q‖ → γ ≤ 1-comparison C u p q := by
  classical
  let P := pure C u
  letI : CompactSpace P := isCompact_iff_compactSpace.mp (ReciprocalPureCompactness.reciprocal_pure_compact hc hs hg hPR)
  obtain ⟨L, hL, hbound⟩ := original_uniform_comparison hs hg
  have hlip := pure_comparison_continuous hs hg hPR
  let S : Set (P × P) := {z | δ ≤ ‖(z.1 : V)-z.2‖}
  have hSc : IsCompact S := isCompact_univ.of_isClosed_subset (isClosed_le continuous_const (by fun_prop)) (subset_univ _)
  by_cases hne : S.Nonempty
  · have hfun : Continuous (fun z : P × P => 1 - comparison C u z.1 z.2) := continuous_const.sub hlip
    obtain ⟨z, hz, hmin⟩ := hSc.exists_isMinOn hne hfun.continuousOn
    have hnepq : z.1 ≠ z.2 := by
      intro heq
      change δ ≤ ‖(z.1 : V) - z.2‖ at hz
      have hh : δ ≤ 0 := by simpa [heq] using hz
      exact hδ.not_ge hh
    have hstrict : comparison C u z.1 z.2 < 1 := by
      obtain ⟨h, _, _, hf, hsingle, _⟩ :=
        ReciprocalEndpointExposure.reciprocal_endpoint_exposure hc hs hg z.1 (fun t => (hPR z.1 t).le)
      have hle : comparison C u z.1 z.2 ≤ (u-h) z.2 := csInf_le
        ⟨0, by rintro r ⟨f, hf', rfl⟩; exact (hf'.1 z.2 (pure_mem z.2).1).1⟩ ⟨_, hf, rfl⟩
      apply hle.trans_lt
      apply lt_of_le_of_ne (by simpa [(pure_mem z.2).2] using (hf.1 z.2 (pure_mem z.2).1).2)
      intro heq
      have hh : (z.2 : V) ∈ ({(z.1 : V)} : Set V) := hsingle ▸ ⟨pure_mem z.2, heq⟩
      exact hnepq (Subtype.ext hh).symm
    refine ⟨1-comparison C u z.1 z.2, by linarith, ?_⟩
    intro p q hpq
    exact hmin (show (p,q) ∈ S from hpq)
  · exact ⟨1, zero_lt_one, fun p q hpq => False.elim (hne ⟨(p,q),hpq⟩)⟩

/-- A positive lower bound on actual full diameters bounds every original
optimal budget, in every chart and direction, on any whole-P label set. -/
theorem original_noncollapse_bounded_budget
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) (U : Set (pure C u)) (δ : ℝ) (hδ : 0 < δ)
    (hdiam : ∀ p ∈ U, δ ≤ Metric.diam (exclusion C u p)) :
    ∃ B : ℝ, 0 < B ∧ ∀ p ∈ U, ∀ a : ExclusionChart C u p,
      ∀ w : EuclideanSpace ℝ (Fin a.dim), ‖w‖ = 1 → extensionBudget a w ≤ B := by
  obtain ⟨γ, hγ, hgap⟩ := uniform_pure_gap hc hs hg hPR δ hδ
  refine ⟨1/γ, by positivity, ?_⟩
  intro p hp a w hw
  obtain ⟨v, hv, hd⟩ := chart_diameter_axis a
  have hqpure : a.param v ∈ pure C u := ((chart_boundary hc hs hg hB p a).symm ▸
      (show a.param v ∈ a.param '' Metric.sphere 0 1 from ⟨v, by simpa using hv, rfl⟩)).2
  have hrpure : a.param (-v) ∈ pure C u := ((chart_boundary hc hs hg hB p a).symm ▸
      (show a.param (-v) ∈ a.param '' Metric.sphere 0 1 from ⟨-v, by simpa using hv, rfl⟩)).2
  let q : pure C u := ⟨a.param v, hqpure⟩
  let r : pure C u := ⟨a.param (-v), hrpure⟩
  obtain ⟨t, ht, _, hscale⟩ := original_common_chart_scale hc hs hg hB hPR p a
  obtain ⟨_, _, _, hcomp⟩ := (hscale a v hv).2 q rfl
  have hgap' := hgap q r ((hdiam p hp).trans hd)
  have hcomp' := hcomp (-v) (by simpa using hv.le)
  have hγt : γ ≤ 2*t := by
    simp only [inner_neg_right, real_inner_self_eq_norm_sq, hv, one_pow] at hcomp'
    change γ ≤ 1 - comparison C u q (a.param (-v)) at hgap'
    rw [hcomp'] at hgap'
    linarith
  rw [(hscale a w hw).1.2.2]
  exact one_div_le_one_div_of_le hγ hγt

end D5.S3.Quantum.Foundation.OriginalComparisonTopology

noncomputable section
open Set Filter Topology TopologicalSpace

namespace D5.S3.Quantum.Foundation.OriginalExclusionLimits
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces OriginalFacePolarity
open ExclusionIncidence ReciprocalExclusionLimits

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The original EB3 data supplies the full positive-dimensional ball condition. -/
theorem ballHyp (h3 : threeBallExclusions C u) : exclusionBalls C u := fun s =>
  ⟨⟨3, by norm_num, (h3 s).choose, (h3 s).choose_spec.1, (h3 s).choose_spec.2⟩⟩

/-- The actual whole exclusion as a nonempty compact set. -/
def wholeExclusion
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) : NonemptyCompacts V :=
  ⟨⟨exclusion C u p, ((exclusion_ball_faces hc hs hg hB).1 p).2.1⟩, ((exclusion_ball_faces hc hs hg hB).1 p).1.nonempty⟩

/-- Every actual Hausdorff discontinuity has a whole-ball singleton-collapse
witness with original pure labels and a pure point in the old whole exclusion. -/
theorem original_discontinuity_collapse
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (h3 : threeBallExclusions C u) (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) (p : pure C u)
    (hdisc : ¬ ContinuousAt (wholeExclusion hc hs hg (ballHyp h3)) p) :
    ∃ pn : ℕ → pure C u, Tendsto pn atTop (𝓝 p) ∧ ∃ q : pure C u, (q : V) ∈ exclusion C u p ∧
        Tendsto (fun n => Metric.hausdorffDist (exclusion C u (pn n)) {(q : V)}) atTop (𝓝 0) := by
  classical
  let hB := ballHyp h3
  let D := wholeExclusion hc hs hg hB
  by_contra hno
  apply hdisc
  change Tendsto D (𝓝 p) (𝓝 (D p))
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro pn hp
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨Q, _, ms, hms, hlim⟩ := (NonemptyCompacts.isCompact_subsets_of_isCompact (base_compact hc hs)).tendsto_subseq
      (fun n => (show (D (pn (ns n)) : Set V) ⊆ base C u from fun x hx => hx.1))
  have hpn : Tendsto (fun n => pn (ns (ms n))) atTop (𝓝 p) := (hp.comp hns).comp hms.tendsto_atTop
  rcases exclusion_limit_dichotomy hc hs hg h3 hPR hpn (fun n => D (pn (ns (ms n)))) Q (fun _ => rfl) hlim with heq | ⟨q, hq, heq⟩
  · refine ⟨ms, ?_⟩
    have hQD : Q = D p := NonemptyCompacts.ext heq
    simpa only [hQD, Function.comp_def] using hlim
  · exfalso
    apply hno
    refine ⟨fun n => pn (ns (ms n)), hpn, q, hq, ?_⟩
    have ht := tendsto_iff_dist_tendsto_zero.mp hlim
    simpa only [NonemptyCompacts.dist_eq, heq, Function.comp_def, D, wholeExclusion,
      NonemptyCompacts.coe_mk, Compacts.coe_mk] using ht

private theorem compact_diameter_control (S T : NonemptyCompacts V) :
    Metric.diam (S : Set V) ≤ Metric.diam (T : Set V) + 2 * dist S T := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  obtain ⟨x', hx', hxx'⟩ := T.isCompact.exists_infDist_eq_dist T.nonempty x
  obtain ⟨y', hy', hyy'⟩ := T.isCompact.exists_infDist_eq_dist T.nonempty y
  have hdx : dist x x' ≤ dist S T := by
    rw [← hxx']
    exact Metric.infDist_le_hausdorffDist_of_mem hx (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      S.nonempty T.nonempty S.isCompact.isBounded T.isCompact.isBounded)
  have hdy : dist y y' ≤ dist S T := by
    rw [← hyy']
    exact Metric.infDist_le_hausdorffDist_of_mem hy (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      S.nonempty T.nonempty S.isCompact.isBounded T.isCompact.isBounded)
  have hxy := Metric.dist_le_diam_of_mem T.isCompact.isBounded hx' hy'
  have ht := dist_triangle4 x x' y' y
  rw [dist_comm y' y] at ht
  linarith

theorem compact_diameter_lipschitz :
    LipschitzWith 2 (fun S : NonemptyCompacts V => Metric.diam (S : Set V)) := by
  apply LipschitzWith.of_dist_le_mul
  intro S T
  rw [Real.dist_eq]
  change |Metric.diam (S : Set V) - Metric.diam (T : Set V)| ≤ 2 * dist S T
  apply abs_le.mpr
  constructor
  · have h := compact_diameter_control T S
    rw [dist_comm T S] at h
    linarith
  · have h := compact_diameter_control S T
    linarith

/-- The IX115 regular region; the indexing j+1 ranges over every positive integer. -/
def regularRegion (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Set (pure C u) :=
  ⋃ j : ℕ, interior {p : pure C u | 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u p)}

/-- The regular region is exactly the whole Hausdorff continuity set. -/
theorem original_regular_iff_continuous
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : threeBallExclusions C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) (p : pure C u) :
    p ∈ regularRegion C u ↔ ContinuousAt (wholeExclusion hc hs hg (ballHyp h3)) p := by
  let D := wholeExclusion hc hs hg (ballHyp h3)
  constructor
  · intro hpreg
    obtain ⟨j, hj⟩ := mem_iUnion.mp hpreg
    by_contra hdisc
    obtain ⟨pn, hpn, q, _, hcollapse⟩ := original_discontinuity_collapse hc hs hg h3 hPR p hdisc
    have ht : Tendsto (fun n => D (pn n)) atTop (𝓝 ({(q : V)} : NonemptyCompacts V)) :=
      tendsto_iff_dist_tendsto_zero.mpr hcollapse
    have hd := (compact_diameter_lipschitz.continuous.tendsto ({(q : V)} : NonemptyCompacts V)).comp ht
    have hsmall : ∀ᶠ n in atTop, 1 / (j + 1 : ℝ) ≤ Metric.diam (D (pn n) : Set V) :=
      (hpn.eventually (isOpen_interior.mem_nhds hj)).mono fun n h =>
        (show 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u (pn n)) from (interior_subset : interior {r : pure C u |
            1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u r)} ⊆
            {r : pure C u | 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u r)}) h)
    have hbad : 1 / (j + 1 : ℝ) ≤ 0 := by
      simpa using ge_of_tendsto hd hsmall
    exact (one_div_pos.mpr (by positivity : 0 < (j + 1 : ℝ))).not_ge hbad
  · intro hcont
    have hgeom := (exclusion_ball_faces hc hs hg (ballHyp h3)).1 p
    have hdpos : 0 < Metric.diam (D p : Set V) := Metric.diam_pos hgeom.1 hgeom.2.1.isBounded
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hdpos
    have hdi := compact_diameter_lipschitz.continuous.continuousAt.comp hcont
    have hn : {s : pure C u | 1 / (j + 1 : ℝ) < Metric.diam (D s : Set V)} ∈ 𝓝 p := hdi.preimage_mem_nhds (Ioi_mem_nhds hj)
    exact mem_iUnion.mpr ⟨j, mem_interior_iff_mem_nhds.mpr (mem_of_superset hn fun x h =>
        (show 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u x) from (show 1 / (j + 1 : ℝ) < Metric.diam (D x : Set V) from h).le))⟩

#print axioms original_discontinuity_collapse

end D5.S3.Quantum.Foundation.OriginalExclusionLimits

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalComparisonTopology
open CircuitBalancedConfirmation ContinuousFrameSum ExclusionWidthCompactness
open FacetZeroGluing ExclusionBallFaces OriginalFacePolarity OriginalBallScale

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- Whole Hausdorff continuity is equivalent to a finite local bound for all
actual optimal budgets, using an open neighborhood in all original P. -/
theorem original_local_budget_iff
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (h3 : ReciprocalExclusionLimits.threeBallExclusions C u) (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    (p : pure C u) :
    ContinuousAt (OriginalExclusionLimits.wholeExclusion hc hs hg (OriginalExclusionLimits.ballHyp h3)) p ↔
      ∃ U : Set (pure C u), IsOpen U ∧ p ∈ U ∧ ∃ B : ℝ, 0 < B ∧ ∀ s ∈ U, ∀ a : ExclusionChart C u s,
          ∀ w : EuclideanSpace ℝ (Fin a.dim), ‖w‖ = 1 → extensionBudget a w ≤ B := by
  let hB := OriginalExclusionLimits.ballHyp h3
  constructor
  · intro hcont
    have hreg := (OriginalExclusionLimits.original_regular_iff_continuous hc hs hg h3 hPR p).mpr hcont
    obtain ⟨j, hj⟩ := mem_iUnion.mp hreg
    let U : Set (pure C u) := interior {s : pure C u | 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u s)}
    have hdiam : ∀ s ∈ U, 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u s) := by
      intro s hs
      exact (interior_subset : interior {r : pure C u | 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u r)} ⊆
        {r : pure C u | 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u r)}) hs
    obtain ⟨B, hBp, hbudget⟩ := original_noncollapse_bounded_budget hc hs hg hB hPR U (1 / (j + 1 : ℝ)) (by positivity) hdiam
    exact ⟨U, isOpen_interior, hj, B, hBp, hbudget⟩
  · rintro ⟨U, hU, hp, B, hBp, hbudget⟩
    obtain ⟨δ, hδ, hdiam⟩ := original_bounded_budget_noncollapse hc hs hg hB hPR U B hBp hbudget
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    apply (OriginalExclusionLimits.original_regular_iff_continuous hc hs hg h3 hPR p).mp
    apply mem_iUnion.mpr
    refine ⟨j, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact mem_of_superset (hU.mem_nhds hp) (fun s hs => hj.le.trans (hdiam s hs))

#print axioms original_local_budget_iff

#print axioms original_noncollapse_bounded_budget


section IntrinsicScalars

variable (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
  (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)

/-- The common actual comparison coefficient, selected from the all-chart law. -/
def calibration (p : pure C u) : ℝ :=
  (original_common_chart_scale hc hs hg hB hPR p (Classical.choice (hB p))).choose

/-- The reciprocal is identified with the original attained infimum in every chart. -/
def optimalBudget (p : pure C u) : ℝ := 1 / (2 * calibration hc hs hg hB hPR p)

private theorem calibration_spec (p : pure C u) :
    0 < calibration hc hs hg hB hPR p ∧ calibration hc hs hg hB hPR p ≤ 1/2 ∧
    ∀ b : ExclusionChart C u p, ∀ v : EuclideanSpace ℝ (Fin b.dim), ‖v‖ = 1 →
      (BudgetFeasible b v (optimalBudget hc hs hg hB hPR p) ∧ (∀ M, BudgetFeasible b v M → optimalBudget hc hs hg hB hPR p ≤ M) ∧
        extensionBudget b v = optimalBudget hc hs hg hB hPR p) ∧
      ∀ q : pure C u, b.param v = q → ∃ e : V →ₗ[ℝ] ℝ, confirms C u q e ∧ (∀ z, e (b.param z) = 1-calibration hc hs hg hB hPR p +
          calibration hc hs hg hB hPR p*⟪v,z⟫) ∧
        ∀ z, ‖z‖ ≤ 1 → comparison C u q (b.param z) = 1-calibration hc hs hg hB hPR p + calibration hc hs hg hB hPR p*⟪v,z⟫ :=
  (original_common_chart_scale hc hs hg hB hPR p (Classical.choice (hB p))).choose_spec

end IntrinsicScalars

section ScalarTopology

variable (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : ReciprocalExclusionLimits.threeBallExclusions C u)
  (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)

local notation "hB₀" => OriginalExclusionLimits.ballHyp h3
local notation "a₀" => calibration hc hs hg hB₀ hPR
local notation "β₀" => optimalBudget hc hs hg hB₀ hPR
local notation "D₀" => OriginalExclusionLimits.wholeExclusion hc hs hg hB₀

/-- The entire regular region is exactly all three actual continuity sets. -/
theorem original_common_continuity_sets (p : pure C u) :
    (p ∈ OriginalExclusionLimits.regularRegion C u ↔ ContinuousAt a₀ p) ∧
    (p ∈ OriginalExclusionLimits.regularRegion C u ↔ ContinuousAt β₀ p) ∧
    UpperSemicontinuous a₀ ∧ LowerSemicontinuous β₀ ∧
    (p ∈ OriginalExclusionLimits.regularRegion C u ↔ ∃ U : Set (pure C u), IsOpen U ∧ p ∈ U ∧ ∃ B : ℝ, 0 < B ∧
        ∀ s ∈ U, β₀ s ≤ B) ∧
    (∀ S : Set (pure C u), IsCompact S → S ⊆ OriginalExclusionLimits.regularRegion C u → ∃ B : ℝ, ∀ s ∈ S, β₀ s ≤ B) ∧
    (0 < a₀ p ∧ a₀ p ≤ 1/2 ∧ ∀ b : ExclusionChart C u p, ∀ v : EuclideanSpace ℝ (Fin b.dim), ‖v‖ = 1 → BudgetFeasible b v (β₀ p) ∧
          (∀ M, BudgetFeasible b v M → β₀ p ≤ M) ∧ extensionBudget b v = β₀ p) := by
  have original_diameter_collapse_budget (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
      (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
      (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) (pn : ℕ → pure C u) (a : ∀ n, ExclusionChart C u (pn n))
      (v : ∀ n, EuclideanSpace ℝ (Fin (a n).dim)) (hv : ∀ n, ‖v n‖ = 1)
      (hd : Tendsto (fun n => Metric.diam (exclusion C u (pn n))) atTop (𝓝 0)) :
      Tendsto (fun n => extensionBudget (a n) (v n)) atTop atTop := by
    obtain ⟨L, hL, haxis⟩ := original_scale_axis_bound hc hs hg hB hPR
    have hprod (n : ℕ) : 1 ≤ extensionBudget (a n) (v n) * (L * Metric.diam (exclusion C u (pn n))) := by
      obtain ⟨t, ht, _, hbudget, hax⟩ := haxis (pn n) (a n)
      rw [hbudget (v n) (hv n)]
      have hdiam : ‖(a n).param (v n) - (a n).param (-v n)‖ ≤ Metric.diam (exclusion C u (pn n)) := by
        rw [← dist_eq_norm]
        exact Metric.dist_le_diam_of_mem ((exclusion_ball_faces hc hs hg hB).1 (pn n)).2.1.isBounded
          (SingleLabelNormalBody.chart_mem (a n) (hv n).le)
          (SingleLabelNormalBody.chart_mem (a n) (z := -v n) (by simpa using (hv n).le))
      have hh := (hax (v n) (hv n)).trans (mul_le_mul_of_nonneg_left hdiam hL.le)
      have hh' : (1 : ℝ) ≤ (L * Metric.diam (exclusion C u (pn n))) / (2*t) :=
        (le_div_iff₀ (by positivity : 0 < 2*t)).mpr (by simpa using hh)
      simpa [div_eq_mul_inv, mul_comm] using hh'
    apply tendsto_atTop.mpr
    intro B
    let R := |B| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hsmall : ∀ᶠ n in atTop, L * Metric.diam (exclusion C u (pn n)) < 1 / R := by
      have ht : Tendsto (fun n => L * Metric.diam (exclusion C u (pn n))) atTop (𝓝 0) := by simpa using tendsto_const_nhds.mul hd
      exact ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / R))
    filter_upwards [hsmall] with n hn
    have hD : 0 ≤ L * Metric.diam (exclusion C u (pn n)) := mul_nonneg hL.le Metric.diam_nonneg
    have hRD : R * (L * Metric.diam (exclusion C u (pn n))) < 1 := by
      simpa [mul_comm] using (lt_div_iff₀ hR).mp hn
    have hbig : R ≤ extensionBudget (a n) (v n) := by
      by_contra h
      have hh := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge h)) hD
      linarith [hprod n]
    exact (show B ≤ R by dsimp [R]; linarith [le_abs_self B]).trans hbig

  have antipodal_calibration (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
      (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
      (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) (p : pure C u) (b : ExclusionChart C u p)
      (v : EuclideanSpace ℝ (Fin b.dim)) (hv : ‖v‖ = 1) (q : pure C u) (hq : b.param v = q) :
      calibration hc hs hg hB hPR p = (1-comparison C u q (b.param (-v)))/2 := by
    obtain ⟨e, he, hf, ht⟩ := ((calibration_spec hc hs hg hB hPR p).2.2 b v hv).2 q hq
    have h := ht (-v) (by simpa using hv.le)
    simp only [inner_neg_right, real_inner_self_eq_norm_sq, hv, one_pow] at h
    linarith

  have original_whole_limit_calibration (pn : ℕ → pure C u) (p : pure C u) (ht : Tendsto (fun n => D₀ (pn n)) atTop (𝓝 (D₀ p))) :
      Tendsto (fun n => a₀ (pn n)) atTop (𝓝 (a₀ p)) := by
    classical
    let E := EuclideanSpace ℝ (Fin 3)
    choose f hfi hfw using fun n => h3 (pn n)
    let c : ℕ → V := fun n => f n 0
    let L : ℕ → E →L[ℝ] V := fun n => (f n).linear.toContinuousLinearMap
    let b (n : ℕ) : ExclusionChart C u (pn n) := ⟨3, by norm_num, f n, hfi n, hfw n⟩
    have hrepr (n : ℕ) (x : E) : c n + L n x = f n x := by
      simpa [c, L, add_comm] using (congrFun (f n).decomp x).symm
    have hball (n : ℕ) : ExclusionIncidence.ballImage (c n) (L n) = D₀ (pn n) := by
      apply NonemptyCompacts.ext
      change (fun x => c n + L n x) '' _ = exclusion C u (pn n)
      simp_rw [hrepr]
      exact hfw n
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨z, ms, hms, hz, hzQ⟩ := ExclusionIncidence.parameter_subsequence
      (c ∘ ns) (L ∘ ns) (D₀ p) (by simpa [Function.comp_def, hball] using ht.comp hns)
    have heval (x : E) : Tendsto (fun n => f (ns (ms n)) x) atTop (𝓝 (z.1 + z.2 x)) := by
      have hcont : Continuous (fun t : V × (E →L[ℝ] V) => t.1 + t.2 x) := by fun_prop
      simpa only [Function.comp_def, hrepr] using (hcont.tendsto z).comp hz
    have hsphere (x : E) (hx : ‖x‖ = 1) : z.1 + z.2 x ∈ pure C u := by
      apply (ReciprocalPureCompactness.reciprocal_pure_compact hc hs hg hPR).isClosed.mem_of_tendsto (heval x)
      exact Eventually.of_forall fun n =>
        ((chart_boundary hc hs hg hB₀ (pn (ns (ms n))) (b (ns (ms n))))).symm ▸
          (show f (ns (ms n)) x ∈ (b (ns (ms n))).param '' Metric.sphere 0 1 from ⟨x, by simpa using hx, rfl⟩) |>.2
    have hinj : Function.Injective z.2 := by
      rcases ExclusionUniformNoncollapse.sphere_extreme_injective_or_zero (base C u) z.1 z.2 hsphere with hi | hz0
      · exact hi
      · exfalso
        have heq : (D₀ p : Set V) = {z.1} := by
          rw [← hzQ]
          change (fun x => z.1 + z.2 x) '' Metric.closedBall 0 1 = _
          simp [hz0]
        have hn := ((exclusion_ball_faces hc hs hg hB₀).1 p).1
        change (D₀ p : Set V).Nontrivial at hn
        rw [heq] at hn
        exact Set.not_nontrivial_singleton hn
    let fz : E →ᵃ[ℝ] V := z.2.toLinearMap.toAffineMap + AffineMap.const ℝ E z.1
    have hfz (x : E) : fz x = z.1 + z.2 x := by simp [fz, add_comm]
    let bz : ExclusionChart C u p := ⟨3, by norm_num, fz,
      by intro x y h; apply hinj; exact add_left_cancel (by simpa only [hfz] using h),
      by change fz '' _ = _; simp_rw [hfz]; exact congrArg (fun Q : NonemptyCompacts V => (Q : Set V)) hzQ⟩
    obtain ⟨v, hv⟩ := exists_norm_eq E (by norm_num : (0:ℝ) ≤ 1)
    have hpure (n : ℕ) : f n v ∈ pure C u := ((chart_boundary hc hs hg hB₀ (pn n) (b n)).symm ▸
        (show f n v ∈ (b n).param '' Metric.sphere 0 1 from ⟨v, by simpa using hv, rfl⟩)).2
    have hpure' (n : ℕ) : f n (-v) ∈ pure C u := ((chart_boundary hc hs hg hB₀ (pn n) (b n)).symm ▸
        (show f n (-v) ∈ (b n).param '' Metric.sphere 0 1 from ⟨-v, by simpa using hv, rfl⟩)).2
    let qn (n : ℕ) : pure C u := ⟨f (ns (ms n)) v, hpure _⟩
    let rn (n : ℕ) : pure C u := ⟨f (ns (ms n)) (-v), hpure' _⟩
    let q : pure C u := ⟨z.1 + z.2 v, hsphere v hv⟩
    let r : pure C u := ⟨z.1 + z.2 (-v), hsphere (-v) (by simpa using hv)⟩
    have hq : Tendsto qn atTop (𝓝 q) := tendsto_subtype_rng.mpr (heval v)
    have hr : Tendsto rn atTop (𝓝 r) := tendsto_subtype_rng.mpr (heval (-v))
    have hcomp := ((pure_comparison_continuous hs hg hPR).tendsto (q,r)).comp (hq.prodMk_nhds hr)
    have ha (n : ℕ) : a₀ (pn (ns (ms n))) = (1-comparison C u (qn n) (rn n))/2 :=
      antipodal_calibration hc hs hg hB₀ hPR _ (b _) v hv (qn n) rfl
    have hap : a₀ p = (1-comparison C u q r)/2 := by
      simpa only [bz, hfz] using antipodal_calibration hc hs hg hB₀ hPR p bz v hv q (hfz v)
    refine ⟨ms, ?_⟩
    rw [hap]
    simpa only [Function.comp_def, ha] using (tendsto_const_nhds.sub hcomp).div_const 2


  have original_singleton_limit_scalars (pn : ℕ → pure C u) (q : V)
      (ht : Tendsto (fun n => D₀ (pn n)) atTop (𝓝 ({q} : NonemptyCompacts V))) :
      Tendsto (fun n => a₀ (pn n)) atTop (𝓝 0) ∧ Tendsto (fun n => β₀ (pn n)) atTop atTop := by
    classical
    have hd : Tendsto (fun n => Metric.diam (exclusion C u (pn n))) atTop (𝓝 0) := by
      simpa [Function.comp_def, OriginalExclusionLimits.wholeExclusion] using
        (OriginalExclusionLimits.compact_diameter_lipschitz.continuous.tendsto ({q} : NonemptyCompacts V)).comp ht
    let b (n : ℕ) : ExclusionChart C u (pn n) := Classical.choice (hB₀ (pn n))
    have hunit (n : ℕ) : ∃ v : EuclideanSpace ℝ (Fin (b n).dim), ‖v‖ = 1 := by
      letI : Nonempty (Fin (b n).dim) := ⟨⟨0, (b n).dim_pos⟩⟩
      exact exists_norm_eq _ (by norm_num : (0:ℝ) ≤ 1)
    choose v hv using hunit
    have hb := original_diameter_collapse_budget hc hs hg hB₀ hPR pn b v hv hd
    have hbe (n : ℕ) : extensionBudget (b n) (v n) = β₀ (pn n) :=
      ((calibration_spec hc hs hg hB₀ hPR (pn n)).2.2 (b n) (v n) (hv n)).1.2.2
    have hb' : Tendsto (fun n => β₀ (pn n)) atTop atTop := by simpa only [hbe] using hb
    refine ⟨?_, hb'⟩
    have hi := (tendsto_inv_atTop_zero.comp hb').div_const 2
    have he (n : ℕ) : (β₀ (pn n))⁻¹ / 2 = a₀ (pn n) := by
      dsimp [optimalBudget]
      field_simp
    simpa only [Function.comp_def, he, zero_div] using hi


  have original_scalar_subsequence (pn : ℕ → pure C u) (p : pure C u) (hp : Tendsto pn atTop (𝓝 p)) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ((Tendsto (fun n => D₀ (pn (φ n))) atTop (𝓝 (D₀ p)) ∧ Tendsto (fun n => a₀ (pn (φ n))) atTop (𝓝 (a₀ p)) ∧
          Tendsto (fun n => β₀ (pn (φ n))) atTop (𝓝 (β₀ p))) ∨
        ∃ q : pure C u, (q:V) ∈ exclusion C u p ∧ Tendsto (fun n => D₀ (pn (φ n))) atTop (𝓝 ({(q:V)} : NonemptyCompacts V)) ∧
          Tendsto (fun n => a₀ (pn (φ n))) atTop (𝓝 0) ∧
          Tendsto (fun n => β₀ (pn (φ n))) atTop atTop) := by
    obtain ⟨Q, _, φ, hφ, ht⟩ := (NonemptyCompacts.isCompact_subsets_of_isCompact (base_compact hc hs)).tendsto_subseq
        (fun n => (show (D₀ (pn n) : Set V) ⊆ base C u from fun x hx => hx.1))
    refine ⟨φ, hφ, ?_⟩
    rcases ReciprocalExclusionLimits.exclusion_limit_dichotomy hc hs hg h3 hPR
        (hp.comp hφ.tendsto_atTop) (fun n => D₀ (pn (φ n))) Q (fun _ => rfl) ht
        with heq | ⟨q, hq, heq⟩
    · have heq' : Q = D₀ p := NonemptyCompacts.ext heq
      subst Q
      have ha := original_whole_limit_calibration _ p ht
      exact Or.inl ⟨ht, ha, tendsto_const_nhds.div (tendsto_const_nhds.mul ha)
        (by have hh := (calibration_spec hc hs hg hB₀ hPR p).1; positivity)⟩
    · have heq' : Q = ({(q:V)} : NonemptyCompacts V) := NonemptyCompacts.ext heq
      subst Q
      exact Or.inr ⟨q, hq, ht, original_singleton_limit_scalars _ q ht⟩


  have original_calibration_upperSemicontinuous : UpperSemicontinuous a₀ := by
    apply upperSemicontinuous_iff_isClosed_preimage.mpr
    intro t
    apply isSeqClosed_iff_isClosed.mp
    intro pn p hn hp
    obtain ⟨φ, hφ, hwhole | ⟨q, hq, ht, ha, hb⟩⟩ := original_scalar_subsequence pn p hp
    · exact ge_of_tendsto hwhole.2.1 (Eventually.of_forall fun n => hn (φ n))
    · exact (ge_of_tendsto ha (Eventually.of_forall fun n => hn (φ n))).trans (calibration_spec hc hs hg hB₀ hPR p).1.le


  have original_optimalBudget_lowerSemicontinuous : LowerSemicontinuous β₀ := by
    apply lowerSemicontinuous_iff_isClosed_preimage.mpr
    intro t
    apply isSeqClosed_iff_isClosed.mp
    intro pn p hn hp
    obtain ⟨φ, hφ, hwhole | ⟨q, hq, ht, ha, hb⟩⟩ := original_scalar_subsequence pn p hp
    · exact le_of_tendsto hwhole.2.2 (Eventually.of_forall fun n => hn (φ n))
    · have hh := (hb.eventually (eventually_ge_atTop (t+1))).exists
      obtain ⟨n, hlarge⟩ := hh
      have hsmall := hn (φ n)
      change β₀ (pn (φ n)) ≤ t at hsmall
      linarith


  have scalars_continuous_of_whole (p : pure C u) (hp : ContinuousAt D₀ p) : ContinuousAt a₀ p ∧ ContinuousAt β₀ p := by
    have ha : ContinuousAt a₀ p := by
      apply tendsto_nhds_iff_seq_tendsto.mpr
      intro pn hn
      exact original_whole_limit_calibration pn p (hp.tendsto.comp hn)
    refine ⟨ha, ?_⟩
    exact continuousAt_const.div (continuousAt_const.mul ha) (by have hh := (calibration_spec hc hs hg hB₀ hPR p).1; positivity)


  have original_discontinuity_scalar_witness (p : pure C u) (hp : ¬ ContinuousAt D₀ p) :
      ∃ pn : ℕ → pure C u, Tendsto pn atTop (𝓝 p) ∧ ∃ q : pure C u, (q:V) ∈ exclusion C u p ∧
          Tendsto (fun n => D₀ (pn n)) atTop (𝓝 ({(q:V)} : NonemptyCompacts V)) ∧
          Tendsto (fun n => a₀ (pn n)) atTop (𝓝 0) ∧
          Tendsto (fun n => β₀ (pn n)) atTop atTop := by
    obtain ⟨pn, hpn, q, hq, ht⟩ := OriginalExclusionLimits.original_discontinuity_collapse hc hs hg h3 hPR p hp
    have ht' : Tendsto (fun n => D₀ (pn n)) atTop (𝓝 ({(q:V)} : NonemptyCompacts V)) := tendsto_iff_dist_tendsto_zero.mpr ht
    exact ⟨pn, hpn, q, hq, ht', original_singleton_limit_scalars pn q ht'⟩
  have hwhole := OriginalExclusionLimits.original_regular_iff_continuous hc hs hg h3 hPR p
  have ha : ContinuousAt a₀ p → ContinuousAt D₀ p := by
    intro hp
    by_contra hdisc
    obtain ⟨pn, hpn, q, hq, ht, hzero, hbig⟩ := original_discontinuity_scalar_witness p hdisc
    have hh := tendsto_nhds_unique (hp.tendsto.comp hpn) hzero
    exact (calibration_spec hc hs hg hB₀ hPR p).1.ne' hh
  have hb : ContinuousAt β₀ p → ContinuousAt D₀ p := by
    intro hp
    by_contra hdisc
    obtain ⟨pn, hpn, q, hq, ht, hzero, hbig⟩ := original_discontinuity_scalar_witness p hdisc
    have ha' : ContinuousAt a₀ p := by
      have hpos : 0 < β₀ p := by
        dsimp [optimalBudget]; exact one_div_pos.mpr (mul_pos (by norm_num) (calibration_spec hc hs hg hB₀ hPR p).1)
      have hi : ContinuousAt (fun s => 1/(2*β₀ s)) p := continuousAt_const.div (continuousAt_const.mul hp)
          (by positivity : 2 * β₀ p ≠ 0)
      have he : (fun s => 1/(2*β₀ s)) = a₀ := by
        funext s
        dsimp [optimalBudget]
        field_simp
      simpa only [he] using hi
    exact hdisc (ha ha')
  refine ⟨⟨fun h => (scalars_continuous_of_whole p (hwhole.mp h)).1, fun h => hwhole.mpr (ha h)⟩,
    ⟨fun h => (scalars_continuous_of_whole p (hwhole.mp h)).2,
    fun h => hwhole.mpr (hb h)⟩,
    original_calibration_upperSemicontinuous,
    original_optimalBudget_lowerSemicontinuous, ?_, ?_, ?_⟩
  · rw [hwhole, original_local_budget_iff hc hs hg h3 hPR p]
    constructor
    · rintro ⟨U, hU, hpU, B, hB, hbud⟩
      refine ⟨U, hU, hpU, B, hB, ?_⟩
      intro s hsU
      let b := Classical.choice (hB₀ s)
      letI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
      obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin b.dim)) (by norm_num : (0:ℝ) ≤ 1)
      exact (((calibration_spec hc hs hg hB₀ hPR s).2.2 b v hv).1.2.2).symm.le.trans (hbud s hsU b v hv)
    · rintro ⟨U, hU, hpU, B, hB, hbud⟩
      refine ⟨U, hU, hpU, B, hB, ?_⟩
      intro s hsU b v hv
      exact (((calibration_spec hc hs hg hB₀ hPR s).2.2 b v hv).1.2.2).le.trans (hbud s hsU)
  · intro S hS hSR
    have hcont : ContinuousOn β₀ S := by
      intro s hsS
      exact ((scalars_continuous_of_whole s ((OriginalExclusionLimits.original_regular_iff_continuous hc hs hg h3 hPR s).mp
          (hSR hsS))).2).continuousWithinAt
    obtain ⟨B, hB⟩ := hS.bddAbove_image hcont
    exact ⟨B, fun s hsS => hB ⟨s, hsS, rfl⟩⟩
  · have h := calibration_spec hc hs hg hB₀ hPR p
    exact ⟨h.1, h.2.1, fun b v hv => (h.2.2 b v hv).1⟩

#print axioms original_common_continuity_sets

end ScalarTopology

end D5.S3.Quantum.Foundation.OriginalComparisonTopology

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
  ∀ s : pure C u, ∃ e : V →ₗ[ℝ] ℝ, confirms C u p e ∧ e q = 0 ∧ e s = comparison C u p s

/-- Actual whole-ball collapse supplies every pure input of the original edge row.
The same minimizing effect carries its actual zero into the singleton limit. -/
theorem actual_collapse_pure_edge_row
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (h3 : ReciprocalExclusionLimits.threeBallExclusions C u) (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (p q : pure C u) (pn : ℕ → pure C u) (hp : Tendsto pn atTop (𝓝 p)) (hcollapse : Tendsto (fun n => Metric.hausdorffDist
      (exclusion C u (pn n)) {(q : V)}) atTop (𝓝 0)) : PureEdgeRow p q := by
  classical
  have hB : exclusionBalls C u := by
    intro s
    obtain ⟨f, hi, hw⟩ := h3 s
    exact ⟨⟨3, by norm_num, f, hi, hw⟩⟩
  have hpV : Tendsto (fun n => (pn n : V)) atTop (𝓝 (p : V)) := continuous_subtype_val.tendsto p |>.comp hp
  have hqD : (q : V) ∈ exclusion C u p := (exclusion_limit_labels hc hs hg hB pn hpV ({(q : V)} : NonemptyCompacts V)
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
    obtain ⟨h, _, _, hf, hsingle, _⟩ := ReciprocalEndpointExposure.reciprocal_endpoint_exposure hc hs hg p (fun t => (hPR p t).le)
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
  have hfp : f p = 1 := tendsto_nhds_unique ((hev.tendsto (f, (p : V))).comp (hflim.prodMk_nhds (hpV.comp hφ.tendsto_atTop))) (by
      change Tendsto (fun n => e (φ n) (pn (φ n))) atTop (𝓝 1)
      have hones (n : ℕ) : e (φ n) (pn (φ n)) = 1 := (he (φ n)).2
      simpa only [hones] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  have hfs : f s = comparison C u p s := tendsto_nhds_unique
    ((show Continuous (fun g : V →L[ℝ] ℝ => g s) by fun_prop).tendsto f |>.comp hflim)
    (by simpa only [Function.comp_def, heval] using ht.comp hφ.tendsto_atTop)
  have hbound : ∀ᶠ n in atTop, e n q ≤ M * Metric.hausdorffDist (exclusion C u (pn n)) {(q : V)} := by
    filter_upwards [hsmall] with n hn
    obtain ⟨z, hz, hez⟩ := CommonOldExclusionConfirmation.minimizer_has_zero hc hs (pn n) (pure_mem s) (he n) (heval n) hn
    have hzD : z ∈ exclusion C u (pn n) := ⟨hz, (e n).toLinearMap, he n, hez⟩
    have hd : ‖(q : V)-z‖ ≤ Metric.hausdorffDist (exclusion C u (pn n)) {(q : V)} := by
      have h := Metric.infDist_le_hausdorffDist_of_mem hzD (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
          ((exclusion_ball_faces hc hs hg hB).1 (pn n)).1.nonempty (singleton_nonempty (q : V))
          ((exclusion_ball_faces hc hs hg hB).1 (pn n)).2.1.isBounded isCompact_singleton.isBounded)
      simpa [Metric.infDist_singleton, dist_eq_norm, norm_sub_rev] using h
    calc
      e n q = e n ((q : V)-z) := by rw [map_sub, hez, sub_zero]
      _ ≤ ‖e n‖ * ‖(q : V)-z‖ := (le_abs_self _).trans ((e n).le_opNorm _)
      _ ≤ M * ‖(q : V)-z‖ := mul_le_mul_of_nonneg_right (hcommon.1.2.2 (e n) (he n).1) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hd hM
  have hfq : f q = 0 := le_antisymm (le_of_tendsto_of_tendsto
      ((show Continuous (fun g : V →L[ℝ] ℝ => g q) by fun_prop).tendsto f |>.comp hflim)
      (by simpa only [Function.comp_def, mul_zero] using (hcollapse.const_mul M).comp hφ.tendsto_atTop)
      (hφ.tendsto_atTop.eventually hbound))
    ((hf q (pure_mem q).1).1)
  exact ⟨f.toLinearMap, ⟨hf, hfp⟩, hfq, hfs⟩

/-- Actual whole-exclusion collapse saturates both original balls, and the same
ep is least on every original mixed state and the entire original cone. -/
theorem original_row_saturation
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ s : pure C u, ∃ b : ExclusionChart C u s, b.dim = 3)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (hInj : Function.Injective (fun s : pure C u => exclusion C u s)) (p : pure C u) (a : ExclusionChart C u p) (ha : a.dim = 3)
    (ep : V →ₗ[ℝ] ℝ) (hp : ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q) (pn : ℕ → pure C u) (hpn : Tendsto pn atTop (𝓝 p))
    (hcollapse : Tendsto (fun n => Metric.hausdorffDist (exclusion C u (pn n)) {(q : V)}) atTop (𝓝 0)) :
    (∀ w : chartSpace a, ‖w‖ = 1 → extensionBudget a w = 1) ∧
    (∀ b : ExclusionChart C u q, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1) ∧
    (∀ x ∈ base C u, comparison C u p x = ep x) ∧ (∀ f : V →ₗ[ℝ] ℝ, confirms C u p f → ∀ x ∈ C, ep x ≤ f x) ∧
    (∀ w : chartSpace a, ‖w‖ = 1 → ∀ s : pure C u, a.param w = s →
      ∀ z : chartSpace a, ‖z‖ ≤ 1 → comparison C u s (a.param z) = (1 + ⟪w,z⟫) / 2) ∧
    (∀ b : ExclusionChart C u q, ∀ w : chartSpace b, ‖w‖ = 1 → ∀ s : pure C u, b.param w = s → ∀ z : chartSpace b, ‖z‖ ≤ 1 →
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
  obtain ⟨eq, hqunique, hL, hLhalf, hform, hanti, horth⟩ := original_neighbor_support hc hs hg hB hInj p hep k q v hv hq
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
  have hqr := (pure_row_positive_bridge hc hs hg p hep k q v hv hq eq heq _ hL hform hrow).2.2.2.2
  obtain ⟨t, ht, hth, hscale, hbudget⟩ := original_scale_and_sharp_budget hc hs hg hB hPR p a
  have hzero := (comparison_zero_iff hs hg q (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1).mpr hqr
  obtain ⟨_, _, _, hcomp⟩ := hscale v hv q hq
  rw [hcomp (-v) (by simpa using hv.le)] at hzero
  simp only [inner_neg_right, real_inner_self_eq_norm_sq, hv, one_pow] at hzero
  have htunit : t = 1 / 2 := by linarith
  have hbudgeta : ∀ w : chartSpace a, ‖w‖ = 1 → extensionBudget a w = 1 := by
    intro w hw
    simpa [htunit] using (hbudget w hw).2.2
  have hrpure : a.param (-v) ∈ pure C u := ((chart_boundary hc hs hg hB p a).symm ▸
      (show a.param (-v) ∈ a.param '' Metric.sphere 0 1 from ⟨-v, by simpa using hv, rfl⟩)).2
  let r : pure C u := ⟨a.param (-v), hrpure⟩
  have hpr : comparison C u p r = 0 := (comparison_zero_iff hs hg p (pure_mem r)).mpr
      (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le))
  have hbudgetq (b : ExclusionChart C u q) (w : chartSpace b) (hw : ‖w‖ = 1) : extensionBudget b w = 1 := by
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
    have hwP : a.param w ∈ pure C u := ((chart_boundary hc hs hg hB p a).symm ▸
        (show a.param w ∈ a.param '' Metric.sphere 0 1 from ⟨w, by simpa using hw, rfl⟩)).2
    let s : pure C u := ⟨a.param w, hwP⟩
    obtain ⟨_, _, _, hcs⟩ := hscale w hw s rfl
    have hcs0 : comparison C u s (a.param (-w)) = 0 := by
      rw [hcs (-w) (by simpa using hw.le), htunit]
      norm_num [inner_neg_right, real_inner_self_eq_norm_sq, hw]
    have hDs := (comparison_zero_iff hs hg s (SingleLabelNormalBody.chart_mem a (z := -w) (by simpa using hw.le)).1).mp hcs0
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
      have hh : comparison C u p s ≤ f s := csInf_le ⟨0, by rintro z ⟨g, hg', rfl⟩; exact (hg'.1 s (pure_mem s).1).1⟩ ⟨f, hf, rfl⟩
      rw [hpure s] at hh
      simpa only [LinearMap.sub_apply, sub_nonneg] using hh
    intro x hx
    exact sub_nonneg.mp (nonneg_on_cone (base_compact hc hs) hs hnon x hx)
  refine ⟨hbudgeta, hbudgetq, ?_, hleast, ?_, ?_⟩
  · intro x hx
    apply le_antisymm
    · exact csInf_le ⟨0, by rintro z ⟨f, hf, rfl⟩; exact (hf.1 x hx.1).1⟩ ⟨ep, hep.1, rfl⟩
    · change ep x ≤ sInf {z : ℝ | ∃ f : V →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = z}
      apply le_csInf (show ({z : ℝ | ∃ f : V →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = z} : Set ℝ).Nonempty from ⟨ep x, ep, hep.1, rfl⟩)
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ s : pure C u, ∃ b : ExclusionChart C u s, b.dim = 3)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (hInj : Function.Injective (fun s : pure C u => exclusion C u s)) (p : pure C u) (a : ExclusionChart C u p) (ha : a.dim = 3)
    (ep : V →ₗ[ℝ] ℝ) (hp : ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep)
    (v : chartSpace a) (hv : ‖v‖ = 1) (hbudget : 1 < extensionBudget a v) :
    ContinuousAt (OriginalExclusionLimits.wholeExclusion hc hs hg (fun s => ⟨(hEB3 s).choose⟩)) p ∧
      ∃ U : Set (pure C u), IsOpen U ∧ p ∈ U ∧ ∃ B : ℝ, 0 < B ∧ ∀ s ∈ U, ∀ b : ExclusionChart C u s,
          ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w ≤ B := by
  have h3 : ReciprocalExclusionLimits.threeBallExclusions C u := by
    intro s
    obtain ⟨⟨d, hd, f, hi, hw⟩, heq⟩ := hEB3 s
    dsimp at heq
    subst d
    exact ⟨f, hi, hw⟩
  have hcont : ContinuousAt (OriginalExclusionLimits.wholeExclusion hc hs hg (fun s => ⟨(hEB3 s).choose⟩)) p := by
    by_contra hdisc
    obtain ⟨pn, hpn, q, hq, hcollapse⟩ := OriginalExclusionLimits.original_discontinuity_collapse hc hs hg h3 hPR p hdisc
    have hB : exclusionBalls C u := fun s => ⟨(hEB3 s).choose⟩
    have hqS : (q : V) ∈ a.param '' Metric.sphere 0 1 := by
      rw [← chart_boundary hc hs hg hB p a]
      exact ⟨hq, q.property⟩
    obtain ⟨w, hw, hwq⟩ := hqS
    have hw1 : ‖w‖ = 1 := by simpa using hw
    have hsat := original_row_saturation hc hs hg hEB3 hPR hInj p a ha ep hp q w hw1 hwq pn hpn hcollapse
    exact (ne_of_gt hbudget) (hsat.1 v hv)
  have hreg := (OriginalExclusionLimits.original_regular_iff_continuous hc hs hg h3 hPR p).mpr hcont
  obtain ⟨_, _, _, _, hlocal, _, _⟩ := OriginalComparisonTopology.original_common_continuity_sets hc hs hg h3 hPR p
  obtain ⟨U, hU, hpU, B, hBp, hbound⟩ := hlocal.mp hreg
  refine ⟨hcont, U, hU, hpU, B, hBp, ?_⟩
  intro s hsU b w hw
  obtain ⟨_, _, _, _, _, _, _, _, hlaw⟩ := OriginalComparisonTopology.original_common_continuity_sets hc hs hg h3 hPR s
  exact (hlaw b w hw).2.2.le.trans (hbound s hsU)

/-- The original P0 condition concerns A(p), while all of F(p) remains available. -/
def uniqueFullZero (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Set (pure C u) :=
  {p | ∃ ep : V →ₗ[ℝ] ℝ, ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep}

/-- Both residual discontinuity branches retain the entire original pure domain.
In the unique-full-zero branch the same ep is least on all C, and every actual
collapse endpoint has unit budget in every whole chart. -/
theorem original_discontinuity_branches
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ s : pure C u, ∃ b : ExclusionChart C u s, b.dim = 3)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (hInj : Function.Injective (fun s : pure C u => exclusion C u s))
    (p : pure C u) (hSigma : p ∉ OriginalExclusionLimits.regularRegion C u) :
    p ∉ uniqueFullZero C u ∨ ∃ ep : V →ₗ[ℝ] ℝ, (∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep) ∧
        (∀ b : ExclusionChart C u p, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1) ∧
        (∀ x ∈ base C u, comparison C u p x = ep x) ∧ (∀ f : V →ₗ[ℝ] ℝ, confirms C u p f → ∀ x ∈ C, ep x ≤ f x) ∧
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
    obtain ⟨pn, hpn, q, hq, hcollapse⟩ := OriginalExclusionLimits.original_discontinuity_collapse hc hs hg h3 hPR p hdisc
    have apply_collapse (q : pure C u) (pn : ℕ → pure C u) (hpn : Tendsto pn atTop (𝓝 p))
        (ht : Tendsto (fun n => Metric.hausdorffDist (exclusion C u (pn n)) {(q : V)}) atTop (𝓝 0)) :
        (∀ w : chartSpace a, ‖w‖ = 1 → extensionBudget a w = 1) ∧
        (∀ b : ExclusionChart C u q, ∀ w : chartSpace b, ‖w‖ = 1 → extensionBudget b w = 1) ∧
        (∀ x ∈ base C u, comparison C u p x = ep x) ∧ (∀ f : V →ₗ[ℝ] ℝ, confirms C u p f → ∀ x ∈ C, ep x ≤ f x) := by
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
