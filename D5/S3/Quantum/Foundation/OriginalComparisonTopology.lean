/- GID: D5/S3/Quantum/Foundation/OriginalComparisonTopology
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalComparisonTopology
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Actual calibration and optimal-budget topology on the entire original pure carrier. -/

import D5.S3.Quantum.Foundation.OriginalBallScale
import D5.S3.Quantum.Foundation.CommonOldExclusionConfirmation
import D5.S3.Quantum.Foundation.OriginalExclusionLimits

/-! The pure reciprocity law is used only to exchange pure endpoints. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalComparisonTopology
open CircuitBalancedConfirmation ContinuousFrameSum ExclusionWidthCompactness
open FacetZeroGluing ExclusionBallFaces OriginalFacePolarity OriginalBallScale

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- One finite positive Lipschitz bound covers every pure row and every pair
of mixed inputs in the whole original normalized base. -/
theorem original_uniform_comparison
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    ∃ L : ℝ, 0 < L ∧ ∀ p : pure C u, ∀ x ∈ base C u, ∀ y ∈ base C u,
      |comparison C u p x - comparison C u p y| ≤ L * ‖x - y‖ := by
  let M := CommonOldExclusionConfirmation.effectNormBound C u
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro p x hx y hy
  have h := (CommonOldExclusionConfirmation.comparison_lipschitz hs hg p).dist_le_mul
    (⟨x, hx⟩ : base C u) (⟨y, hy⟩ : base C u)
  change dist (comparison C u p x) (comparison C u p y) ≤ M * dist x y at h
  have hbound : |comparison C u p x - comparison C u p y| ≤ M * ‖x-y‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using h
  exact hbound.trans (mul_le_mul_of_nonneg_right (by dsimp [M]; linarith [le_abs_self M]) (norm_nonneg _))

/-- The same bound controls every axis in every chart at every original label.
Its scale is obtained from the actual comparison law and attained optimal budget. -/
theorem original_scale_axis_bound
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) :
    ∃ L : ℝ, 0 < L ∧ ∀ (p : pure C u) (a : ExclusionChart C u p),
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
        (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → extensionBudget a v = 1 / (2*t)) ∧
        ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 →
          2*t ≤ L * ‖a.param v - a.param (-v)‖ := by
  obtain ⟨L, hL, hbound⟩ := original_uniform_comparison hs hg
  refine ⟨L, hL, ?_⟩
  intro p a
  obtain ⟨t, ht, hth, hscale, hbudget⟩ := original_scale_and_sharp_budget hc hs hg hB hPR p a
  refine ⟨t, ht, hth, fun v hv => (hbudget v hv).2.2, ?_⟩
  intro v hv
  have hvP : a.param v ∈ pure C u :=
    ((chart_boundary hc hs hg hB p a).symm ▸
      (show a.param v ∈ a.param '' Metric.sphere 0 1 from ⟨v, by simpa using hv, rfl⟩)).2
  let q : pure C u := ⟨a.param v, hvP⟩
  obtain ⟨_, _, _, hcomp⟩ := hscale v hv q rfl
  have hh := hbound q (a.param v) (SingleLabelNormalBody.chart_mem a hv.le).1
    (a.param (-v)) (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1
  rw [hcomp v hv.le, hcomp (-v) (by simpa using hv.le)] at hh
  simp only [inner_neg_right, real_inner_self_eq_norm_sq, hv, one_pow] at hh
  have hh' := (abs_le.mp hh).2
  linarith

/-- A finite budget on any set of original labels forces a uniform positive
diameter there. The set can be a neighborhood in the entire P and need not lie in P0. -/
theorem original_bounded_budget_noncollapse
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    (U : Set (pure C u)) (B : ℝ) (hBpos : 0 < B)
    (hbudget : ∀ p ∈ U, ∀ a : ExclusionChart C u p,
      ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → extensionBudget a v ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ U, δ ≤ Metric.diam (exclusion C u p) := by
  obtain ⟨L, hL, haxis⟩ := original_scale_axis_bound hc hs hg hB hPR
  refine ⟨1 / (B*L), by positivity, ?_⟩
  intro p hp
  obtain ⟨a⟩ := hB p
  obtain ⟨t, ht, _, hbud, hax⟩ := haxis p a
  let E := EuclideanSpace ℝ (Fin a.dim)
  letI : Nonempty (Fin a.dim) := ⟨⟨0, a.dim_pos⟩⟩
  obtain ⟨v, hv⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  have hbd := hbudget p hp a v hv
  rw [hbud v hv] at hbd
  have htB : 1 ≤ B * (2*t) := (div_le_iff₀ (by positivity : 0 < 2*t)).mp hbd
  have hdiam : ‖a.param v - a.param (-v)‖ ≤ Metric.diam (exclusion C u p) := by
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem ((exclusion_ball_faces hc hs hg hB).1 p).2.1.isBounded
      (SingleLabelNormalBody.chart_mem a hv.le)
      (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le))
  apply (div_le_iff₀ (mul_pos hBpos hL)).mpr
  have hh := mul_le_mul_of_nonneg_left ((hax v hv).trans
    (mul_le_mul_of_nonneg_left hdiam hL.le)) hBpos.le
  nlinarith

#print axioms original_scale_axis_bound
#print axioms original_bounded_budget_noncollapse

/-- Every actual diameter-collapse sequence forces the original optimal budgets
to diverge, for every choice of complete charts and unit directions. -/
theorem original_diameter_collapse_budget
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    (pn : ℕ → pure C u) (a : ∀ n, ExclusionChart C u (pn n))
    (v : ∀ n, EuclideanSpace ℝ (Fin (a n).dim)) (hv : ∀ n, ‖v n‖ = 1)
    (hd : Tendsto (fun n => Metric.diam (exclusion C u (pn n))) atTop (𝓝 0)) :
    Tendsto (fun n => extensionBudget (a n) (v n)) atTop atTop := by
  obtain ⟨L, hL, haxis⟩ := original_scale_axis_bound hc hs hg hB hPR
  have hprod (n : ℕ) : 1 ≤ extensionBudget (a n) (v n) *
      (L * Metric.diam (exclusion C u (pn n))) := by
    obtain ⟨t, ht, _, hbudget, hax⟩ := haxis (pn n) (a n)
    rw [hbudget (v n) (hv n)]
    have hdiam : ‖(a n).param (v n) - (a n).param (-v n)‖ ≤
        Metric.diam (exclusion C u (pn n)) := by
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
    have ht : Tendsto (fun n => L * Metric.diam (exclusion C u (pn n))) atTop (𝓝 0) :=
      by simpa using tendsto_const_nhds.mul hd
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

private theorem chart_diameter_axis {p : pure C u} (a : ExclusionChart C u p) :
    ∃ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 ∧
      Metric.diam (exclusion C u p) ≤ ‖a.param v - a.param (-v)‖ := by
  let E := EuclideanSpace ℝ (Fin a.dim)
  let L : E →L[ℝ] V := a.param.linear.toContinuousLinearMap
  letI : Nonempty (Fin a.dim) := ⟨⟨0, a.dim_pos⟩⟩
  have hne : (Metric.sphere (0 : E) 1).Nonempty :=
    (NormedSpace.sphere_nonempty (E := E)).mpr (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne
    L.continuous.norm.continuousOn
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
    exact (mul_le_mul_of_nonneg_left hm hn.le).trans
      (mul_le_of_le_one_left (norm_nonneg _) hz)
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

private theorem pure_comparison_continuous
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) :
    Continuous (fun z : pure C u × pure C u => comparison C u z.1 z.2) := by
  let P := pure C u
  obtain ⟨L, hL, hbound⟩ := original_uniform_comparison hs hg
  have hlip : LipschitzWith ⟨2*L, by positivity⟩
      (fun z : P × P => comparison C u z.1 z.2) := by
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ p q : pure C u, δ ≤ ‖(p : V)-q‖ →
      γ ≤ 1-comparison C u p q := by
  classical
  let P := pure C u
  letI : CompactSpace P := isCompact_iff_compactSpace.mp
    (ReciprocalPureCompactness.reciprocal_pure_compact hc hs hg hPR)
  obtain ⟨L, hL, hbound⟩ := original_uniform_comparison hs hg
  have hlip := pure_comparison_continuous hs hg hPR
  let S : Set (P × P) := {z | δ ≤ ‖(z.1 : V)-z.2‖}
  have hSc : IsCompact S := isCompact_univ.of_isClosed_subset
    (isClosed_le continuous_const (by fun_prop)) (subset_univ _)
  by_cases hne : S.Nonempty
  · have hfun : Continuous (fun z : P × P => 1 - comparison C u z.1 z.2) :=
      continuous_const.sub hlip
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    (U : Set (pure C u)) (δ : ℝ) (hδ : 0 < δ)
    (hdiam : ∀ p ∈ U, δ ≤ Metric.diam (exclusion C u p)) :
    ∃ B : ℝ, 0 < B ∧ ∀ p ∈ U, ∀ a : ExclusionChart C u p,
      ∀ w : EuclideanSpace ℝ (Fin a.dim), ‖w‖ = 1 → extensionBudget a w ≤ B := by
  obtain ⟨γ, hγ, hgap⟩ := uniform_pure_gap hc hs hg hPR δ hδ
  refine ⟨1/γ, by positivity, ?_⟩
  intro p hp a w hw
  obtain ⟨v, hv, hd⟩ := chart_diameter_axis a
  have hqpure : a.param v ∈ pure C u :=
    ((chart_boundary hc hs hg hB p a).symm ▸
      (show a.param v ∈ a.param '' Metric.sphere 0 1 from ⟨v, by simpa using hv, rfl⟩)).2
  have hrpure : a.param (-v) ∈ pure C u :=
    ((chart_boundary hc hs hg hB p a).symm ▸
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

/-- Whole Hausdorff continuity is equivalent to a finite local bound for all
actual optimal budgets, using an open neighborhood in all original P. -/
theorem original_local_budget_iff
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (h3 : ReciprocalExclusionLimits.threeBallExclusions C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)
    (p : pure C u) :
    ContinuousAt (OriginalExclusionLimits.wholeExclusion hc hs hg (OriginalExclusionLimits.ballHyp h3)) p ↔
      ∃ U : Set (pure C u), IsOpen U ∧ p ∈ U ∧ ∃ B : ℝ, 0 < B ∧
        ∀ s ∈ U, ∀ a : ExclusionChart C u s,
          ∀ w : EuclideanSpace ℝ (Fin a.dim), ‖w‖ = 1 → extensionBudget a w ≤ B := by
  let hB := OriginalExclusionLimits.ballHyp h3
  constructor
  · intro hcont
    have hreg := (OriginalExclusionLimits.original_regular_iff_continuous hc hs hg h3 hPR p).mpr hcont
    obtain ⟨j, hj⟩ := mem_iUnion.mp hreg
    let U : Set (pure C u) := interior {s : pure C u |
      1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u s)}
    have hdiam : ∀ s ∈ U, 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u s) := by
      intro s hs
      exact (interior_subset : interior {r : pure C u |
        1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u r)} ⊆
        {r : pure C u | 1 / (j + 1 : ℝ) ≤ Metric.diam (exclusion C u r)}) hs
    obtain ⟨B, hBp, hbudget⟩ := original_noncollapse_bounded_budget hc hs hg hB hPR U
      (1 / (j + 1 : ℝ)) (by positivity) hdiam
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

#print axioms original_diameter_collapse_budget

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
      (BudgetFeasible b v (optimalBudget hc hs hg hB hPR p) ∧
        (∀ M, BudgetFeasible b v M → optimalBudget hc hs hg hB hPR p ≤ M) ∧
        extensionBudget b v = optimalBudget hc hs hg hB hPR p) ∧
      ∀ q : pure C u, b.param v = q → ∃ e : V →ₗ[ℝ] ℝ,
        confirms C u q e ∧
        (∀ z, e (b.param z) = 1-calibration hc hs hg hB hPR p +
          calibration hc hs hg hB hPR p*⟪v,z⟫) ∧
        ∀ z, ‖z‖ ≤ 1 → comparison C u q (b.param z) =
          1-calibration hc hs hg hB hPR p + calibration hc hs hg hB hPR p*⟪v,z⟫ :=
  (original_common_chart_scale hc hs hg hB hPR p (Classical.choice (hB p))).choose_spec

private theorem antipodal_calibration (p : pure C u) (b : ExclusionChart C u p)
    (v : EuclideanSpace ℝ (Fin b.dim)) (hv : ‖v‖ = 1)
    (q : pure C u) (hq : b.param v = q) :
    calibration hc hs hg hB hPR p = (1-comparison C u q (b.param (-v)))/2 := by
  obtain ⟨e, he, hf, ht⟩ := ((calibration_spec hc hs hg hB hPR p).2.2 b v hv).2 q hq
  have h := ht (-v) (by simpa using hv.le)
  simp only [inner_neg_right, real_inner_self_eq_norm_sq, hv, one_pow] at h
  linarith

end IntrinsicScalars

section ScalarTopology

variable (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤)
  (h3 : ReciprocalExclusionLimits.threeBallExclusions C u)
  (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p)

local notation "hB₀" => OriginalExclusionLimits.ballHyp h3
local notation "a₀" => calibration hc hs hg hB₀ hPR
local notation "β₀" => optimalBudget hc hs hg hB₀ hPR
local notation "D₀" => OriginalExclusionLimits.wholeExclusion hc hs hg hB₀

/-- Actual scalar convergence for every whole-ball limit, with arbitrary moving charts.
The extracted limiting affine map is proved injective using the closed pure locus. -/
theorem original_whole_limit_calibration (pn : ℕ → pure C u) (p : pure C u)
    (ht : Tendsto (fun n => D₀ (pn n)) atTop (𝓝 (D₀ p))) :
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
    apply (ReciprocalPureCompactness.reciprocal_pure_compact hc hs hg hPR).isClosed.mem_of_tendsto
      (heval x)
    exact Eventually.of_forall fun n =>
      ((chart_boundary hc hs hg hB₀ (pn (ns (ms n))) (b (ns (ms n))))).symm ▸
        (show f (ns (ms n)) x ∈ (b (ns (ms n))).param '' Metric.sphere 0 1 from
          ⟨x, by simpa using hx, rfl⟩) |>.2
  have hinj : Function.Injective z.2 := by
    rcases ExclusionUniformNoncollapse.sphere_extreme_injective_or_zero
      (base C u) z.1 z.2 hsphere with hi | hz0
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
  have hpure (n : ℕ) : f n v ∈ pure C u :=
    ((chart_boundary hc hs hg hB₀ (pn n) (b n)).symm ▸
      (show f n v ∈ (b n).param '' Metric.sphere 0 1 from ⟨v, by simpa using hv, rfl⟩)).2
  have hpure' (n : ℕ) : f n (-v) ∈ pure C u :=
    ((chart_boundary hc hs hg hB₀ (pn n) (b n)).symm ▸
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

/-- Every actual singleton limit has vanishing scale and divergent optimal budget. -/
theorem original_singleton_limit_scalars (pn : ℕ → pure C u) (q : V)
    (ht : Tendsto (fun n => D₀ (pn n)) atTop (𝓝 ({q} : NonemptyCompacts V))) :
    Tendsto (fun n => a₀ (pn n)) atTop (𝓝 0) ∧
      Tendsto (fun n => β₀ (pn n)) atTop atTop := by
  classical
  have hd : Tendsto (fun n => Metric.diam (exclusion C u (pn n))) atTop (𝓝 0) := by
    simpa [Function.comp_def, OriginalExclusionLimits.wholeExclusion] using
      (OriginalExclusionLimits.compact_diameter_lipschitz.continuous.tendsto
      ({q} : NonemptyCompacts V)).comp ht
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

/-- Every subsequence has a further subsequence with exactly the original
whole-ball scalar limit or the pure singleton zero/infinity limit. -/
theorem original_scalar_subsequence (pn : ℕ → pure C u) (p : pure C u)
    (hp : Tendsto pn atTop (𝓝 p)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((Tendsto (fun n => D₀ (pn (φ n))) atTop (𝓝 (D₀ p)) ∧
        Tendsto (fun n => a₀ (pn (φ n))) atTop (𝓝 (a₀ p)) ∧
        Tendsto (fun n => β₀ (pn (φ n))) atTop (𝓝 (β₀ p))) ∨
      ∃ q : pure C u, (q:V) ∈ exclusion C u p ∧
        Tendsto (fun n => D₀ (pn (φ n))) atTop (𝓝 ({(q:V)} : NonemptyCompacts V)) ∧
        Tendsto (fun n => a₀ (pn (φ n))) atTop (𝓝 0) ∧
        Tendsto (fun n => β₀ (pn (φ n))) atTop atTop) := by
  obtain ⟨Q, _, φ, hφ, ht⟩ :=
    (NonemptyCompacts.isCompact_subsets_of_isCompact (base_compact hc hs)).tendsto_subseq
      (fun n => (show (D₀ (pn n) : Set V) ⊆ base C u from fun x hx => hx.1))
  refine ⟨φ, hφ, ?_⟩
  rcases ReciprocalExclusionLimits.exclusion_limit_dichotomy hc hs hg h3 hPR
      (hp.comp hφ.tendsto_atTop) (fun n => D₀ (pn (φ n))) Q (fun _ => rfl) ht
      with heq | ⟨q, hq, heq⟩
  · have heq' : Q = D₀ p := NonemptyCompacts.ext heq
    subst Q
    have ha := original_whole_limit_calibration hc hs hg h3 hPR _ p ht
    exact Or.inl ⟨ht, ha, tendsto_const_nhds.div (tendsto_const_nhds.mul ha)
      (by have hh := (calibration_spec hc hs hg hB₀ hPR p).1; positivity)⟩
  · have heq' : Q = ({(q:V)} : NonemptyCompacts V) := NonemptyCompacts.ext heq
    subst Q
    exact Or.inr ⟨q, hq, ht, original_singleton_limit_scalars hc hs hg h3 hPR _ q ht⟩

/-- The actual coefficient is upper semicontinuous on all original P. -/
theorem original_calibration_upperSemicontinuous : UpperSemicontinuous a₀ := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro t
  apply isSeqClosed_iff_isClosed.mp
  intro pn p hn hp
  obtain ⟨φ, hφ, hwhole | ⟨q, hq, ht, ha, hb⟩⟩ :=
    original_scalar_subsequence hc hs hg h3 hPR pn p hp
  · exact ge_of_tendsto hwhole.2.1 (Eventually.of_forall fun n => hn (φ n))
  · exact (ge_of_tendsto ha (Eventually.of_forall fun n => hn (φ n))).trans
      (calibration_spec hc hs hg hB₀ hPR p).1.le

/-- The original attained optimum is lower semicontinuous on all original P. -/
theorem original_optimalBudget_lowerSemicontinuous : LowerSemicontinuous β₀ := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro t
  apply isSeqClosed_iff_isClosed.mp
  intro pn p hn hp
  obtain ⟨φ, hφ, hwhole | ⟨q, hq, ht, ha, hb⟩⟩ :=
    original_scalar_subsequence hc hs hg h3 hPR pn p hp
  · exact le_of_tendsto hwhole.2.2 (Eventually.of_forall fun n => hn (φ n))
  · have hh := (hb.eventually (eventually_ge_atTop (t+1))).exists
    obtain ⟨n, hlarge⟩ := hh
    have hsmall := hn (φ n)
    change β₀ (pn (φ n)) ≤ t at hsmall
    linarith

/-- Whole-ball continuity forces continuity of the actual common scalar and optimum. -/
private theorem scalars_continuous_of_whole (p : pure C u)
    (hp : ContinuousAt D₀ p) : ContinuousAt a₀ p ∧ ContinuousAt β₀ p := by
  have ha : ContinuousAt a₀ p := by
    apply tendsto_nhds_iff_seq_tendsto.mpr
    intro pn hn
    exact original_whole_limit_calibration hc hs hg h3 hPR pn p (hp.tendsto.comp hn)
  refine ⟨ha, ?_⟩
  exact continuousAt_const.div (continuousAt_const.mul ha)
    (by have hh := (calibration_spec hc hs hg hB₀ hPR p).1; positivity)

/-- Every actual whole-exclusion discontinuity has the complete scalar witness. -/
theorem original_discontinuity_scalar_witness (p : pure C u)
    (hp : ¬ ContinuousAt D₀ p) :
    ∃ pn : ℕ → pure C u, Tendsto pn atTop (𝓝 p) ∧
      ∃ q : pure C u, (q:V) ∈ exclusion C u p ∧
        Tendsto (fun n => D₀ (pn n)) atTop (𝓝 ({(q:V)} : NonemptyCompacts V)) ∧
        Tendsto (fun n => a₀ (pn n)) atTop (𝓝 0) ∧
        Tendsto (fun n => β₀ (pn n)) atTop atTop := by
  obtain ⟨pn, hpn, q, hq, ht⟩ :=
    OriginalExclusionLimits.original_discontinuity_collapse hc hs hg h3 hPR p hp
  have ht' : Tendsto (fun n => D₀ (pn n)) atTop (𝓝 ({(q:V)} : NonemptyCompacts V)) :=
    tendsto_iff_dist_tendsto_zero.mpr ht
  exact ⟨pn, hpn, q, hq, ht', original_singleton_limit_scalars hc hs hg h3 hPR pn q ht'⟩

/-- The entire regular region is exactly all three actual continuity sets. -/
theorem original_common_continuity_sets (p : pure C u) :
    (p ∈ OriginalExclusionLimits.regularRegion C u ↔ ContinuousAt a₀ p) ∧
    (p ∈ OriginalExclusionLimits.regularRegion C u ↔ ContinuousAt β₀ p) ∧
    UpperSemicontinuous a₀ ∧ LowerSemicontinuous β₀ ∧
    (p ∈ OriginalExclusionLimits.regularRegion C u ↔
      ∃ U : Set (pure C u), IsOpen U ∧ p ∈ U ∧ ∃ B : ℝ, 0 < B ∧
        ∀ s ∈ U, β₀ s ≤ B) ∧
    (∀ S : Set (pure C u), IsCompact S → S ⊆ OriginalExclusionLimits.regularRegion C u →
      ∃ B : ℝ, ∀ s ∈ S, β₀ s ≤ B) ∧
    (0 < a₀ p ∧ a₀ p ≤ 1/2 ∧
      ∀ b : ExclusionChart C u p, ∀ v : EuclideanSpace ℝ (Fin b.dim), ‖v‖ = 1 →
        BudgetFeasible b v (β₀ p) ∧
          (∀ M, BudgetFeasible b v M → β₀ p ≤ M) ∧ extensionBudget b v = β₀ p) := by
  have hwhole := OriginalExclusionLimits.original_regular_iff_continuous hc hs hg h3 hPR p
  have ha : ContinuousAt a₀ p → ContinuousAt D₀ p := by
    intro hp
    by_contra hdisc
    obtain ⟨pn, hpn, q, hq, ht, hzero, hbig⟩ :=
      original_discontinuity_scalar_witness hc hs hg h3 hPR p hdisc
    have hh := tendsto_nhds_unique (hp.tendsto.comp hpn) hzero
    exact (calibration_spec hc hs hg hB₀ hPR p).1.ne' hh
  have hb : ContinuousAt β₀ p → ContinuousAt D₀ p := by
    intro hp
    by_contra hdisc
    obtain ⟨pn, hpn, q, hq, ht, hzero, hbig⟩ :=
      original_discontinuity_scalar_witness hc hs hg h3 hPR p hdisc
    have ha' : ContinuousAt a₀ p := by
      have hpos : 0 < β₀ p := by
        dsimp [optimalBudget]; exact one_div_pos.mpr (mul_pos (by norm_num)
          (calibration_spec hc hs hg hB₀ hPR p).1)
      have hi : ContinuousAt (fun s => 1/(2*β₀ s)) p :=
        continuousAt_const.div (continuousAt_const.mul hp)
          (by positivity : 2 * β₀ p ≠ 0)
      have he : (fun s => 1/(2*β₀ s)) = a₀ := by
        funext s
        dsimp [optimalBudget]
        field_simp
      simpa only [he] using hi
    exact hdisc (ha ha')
  refine ⟨⟨fun h => (scalars_continuous_of_whole hc hs hg h3 hPR p (hwhole.mp h)).1,
    fun h => hwhole.mpr (ha h)⟩,
    ⟨fun h => (scalars_continuous_of_whole hc hs hg h3 hPR p (hwhole.mp h)).2,
    fun h => hwhole.mpr (hb h)⟩,
    original_calibration_upperSemicontinuous hc hs hg h3 hPR,
    original_optimalBudget_lowerSemicontinuous hc hs hg h3 hPR, ?_, ?_, ?_⟩
  · rw [hwhole, original_local_budget_iff hc hs hg h3 hPR p]
    constructor
    · rintro ⟨U, hU, hpU, B, hB, hbud⟩
      refine ⟨U, hU, hpU, B, hB, ?_⟩
      intro s hsU
      let b := Classical.choice (hB₀ s)
      letI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
      obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin b.dim))
        (by norm_num : (0:ℝ) ≤ 1)
      exact (((calibration_spec hc hs hg hB₀ hPR s).2.2 b v hv).1.2.2).symm.le.trans
        (hbud s hsU b v hv)
    · rintro ⟨U, hU, hpU, B, hB, hbud⟩
      refine ⟨U, hU, hpU, B, hB, ?_⟩
      intro s hsU b v hv
      exact (((calibration_spec hc hs hg hB₀ hPR s).2.2 b v hv).1.2.2).le.trans (hbud s hsU)
  · intro S hS hSR
    have hcont : ContinuousOn β₀ S := by
      intro s hsS
      exact ((scalars_continuous_of_whole hc hs hg h3 hPR s
        ((OriginalExclusionLimits.original_regular_iff_continuous hc hs hg h3 hPR s).mp
          (hSR hsS))).2).continuousWithinAt
    obtain ⟨B, hB⟩ := hS.bddAbove_image hcont
    exact ⟨B, fun s hsS => hB ⟨s, hsS, rfl⟩⟩
  · have h := calibration_spec hc hs hg hB₀ hPR p
    exact ⟨h.1, h.2.1, fun b v hv => (h.2.2 b v hv).1⟩

#print axioms original_whole_limit_calibration
#print axioms original_scalar_subsequence
#print axioms original_calibration_upperSemicontinuous
#print axioms original_optimalBudget_lowerSemicontinuous
#print axioms original_discontinuity_scalar_witness
#print axioms original_common_continuity_sets

end ScalarTopology

end D5.S3.Quantum.Foundation.OriginalComparisonTopology
