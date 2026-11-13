/- GID: D5/S3/Quantum/Foundation/OriginalComparisonTopology
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalComparisonTopology
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Uniform mixed-input continuity and pure joint continuity on the original carrier. -/

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
  have hbound : |comparison C u p x - comparison C u p y| ≤ M * ‖x-y‖ := by
    simpa only [Real.dist_eq, Subtype.dist_eq, dist_eq_norm] using h
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
      simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
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
  have hlip : LipschitzWith ⟨2*L, by positivity⟩
      (fun z : P × P => comparison C u z.1 z.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have h1 := hbound z.2 z.1 (pure_mem z.1) w.1 (pure_mem w.1)
    rw [← hPR z.1 z.2, ← hPR w.1 z.2] at h1
    have h2 := hbound w.1 z.2 (pure_mem z.2) w.2 (pure_mem w.2)
    have hf : ‖(z.1 : V)-w.1‖ ≤ dist z w := by
      change dist z.1 w.1 ≤ dist z w
      exact dist_fst_le _ _
    have hsnd : ‖(z.2 : V)-w.2‖ ≤ dist z w := by
      change dist z.2 w.2 ≤ dist z w
      exact dist_snd_le _ _
    change |comparison C u z.1 z.2 - comparison C u w.1 w.2| ≤ (2*L)*dist z w
    exact (abs_sub_le _ _ _).trans (by nlinarith)
  let S : Set (P × P) := {z | δ ≤ ‖(z.1 : V)-z.2‖}
  have hSc : IsCompact S := isCompact_univ.of_isClosed_subset
    (isClosed_le continuous_const (by fun_prop)) (subset_univ _)
  by_cases hne : S.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hSc.exists_isMinOn hne
      (continuous_const.sub hlip.continuous).continuousOn
    have hnepq : z.1 ≠ z.2 := by
      intro heq
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
    exact ⟨1-comparison C u z.1 z.2, by linarith, fun p q hpq => hmin hpq⟩
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
  obtain ⟨t, ht, _, hscale, hbudget⟩ := original_scale_and_sharp_budget hc hs hg hB hPR p a
  obtain ⟨_, _, _, hcomp⟩ := hscale v hv q rfl
  have hgap' := hgap q r ((hdiam p hp).trans hd)
  have hcomp' := hcomp (-v) (by simpa using hv.le)
  have hγt : γ ≤ 2*t := by
    simp only [inner_neg_right, real_inner_self_eq_norm_sq, hv, one_pow] at hcomp'
    change γ ≤ 1 - comparison C u q (a.param (-v)) at hgap'
    rw [hcomp'] at hgap'
    linarith
  rw [(hbudget w hw).2.2]
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

end D5.S3.Quantum.Foundation.OriginalComparisonTopology
