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
open Set Filter Topology
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

#print axioms original_diameter_collapse_budget

end D5.S3.Quantum.Foundation.OriginalComparisonTopology
