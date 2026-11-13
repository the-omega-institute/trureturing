/- GID: D5/S3/Quantum/Foundation/OriginalComparisonTopology
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalComparisonTopology
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Uniform mixed-input continuity and pure joint continuity on the original carrier. -/

import D5.S3.Quantum.Foundation.OriginalBallScale

/-! The pure reciprocity law is used only to exchange pure endpoints. -/

noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalComparisonTopology
open CircuitBalancedConfirmation ContinuousFrameSum ExclusionWidthCompactness
open FacetZeroGluing ExclusionBallFaces OriginalFacePolarity OriginalBallScale

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

private theorem comparison_le_confirmer
    {p : pure C u} {x : V} (hx : x ∈ base C u)
    {f : V →L[ℝ] ℝ} (hf : f ∈ confirmingEffects C u p) :
    comparison C u p x ≤ f x :=
  csInf_le ⟨0, by rintro r ⟨g, hg, rfl⟩; exact (hg.1 x hx.1).1⟩
    ⟨f.toLinearMap, hf, rfl⟩

/-- One finite positive Lipschitz bound covers every pure row and every pair
of mixed inputs in the whole original normalized base. -/
theorem original_uniform_comparison
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    ∃ L : ℝ, 0 < L ∧ ∀ p : pure C u, ∀ x ∈ base C u, ∀ y ∈ base C u,
      |comparison C u p x - comparison C u p y| ≤ L * ‖x - y‖ := by
  obtain ⟨R, hR⟩ := (effects_compact hs hg).isBounded.exists_norm_le
  let L := |R| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hbound (f : V →L[ℝ] ℝ) (hf : f ∈ effects C u) (x y : V) :
      f x - f y ≤ L * ‖x-y‖ := by
    calc
      f x - f y = f (x-y) := (map_sub f x y).symm
      _ ≤ ‖f (x-y)‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖x-y‖ := f.le_opNorm _
      _ ≤ L * ‖x-y‖ := mul_le_mul_of_nonneg_right
        ((hR f hf).trans (by dsimp [L]; linarith [le_abs_self R])) (norm_nonneg _)
  have hdiff (p : pure C u) (x : V) (hx : x ∈ base C u)
      (y : V) (_hy : y ∈ base C u) :
      comparison C u p x - comparison C u p y ≤ L * ‖x-y‖ := by
    obtain ⟨f, hf, he⟩ := comparison_attained hs hg p y
    rw [he]
    exact (sub_le_sub_right (comparison_le_confirmer hx hf) _).trans (hbound f hf.1 x y)
  refine ⟨L, hL, ?_⟩
  intro p x hx y hy
  exact abs_le.mpr ⟨by
    have hh := hdiff p y hy x hx
    rw [norm_sub_rev] at hh
    linarith, hdiff p x hx y hy⟩

/-- Original pure reciprocity gives joint continuity on all pure labels,
without a mixed-state reciprocity law or a closed-pure-carrier premise. -/
theorem original_joint_pure_comparison
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) :
    ∃ L : ℝ, 0 < L ∧ ∀ p q s t : pure C u,
      |comparison C u p s - comparison C u q t| ≤
        L * (‖(p : V) - q‖ + ‖(s : V) - t‖) := by
  obtain ⟨L, hL, hbound⟩ := original_uniform_comparison hs hg
  refine ⟨L, hL, ?_⟩
  intro p q s t
  have hfirst := hbound s p (pure_mem p) q (pure_mem q)
  rw [← hPR p s, ← hPR q s] at hfirst
  have hsecond := hbound q s (pure_mem s) t (pure_mem t)
  calc
    _ ≤ |comparison C u p s - comparison C u q s| +
        |comparison C u q s - comparison C u q t| := abs_sub_le _ _ _
    _ ≤ L * ‖(p : V) - q‖ + L * ‖(s : V) - t‖ := add_le_add hfirst hsecond
    _ = _ := by ring

#print axioms original_uniform_comparison
#print axioms original_joint_pure_comparison

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
