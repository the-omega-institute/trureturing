/- GID: D5/S3/Quantum/Foundation/OriginalBallScale
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalBallScale
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Intrinsic original ball scales, attained extension budgets and uniform noncollapse bounds. -/

import D5.S3.Quantum.Foundation.OriginalRegularHeight
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
import D5.S3.Quantum.Foundation.CommonOldExclusionConfirmation

/-! Common scale and optimal positive-extension budgets on the original whole ball. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalBallScale
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open WholePairBallConfirmation OriginalFacePolarity OriginalRegularHeight
open ExclusionWidthCompactness ReciprocalEndpointExposure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The same original confirmer attains every mixed input of the whole chart. -/
private theorem directional_attainment
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    {p : pure C u} (a : ExclusionChart C u p)
    (v : EuclideanSpace ℝ (Fin a.dim)) (hv : ‖v‖ = 1)
    (q : pure C u) (hq : a.param v = q) :
    ∃ (t : ℝ) (e : V →ₗ[ℝ] ℝ), 0 ≤ t ∧ t ≤ 1 / 2 ∧ confirms C u q e ∧
      (∀ z, e (a.param z) = 1 - t + t * ⟪v, z⟫) ∧
      (∀ z, ‖z‖ ≤ 1 → comparison C u q (a.param z) = 1 - t + t * ⟪v, z⟫) := by
  obtain ⟨e, he, hmin⟩ := comparison_attained hs hg q (a.param (-v))
  let t := (1 - e (a.param (-v))) / 2
  have her := he.1 _ (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1.1
  rw [chart_unit a] at her
  change 0 ≤ e (a.param (-v)) ∧ e (a.param (-v)) ≤ 1 at her
  have ht : 0 ≤ t ∧ t ≤ 1 / 2 := by dsimp [t]; constructor <;> linarith
  have hpeak := peak_formula a e.toLinearMap he.1 v hv (hq ▸ he.2)
  have hform (z) : e (a.param z) = 1 - t + t * ⟪v, z⟫ := by
    dsimp [t]
    have hh := hpeak z
    change e (a.param z) = 1 - (1 - e (a.param (-v))) / 2 * (1 - ⟪v, z⟫) at hh
    rw [hh]
    ring
  refine ⟨t, e.toLinearMap, ht.1, ht.2, ⟨he.1, he.2⟩, ?_, ?_⟩
  · intro z
    exact hform z
  · intro z hz
    have hx := SingleLabelNormalBody.chart_mem a hz
    have hb : BddBelow {r | ∃ f, confirms C u q f ∧ f (a.param z) = r} :=
      ⟨0, by rintro r ⟨f, hf, rfl⟩; exact (hf.1 _ hx.1.1).1⟩
    have hne : ({r | ∃ f, confirms C u q f ∧ f (a.param z) = r} : Set ℝ).Nonempty :=
      ⟨e (a.param z), e.toLinearMap, ⟨he.1, he.2⟩, rfl⟩
    apply le_antisymm
    · exact (csInf_le hb ⟨e.toLinearMap, ⟨he.1, he.2⟩, rfl⟩).trans_eq (hform z)
    · apply le_csInf hne
      rintro r ⟨f, hf, rfl⟩
      have hr : comparison C u q (a.param (-v)) ≤ f (a.param (-v)) :=
        csInf_le ⟨0, by rintro r ⟨g, hg, rfl⟩; exact
          (hg.1 _ (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1.1).1⟩
          ⟨f, hf, rfl⟩
      rw [hmin] at hr
      have htf : (1 - f (a.param (-v))) / 2 ≤ t := by dsimp [t]; linarith
      have hzv : ⟪v, z⟫ ≤ 1 := (real_inner_le_norm v z).trans (by simpa [hv] using hz)
      rw [peak_formula a f hf.1 v hv (hq ▸ hf.2) z]
      nlinarith

/-- One scale works on every direction and every mixed point in this arbitrary chart.
No injectivity of labels or singleton full confirmer is assumed. -/
theorem original_ball_scale
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hB : exclusionBalls C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (p : pure C u) (a : ExclusionChart C u p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
      ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 →
      ∀ q : pure C u, a.param v = q →
      ∃ e : V →ₗ[ℝ] ℝ, confirms C u q e ∧
        (∀ z, e (a.param z) = 1 - t + t * ⟪v, z⟫) ∧
        (∀ z, ‖z‖ ≤ 1 → comparison C u q (a.param z) = 1 - t + t * ⟪v, z⟫) := by
  classical
  let E := EuclideanSpace ℝ (Fin a.dim)
  letI : Nonempty (Fin a.dim) := ⟨⟨0, a.dim_pos⟩⟩
  obtain ⟨v₀, hv₀⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  have hpure (v : E) (hv : ‖v‖ = 1) : a.param v ∈ pure C u :=
    ((chart_boundary hc hs hg hB p a).symm ▸
      (show a.param v ∈ a.param '' Metric.sphere 0 1 from ⟨v, by simpa using hv, rfl⟩)).2
  let q₀ : pure C u := ⟨a.param v₀, hpure v₀ hv₀⟩
  obtain ⟨t₀, e₀, ht₀, ht₀half, he₀, hform₀, hcomp₀⟩ :=
    directional_attainment hs hg a v₀ hv₀ q₀ rfl
  have ht₀pos : 0 < t₀ := by
    obtain ⟨h, hh, hzero, he, hone, _⟩ :=
      reciprocal_endpoint_exposure hc hs hg q₀ (fun x => (hPR q₀ x).le)
    have hr := SingleLabelNormalBody.chart_mem a (by simpa using hv₀.le : ‖-v₀‖ ≤ 1)
    have hne : a.param (-v₀) ≠ (q₀ : V) := by
      intro heq
      have hh : -v₀ = v₀ := a.injective heq
      have hz : v₀ = 0 := by
        have hz2 : (2 : ℝ) • v₀ = 0 := by
          calc
            (2 : ℝ) • v₀ = v₀ - (-v₀) := by module
            _ = 0 := by rw [hh]; simp
        exact (smul_eq_zero.mp hz2).resolve_left (by norm_num)
      simp [hz] at hv₀
    have hlow : 0 < h (a.param (-v₀)) := by
      apply lt_of_le_of_ne (hh _ hr.1.1).1
      intro hz
      exact hne (show a.param (-v₀) ∈ ({(q₀ : V)} : Set V) from
        hzero ▸ (show a.param (-v₀) ∈ {y | y ∈ base C u ∧ h y = 0} from ⟨hr.1, hz.symm⟩))
    have hle : comparison C u q₀ (a.param (-v₀)) ≤ (u - h) (a.param (-v₀)) :=
      csInf_le ⟨0, by rintro r ⟨f, hf, rfl⟩; exact (hf.1 _ hr.1.1).1⟩ ⟨u - h, he, rfl⟩
    rw [hcomp₀ (-v₀) (by simpa using hv₀.le)] at hle
    simp only [inner_neg_right, real_inner_self_eq_norm_sq, hv₀, one_pow, mul_neg,
      mul_one, LinearMap.sub_apply, chart_unit a] at hle
    linarith
  refine ⟨t₀, ht₀pos, ht₀half, ?_⟩
  intro v hv q hq
  obtain ⟨t, e, ht, hthalf, he, hform, hcomp⟩ := directional_attainment hs hg a v hv q hq
  have heq : t = t₀ := by
    by_cases hsame : v = v₀
    · have hqq : q = q₀ := Subtype.val_injective (by simpa [q₀, hsame] using hq.symm)
      have hh := (hcomp (-v) (by simpa using hv.le)).symm.trans
        (hqq ▸ hcomp₀ (-v) (by simpa using hv.le))
      simp only [inner_neg_right, real_inner_self_eq_norm_sq, hv, hsame, hv₀, one_pow] at hh
      nlinarith
    · have hinner : ⟪v, v₀⟫ < 1 := by
        have hh : 0 < ‖v - v₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hsame))
        rw [norm_sub_sq_real, hv, hv₀] at hh
        nlinarith
      have hh := hPR q q₀
      rw [← hq] at hh
      change comparison C u (a.param v) (a.param v₀) = comparison C u (a.param v₀) (a.param v) at hh
      rw [show comparison C u (a.param v) (a.param v₀) = 1 - t + t * ⟪v, v₀⟫ from hq ▸ hcomp v₀ hv₀.le,
        hcomp₀ v hv.le, real_inner_comm v₀ v] at hh
      rw [show ⟪v₀, v⟫ = ⟪v, v₀⟫ from real_inner_comm _ _] at hh
      nlinarith
  exact ⟨e, he, heq ▸ hform, heq ▸ hcomp⟩

/-- Feasibility uses the original positive cone and unit, not a reciprocal definition. -/
def BudgetFeasible {p : V} (a : ExclusionChart C u p)
    (v : EuclideanSpace ℝ (Fin a.dim)) (M : ℝ) : Prop :=
  0 ≤ M ∧ ∃ g : V →ₗ[ℝ] ℝ,
    (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ M * u x) ∧
    ∀ z, ‖z‖ ≤ 1 → g (a.param z) = (1 + ⟪v, z⟫) / 2

/-- The original infimum over all positive extensions and all nonnegative budgets. -/
def extensionBudget {p : V} (a : ExclusionChart C u p)
    (v : EuclideanSpace ℝ (Fin a.dim)) : ℝ :=
  sInf {M : ℝ | BudgetFeasible a v M}

private theorem sharp_budget {p : pure C u} (a : ExclusionChart C u p)
    (t : ℝ) (ht : 0 < t)
    (v : EuclideanSpace ℝ (Fin a.dim)) (hv : ‖v‖ = 1)
    (q : pure C u) (hq : a.param (-v) = q)
    (e : V →ₗ[ℝ] ℝ) (he : confirms C u q e)
    (hform : ∀ z, e (a.param z) = 1 - t + t * ⟪-v, z⟫)
    (hcomp : comparison C u q (a.param v) = 1 - 2 * t) :
    BudgetFeasible a v (1 / (2 * t)) ∧
      (∀ M, BudgetFeasible a v M → 1 / (2 * t) ≤ M) ∧
      extensionBudget a v = 1 / (2 * t) := by
  have ht2 : 0 < 2 * t := by positivity
  have hupper : BudgetFeasible a v (1 / (2 * t)) := by
    refine ⟨by positivity, (2 * t)⁻¹ • (u - e), ?_, ?_⟩
    · intro x hx
      change 0 ≤ (2 * t)⁻¹ * (u x - e x) ∧
        (2 * t)⁻¹ * (u x - e x) ≤ (1 / (2 * t)) * u x
      have hh := he.1 x hx
      constructor
      · exact mul_nonneg (inv_nonneg.mpr ht2.le) (sub_nonneg.mpr hh.2)
      · simpa only [one_div] using mul_le_mul_of_nonneg_left
          (show u x - e x ≤ u x by linarith) (inv_nonneg.mpr ht2.le)
    · intro z hz
      change (2 * t)⁻¹ * (u (a.param z) - e (a.param z)) = _
      rw [chart_unit a, hform z, inner_neg_left]
      field_simp
      <;> ring
  have hlower : ∀ M, BudgetFeasible a v M → 1 / (2 * t) ≤ M := by
    rintro M ⟨hM0, g, hg, hrestrict⟩
    have hgq := hrestrict v hv.le
    have hgm := hrestrict (-v) (by simpa using hv.le)
    simp only [real_inner_self_eq_norm_sq, hv, one_pow, inner_neg_right] at hgq hgm
    have hM : 1 ≤ M := by
      have hh := (hg _ (SingleLabelNormalBody.chart_mem a hv.le).1.1).2
      rw [chart_unit a] at hh
      linarith
    have hMpos : 0 < M := by linarith
    let f : V →ₗ[ℝ] ℝ := u - M⁻¹ • g
    have hf : confirms C u q f := by
      refine ⟨?_, ?_⟩
      · intro x hx
        have hh := hg x hx
        have hbound : M⁻¹ * g x ≤ u x := (inv_mul_le_iff₀ hMpos).mpr (by nlinarith [hh.2])
        change 0 ≤ u x - M⁻¹ * g x ∧ u x - M⁻¹ * g x ≤ u x
        constructor
        · linarith
        · exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hMpos.le) hh.1)
      · rw [← hq]
        change u (a.param (-v)) - M⁻¹ * g (a.param (-v)) = 1
        rw [chart_unit a]
        have hz : g (a.param (-v)) = 0 := by linarith [hgm]
        rw [hz]; ring
    have hle : comparison C u q (a.param v) ≤ f (a.param v) :=
      csInf_le ⟨0, by rintro r ⟨k, hk, rfl⟩; exact
        (hk.1 _ (SingleLabelNormalBody.chart_mem a hv.le).1.1).1⟩ ⟨f, hf, rfl⟩
    rw [hcomp] at hle
    change 1 - 2 * t ≤ u (a.param v) - M⁻¹ * g (a.param v) at hle
    rw [chart_unit a] at hle
    have hg1 : g (a.param v) = 1 := by linarith [hgq]
    rw [hg1, mul_one] at hle
    apply (div_le_iff₀ ht2).mpr
    have hh : 1 ≤ (2 * t) * M := (inv_le_iff_one_le_mul₀ hMpos).mp (by linarith : M⁻¹ ≤ 2 * t)
    nlinarith
  refine ⟨hupper, hlower, le_antisymm ?_ ?_⟩
  · exact csInf_le ⟨0, fun _ h => h.1⟩ hupper
  · exact le_csInf ⟨_, hupper⟩ (fun M hM => hlower M hM)

/-- Each actual chart has a common strictly positive scale and the original
optimal positive-extension budget, attained in every unit direction. -/
theorem original_scale_and_sharp_budget
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (p : pure C u) (a : ExclusionChart C u p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
      (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 →
        ∀ q : pure C u, a.param v = q →
        ∃ e : V →ₗ[ℝ] ℝ, confirms C u q e ∧
          (∀ z, e (a.param z) = 1 - t + t * ⟪v, z⟫) ∧
          (∀ z, ‖z‖ ≤ 1 → comparison C u q (a.param z) = 1 - t + t * ⟪v, z⟫)) ∧
      (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 →
        BudgetFeasible a v (1 / (2 * t)) ∧
        (∀ M, BudgetFeasible a v M → 1 / (2 * t) ≤ M) ∧
        extensionBudget a v = 1 / (2 * t)) := by
  obtain ⟨t, ht, hthalf, hscale⟩ := original_ball_scale hc hs hg hB hPR p a
  refine ⟨t, ht, hthalf, hscale, ?_⟩
  intro v hv
  have hq : a.param (-v) ∈ pure C u :=
    ((chart_boundary hc hs hg hB p a).symm ▸
      (show a.param (-v) ∈ a.param '' Metric.sphere 0 1 from
        ⟨-v, by simpa using hv, rfl⟩)).2
  obtain ⟨e, he, hform, hcomp⟩ := hscale (-v) (by simpa using hv) ⟨a.param (-v), hq⟩ rfl
  apply sharp_budget a t ht v hv ⟨a.param (-v), hq⟩ rfl e he hform
  have hh := hcomp v hv.le
  simp only [inner_neg_left, real_inner_self_eq_norm_sq, hv, one_pow, mul_neg, mul_one] at hh
  linarith

private theorem affine_positive_lift {p : pure C u} (a : ExclusionChart C u p)
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (B : ℝ) (hB : 1 ≤ B)
    (hlift : ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → BudgetFeasible a v B)
    (h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ)
    (hpos : ∀ z, ‖z‖ ≤ 1 → 0 ≤ h z) :
    ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x) ∧
      (∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z) ∧
      ((∀ z, ‖z‖ ≤ 1 → h z ≤ 1) → ∀ x ∈ C, g x ≤ B * u x) := by
  obtain ⟨b, hb⟩ := affine_riesz h
  have hc : ‖b‖ ≤ h 0 := affine_nonneg_bound (fun z hz => by rw [← hb]; exact hpos z hz)
  have hu (x : V) (hx : x ∈ C) : 0 ≤ u x := by
    by_cases hz : x = 0
    · simp [hz]
    · exact (hs x hx hz).le
  by_cases hb0 : b = 0
  · refine ⟨h 0 • u, ?_, ?_, ?_⟩
    · intro x hx
      exact mul_nonneg (hpos 0 (by simp)) (hu x hx)
    · intro z hz
      simp [hb z, hb0, chart_unit a]
    · intro htop x hx
      change h 0 * u x ≤ B * u x
      exact mul_le_mul_of_nonneg_right ((htop 0 (by simp)).trans hB) (hu x hx)
  · have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
    let v := ‖b‖⁻¹ • b
    have hv : ‖v‖ = 1 := by simp [v, norm_smul, hbpos.ne']
    obtain ⟨_, g, hg, hgval⟩ := hlift v hv
    let G : V →ₗ[ℝ] ℝ := (h 0 - ‖b‖) • u + (2 * ‖b‖) • g
    refine ⟨G, ?_, ?_, ?_⟩
    · intro x hx
      change 0 ≤ (h 0 - ‖b‖) * u x + (2 * ‖b‖) * g x
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hc) (hu x hx))
        (mul_nonneg (by positivity) (hg x hx).1)
    · intro z hz
      change (h 0 - ‖b‖) * u (a.param z) + (2 * ‖b‖) * g (a.param z) = h z
      rw [chart_unit a, hgval z hz, hb z]
      simp only [v, inner_smul_left, starRingEnd_apply, star_trivial]
      field_simp
      <;> ring
    · intro htop x hx
      have hcn : ‖b‖ ≤ 1 - h 0 := by
        have hhbound := affine_nonneg_bound (a := 1 - h 0) (v := -b) (fun z hz => by
          have hh := htop z hz
          rw [hb z] at hh
          simp only [inner_neg_left]
          linarith)
        simpa using hhbound
      have hscalar : h 0 - ‖b‖ + 2 * ‖b‖ * B ≤ B := by
        have h1 : 2 * ‖b‖ ≤ 1 := by linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr h1)]
      change (h 0 - ‖b‖) * u x + (2 * ‖b‖) * g x ≤ B * u x
      calc
        _ ≤ (h 0 - ‖b‖) * u x + (2 * ‖b‖) * (B * u x) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (hg x hx).2
            (show 0 ≤ 2 * ‖b‖ by positivity))
        _ = (h 0 - ‖b‖ + 2 * ‖b‖ * B) * u x := by ring
        _ ≤ B * u x := mul_le_mul_of_nonneg_right hscalar (hu x hx)

/-- The original optimum is common to all directions and to the entire affine
face-effect family. Every positive affine face function has an actual positive lift. -/
theorem original_full_face_budget
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (p : pure C u) (a : ExclusionChart C u p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
      (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 →
        BudgetFeasible a v (1 / (2 * t)) ∧
        (∀ M, BudgetFeasible a v M → 1 / (2 * t) ≤ M) ∧
        extensionBudget a v = 1 / (2 * t)) ∧
      (∀ h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ,
        (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z) →
        ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x) ∧
          (∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z) ∧
          ((∀ z, ‖z‖ ≤ 1 → h z ≤ 1) → ∀ x ∈ C, g x ≤ (1 / (2 * t)) * u x)) ∧
      (∀ B : ℝ, (∀ h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ,
        (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
        ∃ g : V →ₗ[ℝ] ℝ,
          (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ B * u x) ∧
          ∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z) → 1 / (2 * t) ≤ B) := by
  obtain ⟨t, ht, hthalf, _, hbudget⟩ := original_scale_and_sharp_budget hc hs hg hB hPR p a
  have hBmin : 1 ≤ 1 / (2 * t) := (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr (by linarith)
  refine ⟨t, ht, hthalf, hbudget,
    fun h hh => affine_positive_lift a hs _ hBmin (fun v hv => (hbudget v hv).1) h hh, ?_⟩
  intro B hwhole
  let E := EuclideanSpace ℝ (Fin a.dim)
  letI : Nonempty (Fin a.dim) := ⟨⟨0, a.dim_pos⟩⟩
  obtain ⟨v, hv⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  let h : E →ᵃ[ℝ] ℝ := (1 / 2 : ℝ) •
    (AffineMap.const ℝ E 1 + (InnerProductSpace.toDual ℝ E v).toLinearMap.toAffineMap)
  have hh (z : E) : h z = (1 + ⟪v, z⟫) / 2 := by simp [h]; ring
  obtain ⟨g, hg, hgz⟩ := hwhole h (by
    intro z hz
    rw [hh]
    have hi := abs_real_inner_le_norm v z
    rw [hv, one_mul] at hi
    have hi' := abs_le.mp (hi.trans hz)
    constructor <;> linarith)
  have hB0 : 0 ≤ B := by
    have hh' := (hg _ (SingleLabelNormalBody.chart_mem a hv.le).1.1).2
    rw [chart_unit a, hgz v hv.le, hh] at hh'
    simp only [real_inner_self_eq_norm_sq, hv, one_pow] at hh'
    linarith
  exact (hbudget v hv).2.1 B ⟨hB0, g, hg, fun z hz => (hgz z hz).trans (hh z)⟩

#print axioms original_full_face_budget

private theorem whole_budget_transport {p : pure C u}
    (a b : ExclusionChart C u p) (A B : ℝ)
    (ha : ∀ h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ,
      (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
      ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ A * u x) ∧
        ∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z)
    (hb : ∀ h : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ,
      (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
      ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ B * u x) ∧
        ∀ z, ‖z‖ ≤ 1 → g (b.param z) = h z) :
    ∀ h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ,
      (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
      ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ B * u x) ∧
        ∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z := by
  intro h hh
  obtain ⟨f, _, hf⟩ := ha h hh
  let j := f.toAffineMap.comp b.param
  have hj (z) (hz : ‖z‖ ≤ 1) : 0 ≤ j z ∧ j z ≤ 1 := by
    obtain ⟨w, hw, heq⟩ := a.whole.symm ▸ SingleLabelNormalBody.chart_mem b hz
    have hw' : ‖w‖ ≤ 1 := by simpa using hw
    change 0 ≤ f (b.param z) ∧ f (b.param z) ≤ 1
    rw [← heq, hf w hw']
    exact hh w hw'
  obtain ⟨g, hg, hgj⟩ := hb j hj
  refine ⟨g, hg, ?_⟩
  intro z hz
  obtain ⟨w, hw, heq⟩ := b.whole.symm ▸ SingleLabelNormalBody.chart_mem a hz
  have hw' : ‖w‖ ≤ 1 := by simpa using hw
  calc
    g (a.param z) = g (b.param w) := congrArg g heq.symm
    _ = f (b.param w) := hgj w hw'
    _ = h z := by rw [heq, hf z hz]

/-- The common scale and the actual optimal budget are independent of every
choice of coordinates for this same full original exclusion. -/
theorem original_chart_independence
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (p : pure C u) (a b : ExclusionChart C u p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
      (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 →
        extensionBudget a v = 1 / (2 * t)) ∧
      (∀ v : EuclideanSpace ℝ (Fin b.dim), ‖v‖ = 1 →
        extensionBudget b v = 1 / (2 * t)) := by
  obtain ⟨ta, hta, htah, hda, hla, hma⟩ := original_full_face_budget hc hs hg hB hPR p a
  obtain ⟨tb, htb, htbh, hdb, hlb, hmb⟩ := original_full_face_budget hc hs hg hB hPR p b
  have hfa : ∀ h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ,
      (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
      ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ (1 / (2 * ta)) * u x) ∧
        ∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z := by
    intro h hh
    obtain ⟨g, hg0, hgz, hg1⟩ := hla h (fun z hz => (hh z hz).1)
    exact ⟨g, fun x hx => ⟨hg0 x hx, hg1 (fun z hz => (hh z hz).2) x hx⟩, hgz⟩
  have hfb : ∀ h : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ,
      (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
      ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ (1 / (2 * tb)) * u x) ∧
        ∀ z, ‖z‖ ≤ 1 → g (b.param z) = h z := by
    intro h hh
    obtain ⟨g, hg0, hgz, hg1⟩ := hlb h (fun z hz => (hh z hz).1)
    exact ⟨g, fun x hx => ⟨hg0 x hx, hg1 (fun z hz => (hh z hz).2) x hx⟩, hgz⟩
  have heq : 1 / (2 * ta) = 1 / (2 * tb) := le_antisymm
    (hma _ (whole_budget_transport a b _ _ hfa hfb))
    (hmb _ (whole_budget_transport b a _ _ hfb hfa))
  exact ⟨ta, hta, htah, fun v hv => (hda v hv).2.2,
    fun v hv => ((hdb v hv).2.2).trans heq.symm⟩

#print axioms original_chart_independence

/-- A single intrinsic scale works in every chart of the same full original
exclusion, on all mixed inputs, with the actual attained sharp budget. -/
theorem original_common_chart_scale
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s)
    (p : pure C u) (a : ExclusionChart C u p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
      ∀ b : ExclusionChart C u p, ∀ v : EuclideanSpace ℝ (Fin b.dim), ‖v‖ = 1 →
      (BudgetFeasible b v (1 / (2*t)) ∧
        (∀ M, BudgetFeasible b v M → 1 / (2*t) ≤ M) ∧
        extensionBudget b v = 1 / (2*t)) ∧
      ∀ q : pure C u, b.param v = q → ∃ e : V →ₗ[ℝ] ℝ,
        confirms C u q e ∧ (∀ z, e (b.param z) = 1-t+t*⟪v,z⟫) ∧
        ∀ z, ‖z‖ ≤ 1 → comparison C u q (b.param z) = 1-t+t*⟪v,z⟫ := by
  obtain ⟨t, ht, hth, _, hba⟩ := original_scale_and_sharp_budget hc hs hg hB hPR p a
  refine ⟨t, ht, hth, ?_⟩
  intro b v hv
  obtain ⟨tb, htb, _, hsb, hbb⟩ := original_scale_and_sharp_budget hc hs hg hB hPR p b
  obtain ⟨t0, _, _, hca, hcb⟩ := original_chart_independence hc hs hg hB hPR p a b
  letI : Nonempty (Fin a.dim) := ⟨⟨0, a.dim_pos⟩⟩
  obtain ⟨v0, hv0⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin a.dim)) (by norm_num : (0 : ℝ) ≤ 1)
  have heqB : 1 / (2*tb) = 1 / (2*t) := calc
    _ = extensionBudget b v := (hbb v hv).2.2.symm
    _ = 1 / (2*t0) := hcb v hv
    _ = extensionBudget a v0 := (hca v0 hv0).symm
    _ = 1 / (2*t) := (hba v0 hv0).2.2
  have heq : tb = t := by
    have hh := (div_eq_div_iff (by positivity : 2*tb ≠ 0) (by positivity : 2*t ≠ 0)).mp heqB
    nlinarith
  subst tb
  exact ⟨hbb v hv, hsb v hv⟩

#print axioms original_common_chart_scale

end D5.S3.Quantum.Foundation.OriginalBallScale

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

end D5.S3.Quantum.Foundation.OriginalComparisonTopology
