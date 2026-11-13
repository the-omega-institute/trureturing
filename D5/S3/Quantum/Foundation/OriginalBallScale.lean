/- GID: D5/S3/Quantum/Foundation/OriginalBallScale
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalBallScale
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The original pure reciprocity law fixes one positive scale on every whole exclusion ball. -/

import D5.S3.Quantum.Foundation.OriginalRegularHeight
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import D5.S3.Quantum.Foundation.ReciprocalEndpointExposure

/-! Common scale and optimal positive-extension budgets on the original whole ball. -/

noncomputable section
open Set
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

end D5.S3.Quantum.Foundation.OriginalBallScale
