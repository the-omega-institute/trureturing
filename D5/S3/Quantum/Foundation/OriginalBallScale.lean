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
  have her := he.1 _ (SingleLabelNormalBody.chart_mem a (by simpa using hv.le)).1.1
  rw [chart_unit a] at her
  have ht : 0 ≤ t ∧ t ≤ 1 / 2 := by dsimp [t]; constructor <;> linarith
  have hform := peak_formula a e.toLinearMap he.1 v hv (hq ▸ he.2)
  refine ⟨t, e.toLinearMap, ht.1, ht.2, ⟨he.1, he.2⟩, ?_, ?_⟩
  · intro z
    simpa [t] using hform z
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
          (hg.1 _ (SingleLabelNormalBody.chart_mem a (by simpa using hv.le)).1.1).1⟩
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
      have hz : v₀ = 0 := neg_eq_self.mp hh
      simp [hz] at hv₀
    have hlow : 0 < h (a.param (-v₀)) := by
      apply lt_of_le_of_ne (hh _ hr.1.1).1
      intro hz
      exact hne (hzero ▸ (show a.param (-v₀) ∈ {y | y ∈ base C u ∧ h y = 0} from ⟨hr.1, hz.symm⟩))
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
      nlinarith
  exact ⟨e, he, heq ▸ hform, heq ▸ hcomp⟩

end D5.S3.Quantum.Foundation.OriginalBallScale
