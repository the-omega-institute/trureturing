/- GID: D5/S3/Quantum/Foundation/RegularAnchorNormalChart
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/RegularAnchorNormalChart
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original regular anchors determine a bounded full normal coordinate chart. -/

import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Quantum.Foundation.CommonPositiveExtension

/-! Normal coordinates retain the entire original cone, base and effect interval.
Regularity means uniqueness in the original common-confirmation family. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.RegularAnchorNormalChart

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OrthogonalJointCompletion CommonPositiveExtension SingleLabelNormalBody

abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- An affine chart of the entire original exclusion by the closed three-ball. -/
structure FullBall3Chart (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : V) where
  param : ThreeSpace →ᵃ[ℝ] V
  injective : Function.Injective param
  whole : param '' Metric.closedBall 0 1 = exclusion C u p

/-- The full three-ball hypothesis, for every original pure label. -/
def EB3 (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p : pure C u, Nonempty (FullBall3Chart C u p)

/-- The same chart in the existing native chart carrier. -/
def FullBall3Chart.native {p : V} (a : FullBall3Chart C u p) : ExclusionChart C u p :=
  ⟨3, by decide, a.param, a.injective, a.whole⟩

/-- The original regular-anchor condition is uniqueness of the full family A_p. -/
def Regular (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : V) : Prop :=
  ∃! e : V →ₗ[ℝ] ℝ, common C u p e

/-- Signed span of the entire original positive annihilator cone. -/
abbrev NormalSpan (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : V) :=
  Submodule.span ℝ (zeroPositive C u p)

private theorem comparison_zero (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (p : pure C u)
    {x : V} (hx : x ∈ base C u) :
    comparison C u p x = 0 ↔ x ∈ exclusion C u p := by
  constructor
  · intro hz
    obtain ⟨f, hf, he⟩ := comparison_attained hs hg p x
    exact ⟨hx, f, hf, he.trans hz⟩
  · rintro ⟨_, f, hf, hfz⟩
    apply le_antisymm
    · exact (csInf_le ⟨0, by rintro r ⟨e, he, rfl⟩; exact (he.1 x hx.1).1⟩
        ⟨f, hf, rfl⟩).trans_eq hfz
    · apply le_csInf ⟨f x, f, hf, rfl⟩
      rintro r ⟨e, he, rfl⟩
      exact (he.1 x hx.1).1

private theorem complement_normal {p : pure C u} {e : V →ₗ[ℝ] ℝ}
    (he : common C u p e) : u - e ∈ zeroPositive C u p := by
  refine ⟨fun x hx => sub_nonneg.mpr (he.1.1 x hx).2, ?_⟩
  simp [LinearMap.sub_apply, (pure_mem p).2, he.1.2]

private theorem complement_chart {p : pure C u} {e : V →ₗ[ℝ] ℝ}
    (he : common C u p e) (a : ExclusionChart C u p) (w) :
    (u - e) (a.param w) = 1 := by
  have hball : affineSpan ℝ (Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin a.dim)) 1) = ⊤ :=
    (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
      ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
  have heq : (u - e).toAffineMap.comp a.param = AffineMap.const ℝ _ (1 : ℝ) := by
    apply AffineMap.ext_on hball
    intro z hz
    have hx := chart_mem a (by simpa using hz)
    change u (a.param z) - e (a.param z) = 1
    rw [hx.1.2, he.2 _ hx]
    ring
  exact congrArg (fun f => f w) heq

private theorem constant_normal
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (p : pure C u) (a : ExclusionChart C u p)
    (e : V →ₗ[ℝ] ℝ) (he : common C u p e)
    (huniq : ∀ f, common C u p f → f = e)
    (f : V →ₗ[ℝ] ℝ) (hf : f ∈ zeroPositive C u p)
    (hzero : slope a f.toContinuousLinearMap = 0) :
    f = f (a.param 0) • (u - e) := by
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨q, hq, hqpos, hmax⟩ := positive_annihilator_maximum hc hs hg p f hf0 hf.1 hf.2
  obtain ⟨w, hw, hwq⟩ := a.whole.symm ▸ hq
  have hformula (z) : f (a.param z) = f (a.param 0) := by
    simpa [hzero] using slope_formula a f.toContinuousLinearMap z
  have hqc : f q = f (a.param 0) := by rw [← hwq, hformula]
  have hpos : 0 < f (a.param 0) := hqc ▸ hqpos
  let b : V →ₗ[ℝ] ℝ := (f (a.param 0))⁻¹ • f
  have hb : proper C u b := cone_bound (base_compact hc hs) hs (fun r => by
    change 0 ≤ (f (a.param 0))⁻¹ * f r ∧ (f (a.param 0))⁻¹ * f r ≤ 1
    refine ⟨mul_nonneg (inv_nonneg.mpr hpos.le) (hf.1 r (pure_mem r).1), ?_⟩
    rw [← div_eq_inv_mul, div_le_one hpos]
    exact (hmax r (pure_mem r)).trans_eq hqc)
  have hcommon : common C u p (u - b) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x hx
      have hh := hb x hx
      change 0 ≤ u x - b x ∧ u x - b x ≤ u x
      constructor <;> linarith
    · simp [b, LinearMap.sub_apply, (pure_mem p).2, hf.2]
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := a.whole.symm ▸ hx
      change u (a.param z) - (f (a.param 0))⁻¹ * f (a.param z) = 0
      rw [(chart_mem a (by simpa using hz)).1.2, hformula, inv_mul_cancel₀ hpos.ne']
      ring
  have heq := huniq _ hcommon
  ext x
  have hh := LinearMap.congr_fun heq x
  change u x - (f (a.param 0))⁻¹ * f x = e x at hh
  change f x = f (a.param 0) * (u x - e x)
  field_simp at hh
  nlinarith

/-- Constant and slope of restriction to the actual full native chart. -/
def coordinates {p : V} (a : ExclusionChart C u p) :
    (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin a.dim)) where
  toFun f := (f (a.param 0), slope a f.toContinuousLinearMap)
  map_add' f g := by
    apply Prod.ext
    · rfl
    · exact (slope a).map_add _ _
  map_smul' t f := by
    apply Prod.ext
    · rfl
    · exact (slope a).map_smul t _

private theorem complement_coordinates {p : pure C u} {e : V →ₗ[ℝ] ℝ}
    (he : common C u p e) (a : ExclusionChart C u p) :
    coordinates a (u - e) = (1, 0) := by
  apply Prod.ext
  · exact complement_chart he a 0
  · apply ext_inner_right ℝ
    intro z
    have hh := slope_formula a (u - e).toContinuousLinearMap z
    rw [complement_chart he a z, complement_chart he a 0] at hh
    simpa using hh.symm

private theorem positive_coordinates_injective
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p) (a : ExclusionChart C u p)
    (e : V →ₗ[ℝ] ℝ) (he : common C u p e)
    (huniq : ∀ f, common C u p f → f = e) :
    Set.InjOn (coordinates a) (zeroPositive C u p) := by
  intro f hf k hk heq
  obtain ⟨r, hr, _, hball⟩ := slope_body_inradius hc hs hg hB p hp a
  let v := slope a f.toContinuousLinearMap
  let t := r / (1 + ‖v‖)
  have ht : 0 < t := div_pos hr (by positivity)
  have hnorm : ‖-t • v‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos ht)]
    change t * ‖v‖ ≤ r
    dsimp [t]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1 + ‖v‖)]
    nlinarith
  obtain ⟨b, hb, hbv⟩ := hball (by simpa using hnorm)
  let d : V →ₗ[ℝ] ℝ := t⁻¹ • b.toLinearMap
  have hd : d ∈ zeroPositive C u p :=
    ⟨fun x hx => mul_nonneg (inv_nonneg.mpr ht.le) (hb.1 x hx), by simp [d, hb.2.1]⟩
  have hfadd : f + d ∈ zeroPositive C u p :=
    ⟨fun x hx => add_nonneg (hf.1 x hx) (hd.1 x hx), by simp [hf.2, hd.2]⟩
  have hkadd : k + d ∈ zeroPositive C u p :=
    ⟨fun x hx => add_nonneg (hk.1 x hx) (hd.1 x hx), by simp [hk.2, hd.2]⟩
  have hfslope : slope a (f + d).toContinuousLinearMap = 0 := by
    change slope a (f.toContinuousLinearMap + t⁻¹ • b) = 0
    rw [map_add, map_smul, hbv, smul_smul]
    change v + (t⁻¹ * -t) • v = 0
    simp [ht.ne']
  have hkslope : slope a (k + d).toContinuousLinearMap = 0 := by
    have hv := congrArg Prod.snd heq
    change slope a f.toContinuousLinearMap = slope a k.toContinuousLinearMap at hv
    change slope a (k.toContinuousLinearMap + t⁻¹ • b) = 0
    rw [map_add, ← hv]
    exact hfslope
  have hfconst := constant_normal hc hs hg p a e he huniq (f + d) hfadd hfslope
  have hkconst := constant_normal hc hs hg p a e he huniq (k + d) hkadd hkslope
  have hcenter := congrArg Prod.fst heq
  change f (a.param 0) = k (a.param 0) at hcenter
  apply add_right_cancel (b := d)
  rw [hfconst, hkconst]
  simp only [LinearMap.add_apply, hcenter]

end D5.S3.Quantum.Foundation.RegularAnchorNormalChart
