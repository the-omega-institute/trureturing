/- GID: D5/S3/Quantum/Foundation/OriginalNormalFamily
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalNormalFamily
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Support thresholds and whole original edge intervals in the singleton normal family. -/

import D5.S3.Quantum.Foundation.OriginalRegularHeight

/-! All normal forms belong to the original dual of the original cone.
Positivity and the proper upper bound are separate conclusions. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalNormalFamily
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open WholePairBallConfirmation OriginalFacePolarity FixedZeroObstruction
open SingleLabelNormalBody OriginalRegularHeight

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

private theorem span_vanishes {p : pure C u} (f : normalSpan C p) : f.val p = 0 := by
  let Z : Submodule ℝ (V →L[ℝ] ℝ) :=
    { carrier := {h | h p = 0}
      zero_mem' := by simp
      add_mem' := by intro f g hf hg; change f p + g p = 0; rw [hf, hg]; ring
      smul_mem' := by intro t f hf; change t * f p = 0; rw [hf]; ring }
  have hsub : normalSpan C p ≤ Z := Submodule.span_le.mpr (fun _ hf => hf.2)
  exact hsub f.property

private theorem g_chart {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (hep : ep ∈ fullZeroConfirmers C u p)
    (k : Coordinates p a ep) (z : chartSpace a) : k.g.val (a.param z) = 1 := by
  have hspan : affineSpan ℝ (Metric.closedBall (0 : chartSpace a) 1) = ⊤ := by
    apply (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
    exact ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
  have hz : ep.toAffineMap.comp a.param = AffineMap.const ℝ _ 0 :=
    AffineMap.ext_on hspan (fun w hw => hep.2 _ (a.whole ▸ mem_image_of_mem a.param hw))
  have hz' := congrArg (fun f : chartSpace a →ᵃ[ℝ] ℝ => f z) hz
  rw [k.g_value]
  change u (a.param z) - ep (a.param z) = 1
  change ep (a.param z) = 0 at hz'
  rw [chart_unit a, hz']; ring

/-- The actual inverse-restriction normal form on all of V. -/
def normalForm {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (k : Coordinates p a ep) (α : ℝ) (v : chartSpace a) : V →ₗ[ℝ] ℝ :=
  α • k.g.val.toLinearMap + (directionLift k v).val.toLinearMap

private theorem normalForm_chart {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (hep : ep ∈ fullZeroConfirmers C u p)
    (k : Coordinates p a ep) (α : ℝ) (v z : chartSpace a) :
    normalForm k α v (a.param z) = α + ⟪v, z⟫ := by
  change α * k.g.val (a.param z) + (directionLift k v).val (a.param z) = _
  rw [g_chart hep k, directionLift_value]; ring

/-- The support threshold takes its supremum over every original non-anchor mixed state. -/
def rho {p : pure C u} {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (k : Coordinates p a ep) (v : chartSpace a) : ℝ :=
  sSup ((fun x : V => -(directionLift k v).val x / k.g.val x) '' (base C u \ {(p : V)}))

private theorem ball_ne_anchor {p : pure C u} {a : ExclusionChart C u p}
    {z : chartSpace a} (hz : ‖z‖ ≤ 1) : a.param z ≠ (p : V) := by
  intro he
  obtain ⟨f, hf, hf0⟩ := (he ▸ SingleLabelNormalBody.chart_mem a hz).2
  linarith [hf.2]

private theorem ratio_bound {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (k : Coordinates p a ep)
    (v : chartSpace a) (hv : ‖v‖ = 1) :
    BddAbove ((fun x : V => -(directionLift k v).val x / k.g.val x) ''
      (base C u \ {(p : V)})) := by
  obtain ⟨M, hM, hdom⟩ := direction_domination k
  refine ⟨M, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hg0 := (interior_subset k.g_interior).1 x hx.1.1
  by_cases hg : k.g.val x = 0
  · simp [hg, show (0 : ℝ) ≤ M by linarith]
  · have hgpos : 0 < k.g.val x := lt_of_le_of_ne hg0 (Ne.symm hg)
    apply (div_le_iff₀ hgpos).mpr
    exact (neg_le_abs _).trans (hdom v hv x hx.1.1)

/-- On unit directions rho is finite, at least one, and exactly pays whole-cone positivity. -/
theorem rho_positive_iff
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q))
    (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (v : chartSpace a) (hv : ‖v‖ = 1) :
    1 ≤ rho k v ∧ ∀ α : ℝ,
      (∀ x ∈ C, 0 ≤ normalForm k α v x) ↔ rho k v ≤ α := by
  have hne : ((fun x : V => -(directionLift k v).val x / k.g.val x) ''
      (base C u \ {(p : V)})).Nonempty := by
    exact ⟨_, a.param (-v), ⟨(SingleLabelNormalBody.chart_mem a (by simpa using hv.le)).1,
      ball_ne_anchor (by simpa using hv.le)⟩, rfl⟩
  have hbound := ratio_bound k v hv
  have hpos (x : V) (hx : x ∈ base C u) (hxp : x ≠ p) : 0 < k.g.val x := by
    rw [k.g_value]
    exact g_positive hc hs hg hB hInj p hep hx hxp
  have hrho : 1 ≤ rho k v := by
    have hh := le_csSup hbound (mem_image_of_mem
      (fun x : V => -(directionLift k v).val x / k.g.val x)
      (show a.param (-v) ∈ base C u \ {(p : V)} from
        ⟨(SingleLabelNormalBody.chart_mem a (by simpa using hv.le)).1,
          ball_ne_anchor (by simpa using hv.le)⟩))
    simpa [rho, directionLift_value, g_chart hep k, inner_neg_right,
      real_inner_self_eq_norm_sq, hv] using hh
  refine ⟨hrho, ?_⟩
  intro α
  constructor
  · intro hnon
    apply csSup_le hne
    rintro _ ⟨x, hx, rfl⟩
    apply (div_le_iff₀ (hpos x hx.1 hx.2)).mpr
    have hh := hnon x hx.1.1
    change 0 ≤ α * k.g.val x + (directionLift k v).val x at hh
    linarith
  · intro hα
    apply nonneg_on_cone (base_compact hc hs) hs
    intro s
    by_cases hsp : (s : V) = p
    · change 0 ≤ α * k.g.val s + (directionLift k v).val s
      rw [hsp, span_vanishes k.g, span_vanishes (directionLift k v)]; simp
    · have hh := (le_csSup hbound (mem_image_of_mem
        (fun x : V => -(directionLift k v).val x / k.g.val x)
        (show (s : V) ∈ base C u \ {(p : V)} from ⟨pure_mem s, hsp⟩))).trans hα
      have hmul := (div_le_iff₀ (hpos s (pure_mem s) hsp)).mp hh
      change 0 ≤ α * k.g.val s + (directionLift k v).val s
      linarith

/-- Once positivity is established, the original whole-base maximum is alpha+norm(v). -/
theorem normal_maximum
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (α : ℝ) (v : chartSpace a) (hpos : ∀ x ∈ C, 0 ≤ normalForm k α v x) :
    (∀ x ∈ base C u, normalForm k α v x ≤ α + ‖v‖) ∧
      ∃ x ∈ exclusion C u p, normalForm k α v x = α + ‖v‖ := by
  have hupper : ∀ x ∈ base C u, normalForm k α v x ≤ α + ‖v‖ := by
    by_cases hn : normalForm k α v = 0
    · intro x hx
      have hα : 0 ≤ α := by
        have hh := hpos (a.param 0) (SingleLabelNormalBody.chart_mem a (by simp)).1.1
        simpa [normalForm_chart hep k] using hh
      rw [hn]; simp only [LinearMap.zero_apply]; positivity
    · obtain ⟨s, hsD, _, hmax⟩ := positive_annihilator_maximum hc hs hg p
        (normalForm k α v) hn hpos (by
          change α * k.g.val p + (directionLift k v).val p = 0
          rw [span_vanishes k.g, span_vanishes (directionLift k v)]; ring)
      obtain ⟨z, hz, hzs⟩ := a.whole.symm ▸ hsD
      intro x hx
      apply (hmax x hx).trans
      rw [← hzs, normalForm_chart hep k]
      have hz1 : ‖z‖ ≤ 1 := by simpa using hz
      exact add_le_add_left ((real_inner_le_norm v z).trans
        (by nlinarith [norm_nonneg v])) α
  refine ⟨hupper, ?_⟩
  by_cases hv : v = 0
  · refine ⟨a.param 0, SingleLabelNormalBody.chart_mem a (by simp), ?_⟩
    simp [normalForm_chart hep k, hv]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨a.param (‖v‖⁻¹ • v), SingleLabelNormalBody.chart_mem a ?_, ?_⟩
    · simp [norm_smul, hvpos.ne']
    · rw [normalForm_chart hep k, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp

end D5.S3.Quantum.Foundation.OriginalNormalFamily
