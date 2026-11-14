/- GID: D5/S3/Quantum/Foundation/OriginalNormalFamily
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalNormalFamily
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original scale support, whole-cone normal positivity and complete edge intervals. -/

import D5.S3.Quantum.Foundation.OriginalRegularHeight
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
import D5.S3.Quantum.Foundation.CommonOldExclusionConfirmation

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
      have hvz : ‖v‖ * ‖z‖ ≤ ‖v‖ := mul_le_of_le_one_right (norm_nonneg v) hz1
      exact add_le_add le_rfl ((real_inner_le_norm v z).trans hvz)
  refine ⟨hupper, ?_⟩
  by_cases hv : v = 0
  · refine ⟨a.param 0, SingleLabelNormalBody.chart_mem a (by simp), ?_⟩
    simp [normalForm_chart hep k, hv]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨a.param (‖v‖⁻¹ • v), SingleLabelNormalBody.chart_mem a ?_, ?_⟩
    · simp [norm_smul, hvpos.ne']
    · rw [normalForm_chart hep k, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp

/-- The original neighboring full confirmer, its exact support threshold and antipode.
The neighbor is proved singleton before its normal coordinates can be reused. -/
theorem original_neighbor_support
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q))
    (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q) :
    ∃ eq : V →ₗ[ℝ] ℝ,
      (∀ e, e ∈ fullZeroConfirmers C u q ↔ e = eq) ∧
      let lam := 1 / (1 + rho k v)
      0 < lam ∧ lam ≤ 1 / 2 ∧
      (∀ x : V, eq x = (1 - lam) * k.g.val x + lam * (directionLift k v).val x) ∧
      eq (a.param (-v)) = (rho k v - 1) / (rho k v + 1) ∧
      ((a.param (-v) ∈ exclusion C u q) ↔ rho k v = 1) := by
  obtain ⟨eq, hqunique⟩ := neighbor_unique hc hs hg hB hInj p hep k q v hv hq
  have heq : eq ∈ fullZeroConfirmers C u q := (hqunique eq).mpr rfl
  let lam := (1 - eq (a.param (-v))) / 2
  have hqD : (q : V) ∈ exclusion C u p := hq ▸ SingleLabelNormalBody.chart_mem a hv.le
  have hpD := (exclusion_symmetric p q).mp hqD
  have hEq := peak_lift hep k eq heq.1.1 (heq.2 _ hpD) v hv (hq ▸ heq.1.2)
  have hform (x : V) : eq x = (1 - lam) * k.g.val x + lam * (directionLift k v).val x := by
    have hh := congrArg (fun f : V →L[ℝ] ℝ => f x) hEq
    change eq x = k.g.val x + lam * ((directionLift k v).val x - k.g.val x) at hh
    linarith
  obtain ⟨M, hM, hdom⟩ := direction_domination k
  have hlower := neighbor_parameter_bound hc hs hg hB hInj p hep k M hM hdom q v hv hq eq heq
  have hlam : 0 < lam := lt_of_lt_of_le (by positivity : 0 < 1 / (1 + M)) hlower
  have hlamhalf : lam ≤ 1 / 2 := by
    have hh := (heq.1.1 _ (SingleLabelNormalBody.chart_mem a (z := -v)
      (by simpa using hv.le)).1.1).1
    dsimp [lam]; linarith
  obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := pure_pair_in_ball hc hs hg hB q
  have hex : ∃ y : pure C u, (y : V) ∈ exclusion C u q ∧ y ≠ p := by
    by_cases h : y₁ = p
    · exact ⟨y₂, hy₂, fun hh => hne (h.trans hh.symm)⟩
    · exact ⟨y₁, hy₁, h⟩
  obtain ⟨y, hy, hyp⟩ := hex
  have hgy : 0 < k.g.val y := by
    rw [k.g_value]
    exact g_positive hc hs hg hB hInj p hep (pure_mem y)
      (fun h => hyp (Subtype.val_injective h))
  let A := (1 - lam) / lam
  have hA : lam * A = 1 - lam := by dsimp [A]; field_simp
  have hratio : -(directionLift k v).val y / k.g.val y = A := by
    apply (div_eq_iff hgy.ne').mpr
    have hh := hform y
    rw [heq.2 _ hy] at hh
    nlinarith
  have hneSet : ((fun x : V => -(directionLift k v).val x / k.g.val x) '' (base C u \ {(p : V)})).Nonempty := by
    exact ⟨_, y, ⟨pure_mem y, fun h => hyp (Subtype.val_injective h)⟩, rfl⟩
  have hrho : rho k v = A := by
    apply le_antisymm
    · apply csSup_le hneSet
      rintro _ ⟨x, hx, rfl⟩
      have hgx : 0 < k.g.val x := by
        rw [k.g_value]
        exact g_positive hc hs hg hB hInj p hep hx.1 hx.2
      apply (div_le_iff₀ hgx).mpr
      have heqx := (heq.1.1 x hx.1.1).1
      rw [hform x] at heqx
      nlinarith
    · rw [← hratio]
      exact le_csSup (ratio_bound k v hv) ⟨y,
        ⟨pure_mem y, fun h => hyp (Subtype.val_injective h)⟩, rfl⟩
  have hApos : 0 < A := div_pos (by linarith) hlam
  have hlamrho : lam = 1 / (1 + rho k v) := by
    rw [hrho]
    apply (eq_div_iff (by positivity : 1 + A ≠ 0)).mpr
    nlinarith
  have hr : eq (a.param (-v)) = 1 - 2 * lam := by dsimp [lam]; ring
  have hrhof := (rho_positive_iff hc hs hg hB hInj p hep k v hv).1
  refine ⟨eq, hqunique, ?_⟩
  dsimp only
  refine ⟨hlamrho ▸ hlam, hlamrho ▸ hlamhalf, hlamrho ▸ hform, ?_, ?_⟩
  · rw [hr, hlamrho]
    field_simp
    <;> ring
  · constructor
    · intro hD
      have hz := heq.2 _ hD
      rw [hr, hlamrho] at hz
      have hd : 0 < 1 + rho k v := by linarith
      have hm := (div_eq_iff hd.ne').mp (show 1 / (1 + rho k v) = 1 / 2 by linarith)
      linarith
    · intro hrho1
      refine ⟨(SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1,
        eq, heq.1, ?_⟩
      rw [hr, hlamrho, hrho1]
      norm_num

private def coordinateEval {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (k : Coordinates p a ep) (x : V) : chartSpace a →ₗ[ℝ] ℝ where
  toFun v := (directionLift k v).val x
  map_add' v w := by simp
  map_smul' t v := by simp

/-- The actual original linear map H, reconstructed from the inverse restriction. -/
def coordinateMap {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (k : Coordinates p a ep) : V →ₗ[ℝ] chartSpace a where
  toFun x := (InnerProductSpace.toDual ℝ (chartSpace a)).symm (coordinateEval k x).toContinuousLinearMap
  map_add' x y := by
    apply (InnerProductSpace.toDual ℝ (chartSpace a)).injective
    ext v
    simp [coordinateEval]
  map_smul' t x := by
    apply (InnerProductSpace.toDual ℝ (chartSpace a)).injective
    ext v
    simp [coordinateEval]

private theorem coordinateMap_inner {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (k : Coordinates p a ep) (v : chartSpace a) (x : V) :
    ⟪v, coordinateMap k x⟫ = (directionLift k v).val x := by
  rw [show ⟪v, coordinateMap k x⟫ = ⟪coordinateMap k x, v⟫ from real_inner_comm _ _]
  exact InnerProductSpace.toDual_symm_apply

/-- Coordinate reconstruction is on every point of the entire affine chart and on p. -/
theorem original_coordinate_map {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (k : Coordinates p a ep) :
    coordinateMap k p = 0 ∧
    (∀ z : chartSpace a, coordinateMap k (a.param z) = z) ∧
    (∀ v : chartSpace a, ∃ f : normalSpan C p,
      ∀ x : V, ⟪v, coordinateMap k x⟫ = f.val x) ∧
    ∀ H : V →ₗ[ℝ] chartSpace a,
      (∀ v : chartSpace a, ∃ f : normalSpan C p, ∀ x : V, ⟪v, H x⟫ = f.val x) →
      (∀ z : chartSpace a, H (a.param z) = z) → H = coordinateMap k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ext_inner_left ℝ
    intro v
    rw [coordinateMap_inner, span_vanishes (directionLift k v), inner_zero_right]
  · intro z
    apply ext_inner_left ℝ
    intro v
    rw [coordinateMap_inner, directionLift_value]
  · intro v
    exact ⟨directionLift k v, coordinateMap_inner k v⟩
  · intro H hH hchart
    apply LinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro v
    obtain ⟨f, hf⟩ := hH v
    have hfd : f = directionLift k v := by
      apply k.equivalence.injective
      ext z
      rw [k.restriction, k.restriction, directionLift_value, ← hf (a.param z), hchart z]
    rw [hf x, hfd, coordinateMap_inner]

/-- The whole original edge consists of the full interval of original functionals.
The interval parameter is an actual convex coefficient, on all of V. -/
theorem original_whole_edge
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q))
    (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q) :
    ∃ eq : V →ₗ[ℝ] ℝ, (∀ e, e ∈ fullZeroConfirmers C u q ↔ e = eq) ∧
      ∀ b : V →ₗ[ℝ] ℝ, (proper C u b ∧ b p = 0 ∧ b q = 1) ↔
        ∃ s : ℝ, s ∈ Icc (0 : ℝ) 1 ∧ b = (1 - s) • (u - ep) + s • eq := by
  obtain ⟨eq, hqunique, hlam, hlamhalf, heqform, hanti, horth⟩ :=
    original_neighbor_support hc hs hg hB hInj p hep k q v hv hq
  have heq : eq ∈ fullZeroConfirmers C u q := (hqunique eq).mpr rfl
  have hqD : (q : V) ∈ exclusion C u p := hq ▸ SingleLabelNormalBody.chart_mem a hv.le
  have hpD := (exclusion_symmetric p q).mp hqD
  let L := 1 / (1 + rho k v)
  have hL : 0 < L := hlam
  have hG : proper C u (u - ep) := by
    intro x hx
    have hh := hep.1.1 x hx
    constructor <;> change _ ≤ _ <;> simp only [LinearMap.sub_apply] <;> linarith
  obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := pure_pair_in_ball hc hs hg hB q
  have hex : ∃ y : pure C u, (y : V) ∈ exclusion C u q ∧ y ≠ p := by
    by_cases h : y₁ = p
    · exact ⟨y₂, hy₂, fun hh => hne (h.trans hh.symm)⟩
    · exact ⟨y₁, hy₁, h⟩
  obtain ⟨y, hy, hyp⟩ := hex
  have hgy : 0 < k.g.val y := by
    rw [k.g_value]
    exact g_positive hc hs hg hB hInj p hep (pure_mem y)
      (fun h => hyp (Subtype.val_injective h))
  refine ⟨eq, hqunique, ?_⟩
  intro b
  constructor
  · rintro ⟨hb, hbp, hbq⟩
    let μ := (1 - b (a.param (-v))) / 2
    have hμ : 0 ≤ μ := by
      have hh := (hb _ (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1.1).2
      rw [chart_unit a] at hh
      dsimp [μ]; linarith
    have hbform := peak_lift hep k b hb hbp v hv (hq ▸ hbq)
    have hby := congrArg (fun f : V →L[ℝ] ℝ => f y) hbform
    change b y = k.g.val y + μ * ((directionLift k v).val y - k.g.val y) at hby
    have heqy := heqform y
    rw [heq.2 _ hy] at heqy
    have hby0 := (hb y (pure_mem y).1).1
    have hμL : μ ≤ L := by
      change 0 = (1 - L) * k.g.val y + L * (directionLift k v).val y at heqy
      nlinarith
    refine ⟨μ / L, ⟨div_nonneg hμ hL.le, (div_le_one hL).mpr hμL⟩, ?_⟩
    ext x
    have hh := congrArg (fun f : V →L[ℝ] ℝ => f x) hbform
    change b x = k.g.val x + μ * ((directionLift k v).val x - k.g.val x) at hh
    change b x = (1 - μ / L) * (u x - ep x) + (μ / L) * eq x
    rw [heqform x]
    have hgx : u x - ep x = k.g.val x := by rw [k.g_value]; rfl
    rw [hgx, hh]
    change _ = (1 - μ / L) * k.g.val x + (μ / L) *
      ((1 - L) * k.g.val x + L * (directionLift k v).val x)
    field_simp
    <;> ring
  · rintro ⟨s, hs', rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hgx := hG x hx
      change 0 ≤ u x - ep x ∧ u x - ep x ≤ u x at hgx
      have heqx := heq.1.1 x hx
      change 0 ≤ (1 - s) * (u x - ep x) + s * eq x ∧
        (1 - s) * (u x - ep x) + s * eq x ≤ u x
      constructor
      · exact add_nonneg (mul_nonneg (by linarith [hs'.2]) hgx.1) (mul_nonneg hs'.1 heqx.1)
      · nlinarith [mul_le_mul_of_nonneg_left hgx.2 (show 0 ≤ 1 - s by linarith [hs'.2]),
          mul_le_mul_of_nonneg_left heqx.2 hs'.1]
    · simp [hep.1.2, heq.2 _ hpD, (pure_mem p).2]
    · simp [hep.2 _ hqD, heq.1.2, (pure_mem q).2]

#print axioms original_whole_edge

/-- The complete fixed edge J(p,q), obtained by complementation on all of V. -/
theorem original_fixed_edge
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q))
    (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q) :
    ∃ eq : V →ₗ[ℝ] ℝ, (∀ e, e ∈ fullZeroConfirmers C u q ↔ e = eq) ∧
      ∀ e : V →ₗ[ℝ] ℝ, (proper C u e ∧ e p = 1 ∧ e q = 0) ↔
        ∃ s : ℝ, s ∈ Icc (0 : ℝ) 1 ∧ e = (1-s) • ep + s • (u-eq) := by
  obtain ⟨eq, huniq, hedge⟩ := original_whole_edge hc hs hg hB hInj p hep k q v hv hq
  have hcompl (f : V →ₗ[ℝ] ℝ) (hf : proper C u f) : proper C u (u-f) := by
    intro x hx
    have hh := hf x hx
    constructor <;> simp only [LinearMap.sub_apply] <;> linarith
  refine ⟨eq, huniq, ?_⟩
  intro e
  constructor
  · rintro ⟨he, hep1, heq0⟩
    obtain ⟨s, hs', hform⟩ := (hedge (u-e)).mp
      ⟨hcompl e he, by simp [hep1, (pure_mem p).2], by simp [heq0, (pure_mem q).2]⟩
    refine ⟨s, hs', ?_⟩
    have hh : u-(u-e) = (1-s) • ep + s • (u-eq) := by rw [hform]; module
    simpa using hh
  · rintro ⟨s, hs', he⟩
    have hform : u-e = (1-s) • (u-ep) + s • eq := by rw [he]; module
    have hh := (hedge (u-e)).mpr ⟨s, hs', hform⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using hcompl (u-e) hh.1
    · have hp' := hh.2.1; simp only [LinearMap.sub_apply, (pure_mem p).2] at hp'; linarith
    · have hq' := hh.2.2; simp only [LinearMap.sub_apply, (pure_mem q).2] at hq'; linarith

/-- The original pure-row identity pays whole-cone positivity before any upper
bound is used. The row premise is the protected producer's required join. -/
theorem pure_row_positive_bridge
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q)
    (eq : V →ₗ[ℝ] ℝ) (heq : eq ∈ fullZeroConfirmers C u q)
    (L : ℝ) (hL : 0 < L)
    (hform : ∀ x : V, eq x = (1 - L) * k.g.val x + L * (directionLift k v).val x)
    (hrow : ∀ s : pure C u, comparison C u p s = min (ep s) ((u - eq) s)) :
    let b := (1 / 2 : ℝ) • normalForm k 1 v
    proper C u b ∧ b p = 0 ∧ b q = 1 ∧ b (a.param (-v)) = 0 ∧
      a.param (-v) ∈ exclusion C u q := by
  have hg0 (x : V) (hx : x ∈ C) : 0 ≤ k.g.val x :=
    (interior_subset k.g_interior).1 x hx
  have hnrow (n : V →ₗ[ℝ] ℝ) (hn : proper C u n) (hnp : n p = 0)
      (s : pure C u) : n s ≤ max (k.g.val s) (eq s) := by
    have hcomp : comparison C u p s ≤ (u - n) s :=
      csInf_le ⟨0, by rintro r ⟨f, hf, rfl⟩; exact (hf.1 s (pure_mem s).1).1⟩
        ⟨u - n, ⟨(by
          intro x hx
          have hh := hn x hx
          constructor <;> simp only [LinearMap.sub_apply] <;> linarith),
          by simp [hnp, (pure_mem p).2]⟩, rfl⟩
    rw [hrow s] at hcomp
    have hgs : k.g.val s = 1 - ep s := by rw [k.g_value]; simp [(pure_mem s).2]
    simp only [LinearMap.sub_apply, (pure_mem s).2] at hcomp
    rcases le_total (ep s) (1 - eq s) with hh | hh
    · rw [min_eq_left hh] at hcomp
      exact (show n s ≤ k.g.val s by linarith).trans (le_max_left _ _)
    · rw [min_eq_right hh] at hcomp
      exact (show n s ≤ eq s by linarith).trans (le_max_right _ _)
  obtain ⟨M, hM, hdom⟩ := direction_domination k
  let ε := 1 / (2 * M)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεM : ε * M = 1 / 2 := by dsimp [ε]; field_simp <;> ring
  have hpos : ∀ x ∈ C, 0 ≤ normalForm k 1 v x := by
    apply nonneg_on_cone (base_compact hc hs) hs
    intro s
    by_contra hbad
    have hbad' : k.g.val s + (directionLift k v).val s < 0 := by
      simpa [normalForm] using lt_of_not_ge hbad
    have hi : |(directionLift k v).val s| ≤ ‖coordinateMap k s‖ := by
      rw [← coordinateMap_inner]
      simpa [hv] using abs_real_inner_le_norm v (coordinateMap k s)
    have hnorm : k.g.val s < ‖coordinateMap k s‖ := by
      linarith [neg_le_abs ((directionLift k v).val s)]
    have hH : 0 < ‖coordinateMap k s‖ := lt_of_le_of_lt (hg0 s (pure_mem s).1) hnorm
    let w : chartSpace a := ‖coordinateMap k s‖⁻¹ • coordinateMap k s
    have hw : ‖w‖ = 1 := by simp [w, norm_smul, hH.ne']
    have hws : (directionLift k w).val s = ‖coordinateMap k s‖ := by
      rw [← coordinateMap_inner]
      simp only [w, inner_smul_left, starRingEnd_apply, star_trivial,
        real_inner_self_eq_norm_sq]
      field_simp
    let n := normalForm k 1 (ε • w)
    have hn0 : ∀ x ∈ C, 0 ≤ n x := by
      intro x hx
      have hd := hdom w hw x hx
      have hd' := neg_abs_le ((directionLift k w).val x)
      have heps := mul_le_mul_of_nonneg_left ((neg_le_neg hd).trans hd') hε.le
      change 0 ≤ 1 * k.g.val x + (directionLift k (ε • w)).val x
      simp only [map_smul, Submodule.coe_smul, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      have hhalf : ε * (M * k.g.val x) = k.g.val x / 2 := by rw [← mul_assoc, hεM]; ring
      nlinarith [hg0 x hx]
    have hmax := (normal_maximum hc hs hg p hep k 1 (ε • w) hn0).1
    let f : V →ₗ[ℝ] ℝ := (1 + ε)⁻¹ • n
    have hf : proper C u f := by
      apply cone_bound (base_compact hc hs) hs
      intro r
      have hr := hmax r (pure_mem r)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hε, hw, mul_one] at hr
      change 0 ≤ (1 + ε)⁻¹ * n r ∧ (1 + ε)⁻¹ * n r ≤ 1
      constructor
      · exact mul_nonneg (by positivity) (hn0 r (pure_mem r).1)
      · apply (inv_mul_le_iff₀ (by positivity : 0 < 1 + ε)).mpr
        simpa using hr
    have hfp : f p = 0 := by simp [f, n, normalForm, span_vanishes]
    have hfs : k.g.val s < f s := by
      change k.g.val s < (1 + ε)⁻¹ * n s
      apply (lt_inv_mul_iff₀ (by positivity : 0 < 1 + ε)).mpr
      dsimp [n, normalForm]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, map_smul,
        Submodule.coe_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, one_mul]
      rw [hws]
      nlinarith
    have hneq : k.g.val s < eq s := by
      have hh := hnrow f hf hfp s
      rcases le_total (k.g.val s) (eq s) with he | he
      · exact lt_of_lt_of_le hfs (by simpa [max_eq_right he] using hh)
      · rw [max_eq_left he] at hh
        exact False.elim (not_lt_of_ge hh hfs)
    rw [hform s] at hneq
    have hgap : 0 < L * (k.g.val s - (directionLift k v).val s) :=
      mul_pos hL (by linarith [hg0 s (pure_mem s).1])
    nlinarith
  let b := (1 / 2 : ℝ) • normalForm k 1 v
  have hb : proper C u b := by
    apply cone_bound (base_compact hc hs) hs
    intro s
    have hh := (normal_maximum hc hs hg p hep k 1 v hpos).1 s (pure_mem s)
    rw [hv] at hh
    change 0 ≤ (1 / 2 : ℝ) * normalForm k 1 v s ∧
      (1 / 2 : ℝ) * normalForm k 1 v s ≤ 1
    constructor <;> linarith [hpos s (pure_mem s).1]
  have hbp : b p = 0 := by
    have hvp : (directionLift k v).val p = 0 := by
      rw [← coordinateMap_inner, (original_coordinate_map k).1, inner_zero_right]
    simp [b, normalForm, span_vanishes, hvp]
  have hbq : b q = 1 := by
    rw [← hq]
    norm_num [b, normalForm_chart hep k, real_inner_self_eq_norm_sq, hv]
  have hbr : b (a.param (-v)) = 0 := by
    simp [b, normalForm_chart hep k, inner_neg_right, real_inner_self_eq_norm_sq, hv]
  exact ⟨hb, hbp, hbq, hbr,
    (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1,
    b, ⟨hb, hbq⟩, hbr⟩

#print axioms pure_row_positive_bridge

end D5.S3.Quantum.Foundation.OriginalNormalFamily
