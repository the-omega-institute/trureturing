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
  let Z : Submodule ℝ (V →L[ℝ] ℝ) := { carrier := {h | h p = 0}
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
    {ep : V →ₗ[ℝ] ℝ} (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep) (α : ℝ) (v z : chartSpace a) :
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
    {ep : V →ₗ[ℝ] ℝ} (k : Coordinates p a ep) (v : chartSpace a) (hv : ‖v‖ = 1) :
    BddAbove ((fun x : V => -(directionLift k v).val x / k.g.val x) '' (base C u \ {(p : V)})) := by
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q)) (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep) (v : chartSpace a) (hv : ‖v‖ = 1) :
    1 ≤ rho k v ∧ ∀ α : ℝ, (∀ x ∈ C, 0 ≤ normalForm k α v x) ↔ rho k v ≤ α := by
  have hne : ((fun x : V => -(directionLift k v).val x / k.g.val x) '' (base C u \ {(p : V)})).Nonempty := by
    exact ⟨_, a.param (-v), ⟨(SingleLabelNormalBody.chart_mem a (by simpa using hv.le)).1,
      ball_ne_anchor (by simpa using hv.le)⟩, rfl⟩
  have hbound := ratio_bound k v hv
  have hpos (x : V) (hx : x ∈ base C u) (hxp : x ≠ p) : 0 < k.g.val x := by
    rw [k.g_value]
    exact g_positive hc hs hg hB hInj p hep hx hxp
  have hrho : 1 ≤ rho k v := by
    have hh := le_csSup hbound (mem_image_of_mem (fun x : V => -(directionLift k v).val x / k.g.val x)
      (show a.param (-v) ∈ base C u \ {(p : V)} from ⟨(SingleLabelNormalBody.chart_mem a (by simpa using hv.le)).1,
          ball_ne_anchor (by simpa using hv.le)⟩))
    simpa [rho, directionLift_value, g_chart hep k, inner_neg_right, real_inner_self_eq_norm_sq, hv] using hh
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
    · have hh := (le_csSup hbound (mem_image_of_mem (fun x : V => -(directionLift k v).val x / k.g.val x)
        (show (s : V) ∈ base C u \ {(p : V)} from ⟨pure_mem s, hsp⟩))).trans hα
      have hmul := (div_le_iff₀ (hpos s (pure_mem s) hsp)).mp hh
      change 0 ≤ α * k.g.val s + (directionLift k v).val s
      linarith

/-- Once positivity is established, the original whole-base maximum is alpha+norm(v). -/
theorem normal_maximum
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ} (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (α : ℝ) (v : chartSpace a) (hpos : ∀ x ∈ C, 0 ≤ normalForm k α v x) : (∀ x ∈ base C u, normalForm k α v x ≤ α + ‖v‖) ∧
      ∃ x ∈ exclusion C u p, normalForm k α v x = α + ‖v‖ := by
  have hupper : ∀ x ∈ base C u, normalForm k α v x ≤ α + ‖v‖ := by
    by_cases hn : normalForm k α v = 0
    · intro x hx
      have hα : 0 ≤ α := by
        have hh := hpos (a.param 0) (SingleLabelNormalBody.chart_mem a (by simp)).1.1
        simpa [normalForm_chart hep k] using hh
      rw [hn]; simp only [LinearMap.zero_apply]; positivity
    · obtain ⟨s, hsD, _, hmax⟩ := positive_annihilator_maximum hc hs hg p (normalForm k α v) hn hpos (by
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q)) (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q) :
    ∃ eq : V →ₗ[ℝ] ℝ, (∀ e, e ∈ fullZeroConfirmers C u q ↔ e = eq) ∧
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
    have hh := (heq.1.1 _ (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1.1).1
    dsimp [lam]; linarith
  obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := pure_pair_in_ball hc hs hg hB q
  have hex : ∃ y : pure C u, (y : V) ∈ exclusion C u q ∧ y ≠ p := by
    by_cases h : y₁ = p
    · exact ⟨y₂, hy₂, fun hh => hne (h.trans hh.symm)⟩
    · exact ⟨y₁, hy₁, h⟩
  obtain ⟨y, hy, hyp⟩ := hex
  have hgy : 0 < k.g.val y := by
    rw [k.g_value]
    exact g_positive hc hs hg hB hInj p hep (pure_mem y) (fun h => hyp (Subtype.val_injective h))
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
      exact le_csSup (ratio_bound k v hv) ⟨y, ⟨pure_mem y, fun h => hyp (Subtype.val_injective h)⟩, rfl⟩
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
      refine ⟨(SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1, eq, heq.1, ?_⟩
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
    (∀ z : chartSpace a, coordinateMap k (a.param z) = z) ∧ (∀ v : chartSpace a, ∃ f : normalSpan C p,
      ∀ x : V, ⟪v, coordinateMap k x⟫ = f.val x) ∧
    ∀ H : V →ₗ[ℝ] chartSpace a, (∀ v : chartSpace a, ∃ f : normalSpan C p, ∀ x : V, ⟪v, H x⟫ = f.val x) →
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q)) (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q) :
    ∃ eq : V →ₗ[ℝ] ℝ, (∀ e, e ∈ fullZeroConfirmers C u q ↔ e = eq) ∧ ∀ b : V →ₗ[ℝ] ℝ, (proper C u b ∧ b p = 0 ∧ b q = 1) ↔
        ∃ s : ℝ, s ∈ Icc (0 : ℝ) 1 ∧ b = (1 - s) • (u - ep) + s • eq := by
  obtain ⟨eq, hqunique, hlam, hlamhalf, heqform, hanti, horth⟩ := original_neighbor_support hc hs hg hB hInj p hep k q v hv hq
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
    exact g_positive hc hs hg hB hInj p hep (pure_mem y) (fun h => hyp (Subtype.val_injective h))
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
    change _ = (1 - μ / L) * k.g.val x + (μ / L) * ((1 - L) * k.g.val x + L * (directionLift k v).val x)
    field_simp
    <;> ring
  · rintro ⟨s, hs', rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hgx := hG x hx
      change 0 ≤ u x - ep x ∧ u x - ep x ≤ u x at hgx
      have heqx := heq.1.1 x hx
      change 0 ≤ (1 - s) * (u x - ep x) + s * eq x ∧ (1 - s) * (u x - ep x) + s * eq x ≤ u x
      constructor
      · exact add_nonneg (mul_nonneg (by linarith [hs'.2]) hgx.1) (mul_nonneg hs'.1 heqx.1)
      · nlinarith [mul_le_mul_of_nonneg_left hgx.2 (show 0 ≤ 1 - s by linarith [hs'.2]), mul_le_mul_of_nonneg_left heqx.2 hs'.1]
    · simp [hep.1.2, heq.2 _ hpD, (pure_mem p).2]
    · simp [hep.2 _ hqD, heq.1.2, (pure_mem q).2]

#print axioms original_whole_edge

/-- The complete fixed edge J(p,q), obtained by complementation on all of V. -/
theorem original_fixed_edge
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q)) (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q) :
    ∃ eq : V →ₗ[ℝ] ℝ, (∀ e, e ∈ fullZeroConfirmers C u q ↔ e = eq) ∧ ∀ e : V →ₗ[ℝ] ℝ, (proper C u e ∧ e p = 1 ∧ e q = 0) ↔
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
    obtain ⟨s, hs', hform⟩ := (hedge (u-e)).mp ⟨hcompl e he, by simp [hep1, (pure_mem p).2], by simp [heq0, (pure_mem q).2]⟩
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ} (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q) (eq : V →ₗ[ℝ] ℝ) (heq : eq ∈ fullZeroConfirmers C u q)
    (L : ℝ) (hL : 0 < L) (hform : ∀ x : V, eq x = (1 - L) * k.g.val x + L * (directionLift k v).val x)
    (hrow : ∀ s : pure C u, comparison C u p s = min (ep s) ((u - eq) s)) :
    let b := (1 / 2 : ℝ) • normalForm k 1 v
    proper C u b ∧ b p = 0 ∧ b q = 1 ∧ b (a.param (-v)) = 0 ∧ a.param (-v) ∈ exclusion C u q := by
  have hg0 (x : V) (hx : x ∈ C) : 0 ≤ k.g.val x := (interior_subset k.g_interior).1 x hx
  have hnrow (n : V →ₗ[ℝ] ℝ) (hn : proper C u n) (hnp : n p = 0) (s : pure C u) : n s ≤ max (k.g.val s) (eq s) := by
    have hcomp : comparison C u p s ≤ (u - n) s := csInf_le ⟨0, by rintro r ⟨f, hf, rfl⟩; exact (hf.1 s (pure_mem s).1).1⟩
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
      simp only [w, inner_smul_left, starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq]
      field_simp
    let n := normalForm k 1 (ε • w)
    have hn0 : ∀ x ∈ C, 0 ≤ n x := by
      intro x hx
      have hd := hdom w hw x hx
      have hd' := neg_abs_le ((directionLift k w).val x)
      have heps := mul_le_mul_of_nonneg_left ((neg_le_neg hd).trans hd') hε.le
      change 0 ≤ 1 * k.g.val x + (directionLift k (ε • w)).val x
      simp only [map_smul, Submodule.coe_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
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
    have hgap : 0 < L * (k.g.val s - (directionLift k v).val s) := mul_pos hL (by linarith [hg0 s (pure_mem s).1])
    nlinarith
  let b := (1 / 2 : ℝ) • normalForm k 1 v
  have hb : proper C u b := by
    apply cone_bound (base_compact hc hs) hs
    intro s
    have hh := (normal_maximum hc hs hg p hep k 1 v hpos).1 s (pure_mem s)
    rw [hv] at hh
    change 0 ≤ (1 / 2 : ℝ) * normalForm k 1 v s ∧ (1 / 2 : ℝ) * normalForm k 1 v s ≤ 1
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
  exact ⟨hb, hbp, hbq, hbr, (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le)).1, b, ⟨hb, hbq⟩, hbr⟩

#print axioms pure_row_positive_bridge

end D5.S3.Quantum.Foundation.OriginalNormalFamily

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
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) {p : pure C u} (a : ExclusionChart C u p)
    (v : EuclideanSpace ℝ (Fin a.dim)) (hv : ‖v‖ = 1) (q : pure C u) (hq : a.param v = q) :
    ∃ (t : ℝ) (e : V →ₗ[ℝ] ℝ), 0 ≤ t ∧ t ≤ 1 / 2 ∧ confirms C u q e ∧ (∀ z, e (a.param z) = 1 - t + t * ⟪v, z⟫) ∧
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
    have hb : BddBelow {r | ∃ f, confirms C u q f ∧ f (a.param z) = r} := ⟨0, by rintro r ⟨f, hf, rfl⟩; exact (hf.1 _ hx.1.1).1⟩
    have hne : ({r | ∃ f, confirms C u q f ∧ f (a.param z) = r} : Set ℝ).Nonempty :=
      ⟨e (a.param z), e.toLinearMap, ⟨he.1, he.2⟩, rfl⟩
    apply le_antisymm
    · exact (csInf_le hb ⟨e.toLinearMap, ⟨he.1, he.2⟩, rfl⟩).trans_eq (hform z)
    · apply le_csInf hne
      rintro r ⟨f, hf, rfl⟩
      have hr : comparison C u q (a.param (-v)) ≤ f (a.param (-v)) := csInf_le ⟨0, by rintro r ⟨g, hg, rfl⟩; exact
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s) (p : pure C u) (a : ExclusionChart C u p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧ ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → ∀ q : pure C u, a.param v = q →
      ∃ e : V →ₗ[ℝ] ℝ, confirms C u q e ∧ (∀ z, e (a.param z) = 1 - t + t * ⟪v, z⟫) ∧
        (∀ z, ‖z‖ ≤ 1 → comparison C u q (a.param z) = 1 - t + t * ⟪v, z⟫) := by
  classical
  let E := EuclideanSpace ℝ (Fin a.dim)
  letI : Nonempty (Fin a.dim) := ⟨⟨0, a.dim_pos⟩⟩
  obtain ⟨v₀, hv₀⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  have hpure (v : E) (hv : ‖v‖ = 1) : a.param v ∈ pure C u := ((chart_boundary hc hs hg hB p a).symm ▸
      (show a.param v ∈ a.param '' Metric.sphere 0 1 from ⟨v, by simpa using hv, rfl⟩)).2
  let q₀ : pure C u := ⟨a.param v₀, hpure v₀ hv₀⟩
  obtain ⟨t₀, e₀, ht₀, ht₀half, he₀, hform₀, hcomp₀⟩ := directional_attainment hs hg a v₀ hv₀ q₀ rfl
  have ht₀pos : 0 < t₀ := by
    obtain ⟨h, hh, hzero, he, hone, _⟩ := reciprocal_endpoint_exposure hc hs hg q₀ (fun x => (hPR q₀ x).le)
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
      have hh := (hcomp (-v) (by simpa using hv.le)).symm.trans (hqq ▸ hcomp₀ (-v) (by simpa using hv.le))
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
  0 ≤ M ∧ ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ M * u x) ∧ ∀ z, ‖z‖ ≤ 1 → g (a.param z) = (1 + ⟪v, z⟫) / 2

/-- The original infimum over all positive extensions and all nonnegative budgets. -/
def extensionBudget {p : V} (a : ExclusionChart C u p)
    (v : EuclideanSpace ℝ (Fin a.dim)) : ℝ :=
  sInf {M : ℝ | BudgetFeasible a v M}

private theorem sharp_budget {p : pure C u} (a : ExclusionChart C u p)
    (t : ℝ) (ht : 0 < t) (v : EuclideanSpace ℝ (Fin a.dim)) (hv : ‖v‖ = 1) (q : pure C u) (hq : a.param (-v) = q)
    (e : V →ₗ[ℝ] ℝ) (he : confirms C u q e) (hform : ∀ z, e (a.param z) = 1 - t + t * ⟪-v, z⟫)
    (hcomp : comparison C u q (a.param v) = 1 - 2 * t) :
    BudgetFeasible a v (1 / (2 * t)) ∧ (∀ M, BudgetFeasible a v M → 1 / (2 * t) ≤ M) ∧ extensionBudget a v = 1 / (2 * t) := by
  have ht2 : 0 < 2 * t := by positivity
  have hupper : BudgetFeasible a v (1 / (2 * t)) := by
    refine ⟨by positivity, (2 * t)⁻¹ • (u - e), ?_, ?_⟩
    · intro x hx
      change 0 ≤ (2 * t)⁻¹ * (u x - e x) ∧ (2 * t)⁻¹ * (u x - e x) ≤ (1 / (2 * t)) * u x
      have hh := he.1 x hx
      constructor
      · exact mul_nonneg (inv_nonneg.mpr ht2.le) (sub_nonneg.mpr hh.2)
      · simpa only [one_div] using mul_le_mul_of_nonneg_left (show u x - e x ≤ u x by linarith) (inv_nonneg.mpr ht2.le)
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
    have hle : comparison C u q (a.param v) ≤ f (a.param v) := csInf_le ⟨0, by rintro r ⟨k, hk, rfl⟩; exact
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s) (p : pure C u) (a : ExclusionChart C u p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧ (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → ∀ q : pure C u, a.param v = q →
        ∃ e : V →ₗ[ℝ] ℝ, confirms C u q e ∧ (∀ z, e (a.param z) = 1 - t + t * ⟪v, z⟫) ∧
          (∀ z, ‖z‖ ≤ 1 → comparison C u q (a.param z) = 1 - t + t * ⟪v, z⟫)) ∧
      (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → BudgetFeasible a v (1 / (2 * t)) ∧
        (∀ M, BudgetFeasible a v M → 1 / (2 * t) ≤ M) ∧
        extensionBudget a v = 1 / (2 * t)) := by
  obtain ⟨t, ht, hthalf, hscale⟩ := original_ball_scale hc hs hg hB hPR p a
  refine ⟨t, ht, hthalf, hscale, ?_⟩
  intro v hv
  have hq : a.param (-v) ∈ pure C u := ((chart_boundary hc hs hg hB p a).symm ▸
      (show a.param (-v) ∈ a.param '' Metric.sphere 0 1 from ⟨-v, by simpa using hv, rfl⟩)).2
  obtain ⟨e, he, hform, hcomp⟩ := hscale (-v) (by simpa using hv) ⟨a.param (-v), hq⟩ rfl
  apply sharp_budget a t ht v hv ⟨a.param (-v), hq⟩ rfl e he hform
  have hh := hcomp v hv.le
  simp only [inner_neg_left, real_inner_self_eq_norm_sq, hv, one_pow, mul_neg, mul_one] at hh
  linarith

private theorem affine_positive_lift {p : pure C u} (a : ExclusionChart C u p)
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (B : ℝ) (hB : 1 ≤ B)
    (hlift : ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → BudgetFeasible a v B) (h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ)
    (hpos : ∀ z, ‖z‖ ≤ 1 → 0 ≤ h z) :
    ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x) ∧ (∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z) ∧
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
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hc) (hu x hx)) (mul_nonneg (by positivity) (hg x hx).1)
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
        _ ≤ (h 0 - ‖b‖) * u x + (2 * ‖b‖) * (B * u x) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hg x hx).2
            (show 0 ≤ 2 * ‖b‖ by positivity))
        _ = (h 0 - ‖b‖ + 2 * ‖b‖ * B) * u x := by ring
        _ ≤ B * u x := mul_le_mul_of_nonneg_right hscalar (hu x hx)

/-- The original optimum is common to all directions and to the entire affine
face-effect family. Every positive affine face function has an actual positive lift. -/
theorem original_full_face_budget
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s) (p : pure C u) (a : ExclusionChart C u p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧ (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → BudgetFeasible a v (1 / (2 * t)) ∧
        (∀ M, BudgetFeasible a v M → 1 / (2 * t) ≤ M) ∧
        extensionBudget a v = 1 / (2 * t)) ∧
      (∀ h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ, (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z) → ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x) ∧
          (∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z) ∧ ((∀ z, ‖z‖ ≤ 1 → h z ≤ 1) → ∀ x ∈ C, g x ≤ (1 / (2 * t)) * u x)) ∧
      (∀ B : ℝ, (∀ h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ, (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) → ∃ g : V →ₗ[ℝ] ℝ,
          (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ B * u x) ∧
          ∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z) → 1 / (2 * t) ≤ B) := by
  obtain ⟨t, ht, hthalf, _, hbudget⟩ := original_scale_and_sharp_budget hc hs hg hB hPR p a
  have hBmin : 1 ≤ 1 / (2 * t) := (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr (by linarith)
  refine ⟨t, ht, hthalf, hbudget, fun h hh => affine_positive_lift a hs _ hBmin (fun v hv => (hbudget v hv).1) h hh, ?_⟩
  intro B hwhole
  let E := EuclideanSpace ℝ (Fin a.dim)
  letI : Nonempty (Fin a.dim) := ⟨⟨0, a.dim_pos⟩⟩
  obtain ⟨v, hv⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  let h : E →ᵃ[ℝ] ℝ := (1 / 2 : ℝ) • (AffineMap.const ℝ E 1 + (InnerProductSpace.toDual ℝ E v).toLinearMap.toAffineMap)
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
    (a b : ExclusionChart C u p) (A B : ℝ) (ha : ∀ h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ, (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
      ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ A * u x) ∧ ∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z)
    (hb : ∀ h : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ, (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
      ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ B * u x) ∧ ∀ z, ‖z‖ ≤ 1 → g (b.param z) = h z) :
    ∀ h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ, (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
      ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ B * u x) ∧ ∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z := by
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s) (p : pure C u) (a b : ExclusionChart C u p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧ (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → extensionBudget a v = 1 / (2 * t)) ∧
      (∀ v : EuclideanSpace ℝ (Fin b.dim), ‖v‖ = 1 → extensionBudget b v = 1 / (2 * t)) := by
  obtain ⟨ta, hta, htah, hda, hla, hma⟩ := original_full_face_budget hc hs hg hB hPR p a
  obtain ⟨tb, htb, htbh, hdb, hlb, hmb⟩ := original_full_face_budget hc hs hg hB hPR p b
  have hfa : ∀ h : EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ, (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
      ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ (1 / (2 * ta)) * u x) ∧ ∀ z, ‖z‖ ≤ 1 → g (a.param z) = h z := by
    intro h hh
    obtain ⟨g, hg0, hgz, hg1⟩ := hla h (fun z hz => (hh z hz).1)
    exact ⟨g, fun x hx => ⟨hg0 x hx, hg1 (fun z hz => (hh z hz).2) x hx⟩, hgz⟩
  have hfb : ∀ h : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ, (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
      ∃ g : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x ∧ g x ≤ (1 / (2 * tb)) * u x) ∧ ∀ z, ‖z‖ ≤ 1 → g (b.param z) = h z := by
    intro h hh
    obtain ⟨g, hg0, hgz, hg1⟩ := hlb h (fun z hz => (hh z hz).1)
    exact ⟨g, fun x hx => ⟨hg0 x hx, hg1 (fun z hz => (hh z hz).2) x hx⟩, hgz⟩
  have heq : 1 / (2 * ta) = 1 / (2 * tb) := le_antisymm (hma _ (whole_budget_transport a b _ _ hfa hfb))
    (hmb _ (whole_budget_transport b a _ _ hfb hfa))
  exact ⟨ta, hta, htah, fun v hv => (hda v hv).2.2, fun v hv => ((hdb v hv).2.2).trans heq.symm⟩

#print axioms original_chart_independence

/-- A single intrinsic scale works in every chart of the same full original
exclusion, on all mixed inputs, with the actual attained sharp budget. -/
theorem original_common_chart_scale
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ s t : pure C u, comparison C u s t = comparison C u t s) (p : pure C u) (a : ExclusionChart C u p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧ ∀ b : ExclusionChart C u p, ∀ v : EuclideanSpace ℝ (Fin b.dim), ‖v‖ = 1 →
      (BudgetFeasible b v (1 / (2*t)) ∧ (∀ M, BudgetFeasible b v M → 1 / (2*t) ≤ M) ∧ extensionBudget b v = 1 / (2*t)) ∧
      ∀ q : pure C u, b.param v = q → ∃ e : V →ₗ[ℝ] ℝ, confirms C u q e ∧ (∀ z, e (b.param z) = 1-t+t*⟪v,z⟫) ∧
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
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    ∃ L : ℝ, 0 < L ∧ ∀ p : pure C u, ∀ x ∈ base C u, ∀ y ∈ base C u,
      |comparison C u p x - comparison C u p y| ≤ L * ‖x - y‖ := by
  let M := CommonOldExclusionConfirmation.effectNormBound C u
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro p x hx y hy
  have h := (CommonOldExclusionConfirmation.comparison_lipschitz hs hg p).dist_le_mul (⟨x, hx⟩ : base C u) (⟨y, hy⟩ : base C u)
  change dist (comparison C u p x) (comparison C u p y) ≤ M * dist x y at h
  have hbound : |comparison C u p x - comparison C u p y| ≤ M * ‖x-y‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using h
  exact hbound.trans (mul_le_mul_of_nonneg_right (by dsimp [M]; linarith [le_abs_self M]) (norm_nonneg _))

/-- The same bound controls every axis in every chart at every original label.
Its scale is obtained from the actual comparison law and attained optimal budget. -/
theorem original_scale_axis_bound
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) :
    ∃ L : ℝ, 0 < L ∧ ∀ (p : pure C u) (a : ExclusionChart C u p), ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
        (∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → extensionBudget a v = 1 / (2*t)) ∧
        ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → 2*t ≤ L * ‖a.param v - a.param (-v)‖ := by
  obtain ⟨L, hL, hbound⟩ := original_uniform_comparison hs hg
  refine ⟨L, hL, ?_⟩
  intro p a
  obtain ⟨t, ht, hth, hscale, hbudget⟩ := original_scale_and_sharp_budget hc hs hg hB hPR p a
  refine ⟨t, ht, hth, fun v hv => (hbudget v hv).2.2, ?_⟩
  intro v hv
  have hvP : a.param v ∈ pure C u := ((chart_boundary hc hs hg hB p a).symm ▸
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
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) (U : Set (pure C u)) (B : ℝ) (hBpos : 0 < B)
    (hbudget : ∀ p ∈ U, ∀ a : ExclusionChart C u p, ∀ v : EuclideanSpace ℝ (Fin a.dim), ‖v‖ = 1 → extensionBudget a v ≤ B) :
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
      (SingleLabelNormalBody.chart_mem a hv.le) (SingleLabelNormalBody.chart_mem a (z := -v) (by simpa using hv.le))
  apply (div_le_iff₀ (mul_pos hBpos hL)).mpr
  have hh := mul_le_mul_of_nonneg_left ((hax v hv).trans (mul_le_mul_of_nonneg_left hdiam hL.le)) hBpos.le
  nlinarith

#print axioms original_scale_axis_bound
#print axioms original_bounded_budget_noncollapse

end D5.S3.Quantum.Foundation.OriginalComparisonTopology
