/- GID: D5/S3/Quantum/Foundation/OriginalRegularHeight
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalRegularHeight
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Actual adjacent exclusion balls have uniformly positive height at each regular anchor. -/

import D5.S3.Quantum.Foundation.RegularAnchorHeight
import D5.S3.Quantum.Foundation.OriginalNormalRestriction

/-! The original normal restriction pays the change of anchor before either
second-ball injectivity or uniform endpoint separation is used. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalRegularHeight

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open WholePairBallConfirmation OriginalFacePolarity FixedZeroObstruction
open OrthogonalJointCompletion OriginalNormalRestriction RegularAnchorHeight

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

private abbrev normal (C : PointedCone ℝ V) (p : V) : Set (V →L[ℝ] ℝ) :=
  {f | (∀ x ∈ C, 0 ≤ f x) ∧ f p = 0}

private abbrev normalSpan (C : PointedCone ℝ V) (p : V) :=
  Submodule.span ℝ (normal C p)

private abbrev chartSpace {p : V} (a : ExclusionChart C u p) :=
  EuclideanSpace ℝ (Fin a.dim)

private theorem chart_unit {p : V} (a : ExclusionChart C u p) (z : chartSpace a) :
    u (a.param z) = 1 := by
  have hspan : affineSpan ℝ (Metric.closedBall (0 : chartSpace a) 1) = ⊤ := by
    apply (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
    exact ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
  have heq : u.toAffineMap.comp a.param = AffineMap.const ℝ _ 1 := by
    apply AffineMap.ext_on hspan
    intro w hw
    exact (show a.param w ∈ exclusion C u p from
      a.whole ▸ mem_image_of_mem a.param hw).1.2
  exact congrArg (fun f : chartSpace a →ᵃ[ℝ] ℝ => f z) heq

private theorem peak_formula {p : V} (a : ExclusionChart C u p)
    (e : V →ₗ[ℝ] ℝ) (he : proper C u e)
    (v : chartSpace a) (hv : ‖v‖ = 1) (hpeak : e (a.param v) = 1) :
    ∀ z, e (a.param z) = 1 - ((1 - e (a.param (-v))) / 2) * (1 - ⟪v, z⟫) := by
  have hf := affine_zero_antipode ((u - e).toAffineMap.comp a.param)
    (by simpa using hv : ‖-v‖ = 1)
    (fun z hz => sub_nonneg.mpr (he _
      (show a.param z ∈ exclusion C u p from
        a.whole ▸ mem_image_of_mem a.param (by simpa using hz)).1.1).2)
    (by simpa [chart_unit a, hpeak])
  intro z
  have hh := hf z
  change u (a.param z) - e (a.param z) =
    (u (a.param (-v)) - e (a.param (-v))) / 2 * (1 + ⟪-v, z⟫) at hh
  simp only [chart_unit a, inner_neg_left] at hh
  linarith

private structure Coordinates (p : pure C u) (a : ExclusionChart C u p)
    (ep : V →ₗ[ℝ] ℝ) where
  g : normalSpan C p
  equivalence : normalSpan C p ≃ₗ[ℝ] (chartSpace a →ᵃ[ℝ] ℝ)
  g_value : g.val = (u - ep).toContinuousLinearMap
  g_interior : g ∈ interior ((normalSpan C p).subtype ⁻¹' normal C p)
  restriction : ∀ (f : normalSpan C p) z, equivalence f z = f.val (a.param z)

private theorem original_coordinates
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ q : pure C u, ∃ b : ExclusionChart C u q, b.dim = 3)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q))
    (p : pure C u) (a : ExclusionChart C u p) (ha : a.dim = 3)
    (ep : V →ₗ[ℝ] ℝ) (hp : ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep) :
    Nonempty (Coordinates p a ep) := by
  obtain ⟨g, e, hge, hgi, _, he, _, _⟩ :=
    (original_normal_restriction hc hs hg hEB3 (fun _ _ h => hInj h) p a ha).2.2.2.2 ep hp
  refine ⟨⟨g, e, hge, hgi, ?_⟩⟩
  intro f z
  exact congrArg (fun h : normalSpan C p →ₗ[ℝ] (chartSpace a →ᵃ[ℝ] ℝ) => h f z) he

private def directionLift {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (k : Coordinates p a ep) : chartSpace a →ₗ[ℝ] normalSpan C p :=
  k.equivalence.symm.toLinearMap.comp
    { toFun := fun v => (InnerProductSpace.toDual ℝ (chartSpace a) v).toLinearMap.toAffineMap
      map_add' := by intro v w; ext z; simp
      map_smul' := by
        intro t v
        ext z
        change ⟪t • v, z⟫ = t * ⟪v, z⟫
        simp }

private theorem directionLift_value {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (k : Coordinates p a ep) (v z : chartSpace a) :
    (directionLift k v).val (a.param z) = ⟪v, z⟫ := by
  rw [← k.restriction]
  simp [directionLift]

private theorem g_positive
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q))
    (p : pure C u) {ep : V →ₗ[ℝ] ℝ} (hep : ep ∈ fullZeroConfirmers C u p)
    {y : V} (hy : y ∈ base C u) (hyp : y ≠ p) : 0 < (u - ep) y := by
  have hnonneg := (hep.1.1 y hy.1).2
  have hne : ep y ≠ 1 := by
    intro heq
    exact hyp ((show y ∈ ({(p : V)} : Set V) from
      (full_zero_faces hc hs hg hB hInj p hep).2 ▸ ⟨hy, heq⟩))
  change 0 < u y - ep y
  rw [hy.2] at *
  exact sub_pos.mpr (lt_of_le_of_ne hnonneg hne)

private theorem peak_lift {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (hep : ep ∈ fullZeroConfirmers C u p)
    (k : Coordinates p a ep) (e : V →ₗ[ℝ] ℝ) (he : proper C u e) (hep0 : e p = 0)
    (v : chartSpace a) (hv : ‖v‖ = 1) (hpeak : e (a.param v) = 1) :
    let lam := (1 - e (a.param (-v))) / 2
    e.toContinuousLinearMap =
      (k.g + lam • (directionLift k v - k.g)).val := by
  dsimp only
  let eL : normalSpan C p := ⟨e.toContinuousLinearMap,
    Submodule.subset_span ⟨fun x hx => (he x hx).1, hep0⟩⟩
  have heq : eL = k.g + ((1 - e (a.param (-v))) / 2) •
      (directionLift k v - k.g) := by
    apply k.equivalence.injective
    ext z
    simp only [k.restriction]
    change e (a.param z) = k.g.val (a.param z) +
      ((1 - e (a.param (-v))) / 2) *
        ((directionLift k v).val (a.param z) - k.g.val (a.param z))
    have hgval : k.g.val (a.param z) = 1 := by
      rw [k.g_value]
      change u (a.param z) - ep (a.param z) = 1
      -- A full confirmer is zero on the whole ball, hence on its affine span.
      have hspan : affineSpan ℝ (Metric.closedBall (0 : chartSpace a) 1) = ⊤ := by
        apply (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
        exact ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
      have hezero : ep.toAffineMap.comp a.param = AffineMap.const ℝ _ 0 :=
        AffineMap.ext_on hspan (fun w hw => hep.2 _
          (a.whole ▸ mem_image_of_mem a.param hw))
      have hz := congrArg (fun f : chartSpace a →ᵃ[ℝ] ℝ => f z) hezero
      change ep (a.param z) = 0 at hz
      rw [chart_unit a, hz]
      norm_num
    rw [hgval, directionLift_value]
    rw [peak_formula a e he v hv hpeak z]
    ring
  exact congrArg Subtype.val heq

private theorem neighbor_unique
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q))
    (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q) :
    ∃ eq : V →ₗ[ℝ] ℝ, ∀ e, e ∈ fullZeroConfirmers C u q ↔ e = eq := by
  classical
  have hqD : (q : V) ∈ exclusion C u p := hq ▸
    (a.whole ▸ mem_image_of_mem a.param (by simpa using hv.le))
  have hpD := (exclusion_symmetric p q).mp hqD
  obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := pure_pair_in_ball hc hs hg hB q
  have hex : ∃ y : pure C u, (y : V) ∈ exclusion C u q ∧ y ≠ p := by
    by_cases h : y₁ = p
    · exact ⟨y₂, hy₂, fun hh => hne (h.trans hh.symm)⟩
    · exact ⟨y₁, hy₁, h⟩
  obtain ⟨y, hy, hyp⟩ := hex
  have hgy : 0 < (u - ep) y := g_positive hc hs hg hB hInj p hep (pure_mem y)
    (fun h => hyp (Subtype.val_injective h))
  have hsame (e f : V →ₗ[ℝ] ℝ)
      (he : e ∈ fullZeroConfirmers C u q) (hf : f ∈ fullZeroConfirmers C u q) : e = f := by
    let lam := (1 - e (a.param (-v))) / 2
    let μ := (1 - f (a.param (-v))) / 2
    have heL := peak_lift hep k e he.1.1 (he.2 _ hpD) v hv (hq ▸ he.1.2)
    have hfL := peak_lift hep k f hf.1.1 (hf.2 _ hpD) v hv (hq ▸ hf.1.2)
    have hey := congrArg (fun h : V →L[ℝ] ℝ => h y) heL
    have hfy := congrArg (fun h : V →L[ℝ] ℝ => h y) hfL
    change e y = k.g.val y + lam * ((directionLift k v).val y - k.g.val y) at hey
    change f y = k.g.val y + μ * ((directionLift k v).val y - k.g.val y) at hfy
    rw [he.2 _ hy] at hey
    rw [hf.2 _ hy] at hfy
    have hgn : k.g.val y ≠ 0 := by rw [k.g_value]; exact ne_of_gt hgy
    have hdiff : (directionLift k v).val y - k.g.val y ≠ 0 := by
      intro h
      simp only [h, mul_zero, add_zero] at hey
      exact hgn hey.symm
    have hlam : lam = μ := (mul_right_cancel₀ hdiff).mp (by linarith [hey, hfy])
    have hmaps : e.toContinuousLinearMap = f.toContinuousLinearMap := by
      rw [heL, hfL]
      change (k.g + lam • _).val = (k.g + μ • _).val
      rw [hlam]
    exact LinearMap.ext (fun x => congrArg (fun h : V →L[ℝ] ℝ => h x) hmaps)
  obtain ⟨eq, heq, hzero⟩ := ((exclusion_ball_faces hc hs hg hB).1 q).2.2.2.2.2.2
  have heqfull : eq ∈ fullZeroConfirmers C u q :=
    ⟨heq, fun x hx => (show x ∈ {x | x ∈ base C u ∧ eq x = 0} from hzero ▸ hx).2⟩
  exact ⟨eq, fun e => ⟨fun he => hsame e eq he heqfull, fun h => h ▸ heqfull⟩⟩

private theorem direction_domination {p : pure C u} {a : ExclusionChart C u p}
    {ep : V →ₗ[ℝ] ℝ} (k : Coordinates p a ep) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ v : chartSpace a, ‖v‖ = 1 →
      ∀ x ∈ C, |(directionLift k v).val x| ≤ M * k.g.val x := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp k.g_interior)
  let T := (directionLift k).toContinuousLinearMap
  let δ : ℝ := r / (2 * (‖T‖ + 1))
  have hδ : 0 < δ := div_pos hr (by positivity)
  refine ⟨δ⁻¹ + 1, le_add_of_nonneg_left (inv_nonneg.mpr hδ.le), ?_⟩
  intro v hv x hx
  have hsmall : ‖δ • directionLift k v‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    have hnorm : ‖directionLift k v‖ ≤ ‖T‖ := by
      simpa [T, hv] using T.le_opNorm v
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hnorm hδ.le)
    dsimp [δ]
    apply (div_mul_eq_mul_div _ _ _).trans_lt
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖T‖ + 1))).mpr
    nlinarith [norm_nonneg T]
  have hplus : k.g + δ • directionLift k v ∈
      (normalSpan C p).subtype ⁻¹' normal C p :=
    hball (by simpa [dist_eq_norm] using hsmall)
  have hminus : k.g - δ • directionLift k v ∈
      (normalSpan C p).subtype ⁻¹' normal C p :=
    hball (by simpa [dist_eq_norm] using hsmall)
  have hp := hplus.1 x hx
  have hm := hminus.1 x hx
  change 0 ≤ k.g.val x + δ * (directionLift k v).val x at hp
  change 0 ≤ k.g.val x - δ * (directionLift k v).val x at hm
  have hg0 := (interior_subset k.g_interior).1 x hx
  have hbound : |(directionLift k v).val x| ≤ δ⁻¹ * k.g.val x := by
    rw [inv_mul_eq_div, le_div_iff₀ hδ]
    by_cases hh : 0 ≤ (directionLift k v).val x
    · rw [abs_of_nonneg hh]
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hh)]
      nlinarith
  exact hbound.trans (by nlinarith)

private theorem neighbor_parameter_bound
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q))
    (p : pure C u) {a : ExclusionChart C u p} {ep : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p) (k : Coordinates p a ep)
    (M : ℝ) (hM : 1 ≤ M)
    (hbound : ∀ v : chartSpace a, ‖v‖ = 1 →
      ∀ x ∈ C, |(directionLift k v).val x| ≤ M * k.g.val x)
    (q : pure C u) (v : chartSpace a) (hv : ‖v‖ = 1) (hq : a.param v = q)
    (e : V →ₗ[ℝ] ℝ) (he : e ∈ fullZeroConfirmers C u q) :
    1 / (1 + M) ≤ (1 - e (a.param (-v))) / 2 := by
  have hqD : (q : V) ∈ exclusion C u p := hq ▸
    (a.whole ▸ mem_image_of_mem a.param (by simpa using hv.le))
  have hpD := (exclusion_symmetric p q).mp hqD
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
  let lam := (1 - e (a.param (-v))) / 2
  have hrK : a.param (-v) ∈ base C u :=
    (show a.param (-v) ∈ exclusion C u p from a.whole ▸
      mem_image_of_mem a.param (by simpa using hv.le)).1
  have hlam : 0 ≤ lam := by
    have hh := (he.1.1 _ hrK.1).2
    rw [hrK.2] at hh
    dsimp [lam]
    linarith
  have heL := peak_lift hep k e he.1.1 (he.2 _ hpD) v hv (hq ▸ he.1.2)
  have hey := congrArg (fun h : V →L[ℝ] ℝ => h y) heL
  change e y = k.g.val y + lam * ((directionLift k v).val y - k.g.val y) at hey
  rw [he.2 _ hy] at hey
  have hlo := (abs_le.mp (hbound v hv y (pure_mem y).1)).1
  have hmul := mul_le_mul_of_nonneg_left
    (show k.g.val y - (directionLift k v).val y ≤ (1 + M) * k.g.val y by linarith) hlam
  have hone : 1 ≤ lam * (1 + M) := by nlinarith
  exact (div_le_iff₀ (by linarith : 0 < 1 + M)).mpr (by nlinarith)

private theorem two_ball_identity
    {p q aa : pure C u} {b : ExclusionChart C u q}
    {ep eq ea : V →ₗ[ℝ] ℝ}
    (hep : ep ∈ fullZeroConfirmers C u p)
    (heq : eq ∈ fullZeroConfirmers C u q)
    (hea : ea ∈ fullZeroConfirmers C u aa)
    (kq : Coordinates q b eq)
    (s : chartSpace b) (hs : ‖s‖ = 1)
    (hsp : b.param s = p) (hsa : b.param (-s) = aa)
    (hpq : (q : V) ∈ exclusion C u p) :
    (1 - ea p) • ep + (1 - ep aa) • ea =
      (1 - ea p * ep aa) • (u - eq) := by
  have haD : (aa : V) ∈ exclusion C u q := hsa ▸
    (b.whole ▸ mem_image_of_mem b.param (by simpa using hs.le))
  have hepq := hep.2 _ hpq
  have heaq := hea.2 _ ((exclusion_symmetric q aa).mp haD)
  let epL : normalSpan C q := ⟨ep.toContinuousLinearMap,
    Submodule.subset_span ⟨fun x hx => (hep.1.1 x hx).1, hepq⟩⟩
  let eaL : normalSpan C q := ⟨ea.toContinuousLinearMap,
    Submodule.subset_span ⟨fun x hx => (hea.1.1 x hx).1, heaq⟩⟩
  have hidentity : (1 - ea p) • epL + (1 - ep aa) • eaL =
      (1 - ea p * ep aa) • kq.g := by
    apply kq.equivalence.injective
    ext z
    simp only [kq.restriction]
    change (1 - ea p) * ep (b.param z) + (1 - ep aa) * ea (b.param z) =
      (1 - ea p * ep aa) * kq.g.val (b.param z)
    have hepform := peak_formula b ep hep.1.1 s hs (hsp ▸ hep.1.2) z
    have heaform := peak_formula b ea hea.1.1 (-s) (by simpa using hs)
      (hsa ▸ hea.1.2) z
    rw [hsa] at hepform
    simp only [neg_neg, hsp, inner_neg_left] at heaform
    have hgform : kq.g.val (b.param z) = 1 := by
      rw [← kq.restriction]
      have hspan : affineSpan ℝ (Metric.closedBall (0 : chartSpace b) 1) = ⊤ := by
        apply (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
        exact ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
      have hezero : eq.toAffineMap.comp b.param = AffineMap.const ℝ _ 0 :=
        AffineMap.ext_on hspan (fun w hw => heq.2 _
          (b.whole ▸ mem_image_of_mem b.param hw))
      have hz := congrArg (fun f : chartSpace b →ᵃ[ℝ] ℝ => f z) hezero
      change eq (b.param z) = 0 at hz
      rw [kq.restriction, kq.g_value]
      change u (b.param z) - eq (b.param z) = 1
      rw [chart_unit b, hz]
      norm_num
    rw [hepform, heaform, hgform]
    ring
  ext x
  have hh := congrArg (fun f : normalSpan C q => f.val x) hidentity
  change (1 - ea p) * ep x + (1 - ep aa) * ea x =
    (1 - ea p * ep aa) * kq.g.val x at hh
  simpa only [kq.g_value] using hh

set_option maxHeartbeats 800000 in
/-- One positive original height at a given regular anchor works for every
unit direction, every complete adjacent ball chart, its actual opposite
endpoint and every full original confirming effect of that endpoint. -/
theorem original_regular_height
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ q : pure C u, ∃ b : ExclusionChart C u q, b.dim = 3)
    (hInj : Function.Injective (fun q : pure C u => exclusion C u q))
    (p : pure C u) (a : ExclusionChart C u p) (ha : a.dim = 3)
    (ep : V →ₗ[ℝ] ℝ) (hep : ep ∈ fullZeroConfirmers C u p)
    (hreg : RegularAnchor hc hs p) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ (v : chartSpace a), ‖v‖ = 1 →
      ∀ q : pure C u, a.param v = q →
      ∀ (b : ExclusionChart C u q), b.dim = 3 →
      ∀ (s : chartSpace b), ‖s‖ = 1 → b.param s = p →
      ∀ aa : pure C u, b.param (-s) = aa →
      ∀ ea : V →ₗ[ℝ] ℝ, ea ∈ fullZeroConfirmers C u aa →
        σ ≤ (u - ep) aa ∧
        (aa : V) ∈ exclusion C u q ∧
        ∀ x ∈ exclusion C u q, (u - ep) x ≤ (u - ep) aa := by
  classical
  let hB : exclusionBalls C u := fun q => ⟨(hEB3 q).choose⟩
  obtain ⟨ep₀, hp₀⟩ := hreg.1
  have hepep₀ := (hp₀ ep).mp hep
  have hp : ∀ e, e ∈ fullZeroConfirmers C u p ↔ e = ep := by
    simpa only [hepep₀] using hp₀
  obtain ⟨k⟩ := original_coordinates hc hs hg hEB3 hInj p a ha ep hp
  obtain ⟨M, hM, hbound⟩ := direction_domination k
  have hε : 0 < 2 / (1 + M) := div_pos (by norm_num) (by linarith)
  obtain ⟨σ, hσ, hheight⟩ := regular_anchor_uniform_height hc hs hg hB hInj p ep hreg hep hε
  refine ⟨σ, hσ, ?_⟩
  intro v hv q hq b hb s hsphere hsp aa hsa ea hea
  have hqD : (q : V) ∈ exclusion C u p := hq ▸
    (a.whole ▸ mem_image_of_mem a.param (by simpa using hv.le))
  have hpD := (exclusion_symmetric p q).mp hqD
  obtain ⟨eq, hqunique⟩ := neighbor_unique hc hs hg hB hInj p hep k q v hv hq
  have heq : eq ∈ fullZeroConfirmers C u q := (hqunique eq).mpr rfl
  obtain ⟨kq⟩ := original_coordinates hc hs hg hEB3 hInj q b hb eq hqunique
  have hid := two_ball_identity hep heq hea kq s hsphere hsp hsa hqD
  have haD : (aa : V) ∈ exclusion C u q := hsa ▸
    (b.whole ▸ mem_image_of_mem b.param (by simpa using hsphere.le))
  have hap : (aa : V) ≠ p := by
    intro he
    have hneg : -s = s := b.injective (hsa.trans (he.trans hsp.symm))
    have hs0 : s = 0 := by have hh := congrArg (fun z => z + s) hneg; simpa using hh
    simpa [hs0] using hsphere
  have htpos : 0 < 1 - ep aa := by
    simpa only [LinearMap.sub_apply, (pure_mem aa).2] using
      g_positive hc hs hg hB hInj p hep (pure_mem aa) hap
  have ht : 0 ≤ ep aa := (hep.1.1 _ (pure_mem aa).1).1
  have hd : ea p ≤ 1 := by simpa only [(pure_mem p).2] using
    (hea.1.1 _ (pure_mem p).1).2
  have hlam := neighbor_parameter_bound hc hs hg hB hInj p hep k M hM hbound q v hv hq eq heq
  have hzD : a.param (-v) ∈ exclusion C u p := a.whole ▸
    mem_image_of_mem a.param (by simpa using hv.le)
  have hread := congrArg (fun f : V →ₗ[ℝ] ℝ => f (a.param (-v))) hid
  have hepz := hep.2 _ hzD
  change (1 - ea p) * ep (a.param (-v)) + (1 - ep aa) * ea (a.param (-v)) =
    (1 - ea p * ep aa) * (u (a.param (-v)) - eq (a.param (-v))) at hread
  rw [hepz, chart_unit a] at hread
  have hfactor : 1 - ep aa ≤ 1 - ea p * ep aa := by nlinarith
  have hlam0 : 0 ≤ 1 - eq (a.param (-v)) := by
    have hh := (heq.1.1 _ hzD.1.1).2
    rw [hzD.1.2] at hh
    linarith
  have hmul := mul_le_mul_of_nonneg_right hfactor hlam0
  have hreading : 2 / (1 + M) ≤ ea (a.param (-v)) := by
    have htwo : 2 / (1 + M) ≤ 1 - eq (a.param (-v)) := by linarith
    have hmid : 1 - eq (a.param (-v)) ≤ ea (a.param (-v)) := by nlinarith
    exact htwo.trans hmid
  refine ⟨hheight aa ea hea ⟨_, hzD, hreading⟩, haD, ?_⟩
  have hgpos : ∀ z, ‖z‖ ≤ 1 → 0 ≤ (u - ep) (b.param z) := by
    intro z hz
    exact sub_nonneg.mpr (hep.1.1 _
      (show b.param z ∈ exclusion C u q from b.whole ▸
        mem_image_of_mem b.param (by simpa using hz)).1.1).2
  have hgp : (u - ep) (b.param s) = 0 := by
    simp [hsp, hep.1.2, (pure_mem p).2]
  have hgform := affine_zero_antipode ((u - ep).toAffineMap.comp b.param)
    (by simpa using hsphere : ‖-s‖ = 1) hgpos (by simpa using hgp)
  intro x hx
  obtain ⟨w, hw, rfl⟩ := b.whole.symm ▸ hx
  have hw1 : ‖w‖ ≤ 1 := by simpa using hw
  have hinner : ⟪-s, w⟫ ≤ 1 := by
    calc
      ⟪-s, w⟫ ≤ ‖-s‖ * ‖w‖ := real_inner_le_norm _ _
      _ ≤ 1 := by simpa [hsphere] using hw1
  have hga : 0 ≤ (u - ep) aa := by
    exact sub_nonneg.mpr (hep.1.1 _ (pure_mem aa).1).2
  have hh := hgform w
  change (u - ep) (b.param w) = (u - ep) (b.param (-s)) / 2 * (1 + ⟪-s, w⟫) at hh
  rw [hsa] at hh
  nlinarith

#print axioms original_regular_height

end D5.S3.Quantum.Foundation.OriginalRegularHeight
