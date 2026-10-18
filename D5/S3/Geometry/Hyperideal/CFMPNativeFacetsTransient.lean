import D5.S3.Geometry.Hyperideal.CFMPNativeForwardTransient
import Batteries.Tactic.OpenPrivate

/-! UNCOMPILED transient source-only incremental extension of facets.lean.
Zero canonical Lean retention. No compilation, kernel proof or benchmark result.
Original suffix statements, proofs and comments are preserved verbatim.
Cumulative-file comments refer to the supplied packet; inherited declarations
are supplied by imports here. Any original retention commentary is superseded
by this attempt's zero-retention constraint. -/

noncomputable section
open scoped BigOperators Matrix
open Set
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments

/-! Bounded full-support-face extension. Entire file UNCOMPILED.
No imports or inherited bytes have been changed. The public metric supplier
owns all hyperbolic segment geometry. The terminal results concern precisely
NativeForward.forward8halfspace l hl hdet, with its original normals/corners.
Here “affine face hull” means convexHull in the original affine coefficient
space, not equality of a bounded face with its unbounded affineSpan. -/
namespace NativeCornerExtractionSource
open private B_apply
  from D5.S3.Geometry.Hyperideal.CFMPNativeCapMetricTransient
open private temporary_dual_support_conclusion
  from D5.S3.Geometry.Hyperideal.CFMPNativeInverseTransient

namespace NativeFacets
open NativeForward
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.HyperbolicTopology
set_option autoImplicit false

/-- Elementary support-slice lemma, actually consumed twice below.
The auxiliary convex set remembers that a zero support value must already
belong to the hull of zero-support generators. -/
theorem convexHull_zero_support {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Set E) (f : E →ₗ[ℝ] ℝ) (hS : ∀ x ∈ S, f x ≤ 0) :
    convexHull ℝ S ∩ {x | f x = 0} = convexHull ℝ (S ∩ {x | f x = 0}) := by
  let H := convexHull ℝ (S ∩ {x | f x = 0})
  let T : Set E := {x | f x ≤ 0 ∧ (f x = 0 → x ∈ H)}
  have hT : Convex ℝ T := by
    intro x hx y hy a b ha hb hab
    have he : f (a • x + b • y) = a * f x + b * f y := by simp
    refine ⟨?_, ?_⟩
    · rw [he]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx.1)
        (mul_nonpos_of_nonneg_of_nonpos hb hy.1)
    · intro hz
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using
          hy.2 (by simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using hz)
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simpa only [hb0, ha1, zero_smul, one_smul, add_zero] using
          hx.2 (by simpa only [hb0, ha1, zero_smul, one_smul, add_zero] using hz)
      rw [he] at hz
      have hfx : f x = 0 := by
        have hby := mul_nonpos_of_nonneg_of_nonpos hb hy.1
        have hax : a * f x = 0 := le_antisymm
          (mul_nonpos_of_nonneg_of_nonpos ha hx.1) (by linarith only [hz, hby])
        exact (mul_eq_zero.mp hax).resolve_left ha0
      have hfy : f y = 0 := by
        have hax := mul_nonpos_of_nonneg_of_nonpos ha hx.1
        have hby : b * f y = 0 := le_antisymm
          (mul_nonpos_of_nonneg_of_nonpos hb hy.1) (by linarith only [hz, hax])
        exact (mul_eq_zero.mp hby).resolve_left hb0
      exact (convex_convexHull ℝ _) (hx.2 hfx) (hy.2 hfy) ha hb hab
  have hST : S ⊆ T := fun x hx =>
    ⟨hS x hx, fun hz => subset_convexHull ℝ _ ⟨hx, hz⟩⟩
  apply Subset.antisymm
  · intro x hx
    exact (convexHull_min hST hT hx.1).2 hx.2
  · apply convexHull_min
    · intro x hx
      exact ⟨subset_convexHull ℝ S hx.1, hx.2⟩
    · apply (convex_convexHull ℝ S).inter
      intro x hx y hy a b _ _ _
      change f x = 0 at hx
      change f y = 0 at hy
      change f (a • x + b • y) = 0
      simp [map_add, map_smul, hx, hy]

/-- The three original ordered endpoints on cap i. -/
def cap3vertex (l : Fin 6 → ℝ) (i : Fin 4) : Set V :=
  {v | ∃ j, j ≠ i ∧ endpoint l i j = v}

/-- The six original ordered endpoints avoiding i. -/
def side6vertex (l : Fin 6 → ℝ) (i : Fin 4) : Set V :=
  {v | ∃ j k, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧ endpoint l j k = v}

/-- Full support slice, not merely inclusion of the three corners. -/
theorem cap3vertex_affine_face (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (i : Fin 4) :
    cutBody l ∩ {v | (∑ j, lengthGram l i j * v j) = 0} =
      convexHull ℝ (cap3vertex l i) := by
  let S := range (fun p : EndpointLabel => endpoint l p.val.1 p.val.2)
  let f : V →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ j, lengthGram l i j * v j
      map_add' := by intro v w; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        simp [Finset.mul_sum, mul_left_comm, mul_assoc] }
  obtain ⟨_, hhull, _, he⟩ := cut_body_polytope l hl
  have hS : ∀ v ∈ S, f v ≤ 0 := by
    rintro v ⟨p, rfl⟩
    exact (he p.val.1 p.val.2 p.property).1.2 i
  have hs : S ∩ {v | f v = 0} = cap3vertex l i := by
    ext v
    constructor
    · rintro ⟨⟨p, rfl⟩, hz⟩
      have hip : i = p.val.1 := by
        by_contra hn
        exact (ne_of_lt ((he p.val.1 p.val.2 p.property).2.2.2.2.2 i hn)) hz
      exact ⟨p.val.2, by simpa only [hip] using p.property.symm,
        by rw [hip]⟩
    · rintro ⟨j, hji, rfl⟩
      exact ⟨⟨⟨(i,j), hji.symm⟩, rfl⟩, (he i j hji.symm).2.2.2.2.1⟩
  have h := convexHull_zero_support S f hS
  rw [hs] at h
  simpa only [S, hhull, f, LinearMap.coe_mk, AddHom.coe_mk] using h

/-- Full support slice, not merely inclusion of the six corners. -/
theorem side6vertex_affine_face (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (i : Fin 4) :
    cutBody l ∩ {v | v i = 0} = convexHull ℝ (side6vertex l i) := by
  let S := range (fun p : EndpointLabel => endpoint l p.val.1 p.val.2)
  let f : V →ₗ[ℝ] ℝ :=
    { toFun := fun v => -v i
      map_add' := by intro v w; simp [add_comm]
      map_smul' := by intro a v; simp }
  obtain ⟨_, hhull, _, he⟩ := cut_body_polytope l hl
  have hS : ∀ v ∈ S, f v ≤ 0 := by
    rintro v ⟨p, rfl⟩
    exact neg_nonpos.mpr ((he p.val.1 p.val.2 p.property).1.1.1 i)
  have hs : S ∩ {v | f v = 0} = side6vertex l i := by
    ext v
    constructor
    · rintro ⟨⟨p, rfl⟩, hz⟩
      have hz' : endpoint l p.val.1 p.val.2 i = 0 := neg_eq_zero.mp hz
      have hi : p.val.1 ≠ i := by
        intro h; rw [← h] at hz'
        exact (ne_of_gt (he p.val.1 p.val.2 p.property).2.1) hz'
      have hj : p.val.2 ≠ i := by
        intro h; rw [← h] at hz'
        exact (ne_of_gt (he p.val.1 p.val.2 p.property).2.2.1) hz'
      exact ⟨p.val.1, p.val.2, hi, hj, p.property, rfl⟩
    · rintro ⟨j, k, hji, hki, hjk, rfl⟩
      refine ⟨⟨⟨(j,k), hjk⟩, rfl⟩, ?_⟩
      change -endpoint l j k i = 0
      rw [(he j k hjk).2.2.2.1 i hji.symm hki.symm, neg_zero]
  have h := convexHull_zero_support S f hS
  rw [hs] at h
  simpa only [S, hhull, f, LinearMap.coe_mk, AddHom.coe_mk, neg_eq_zero] using h

/-- Only a binding of the inherited homeomorphism, rewriting actualLengths
back to the original six slots. No second body or frame is constructed. -/
private theorem forward_homeomorph_exists (l : Fin 6 → ℝ)
    (hl : ∀ k, 0 < l k) (hdet : (lengthGram l).det < 0) :
    ∃ h : cutBody l ≃ₜ (forward8halfspace l hl hdet).P,
      ∀ v, lift (h v).val = radial l v.val ᵥ*
        ((forward8halfspace l hl hdet).cap : Matrix (Fin 4) (Fin 4) ℝ) := by
  have hlen := (forward8halfspace_spec l hl hdet).2.2.2
  have h := native_body_exact_homeomorph (forward8halfspace l hl hdet)
  dsimp only at h
  rw [hlen] at h
  obtain ⟨h, hh, _, _, _⟩ := h
  exact ⟨h, hh⟩

noncomputable def forwardHomeomorph (l : Fin 6 → ℝ)
    (hl : ∀ k, 0 < l k) (hdet : (lengthGram l).det < 0) :
    cutBody l ≃ₜ (forward8halfspace l hl hdet).P :=
  Classical.choose (forward_homeomorph_exists l hl hdet)

def forwardRadial (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (v : cutBody l) : HyperbolicThreeSpace :=
  (forwardHomeomorph l hl hdet v).val

theorem forwardRadial_lift (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (v : cutBody l) :
    lift (forwardRadial l hl hdet v) = radial l v.val ᵥ*
      ((forward8halfspace l hl hdet).cap : Matrix (Fin 4) (Fin 4) ℝ) :=
  Classical.choose_spec (forward_homeomorph_exists l hl hdet) v

/-- Subtype restriction makes the radial map's domain explicit. Consumed by
both whole-facet equalities and the whole-segment equality below. -/
def radialImage (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (S : Set V) : Set HyperbolicThreeSpace :=
  forwardRadial l hl hdet '' {v : cutBody l | v.val ∈ S}

/-- Actual corners of the SAME forward object are the radial endpoints. -/
theorem forwardRadial_endpoint (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (i j : Fin 4) (hij : i ≠ j) :
    forwardRadial l hl hdet
      ⟨endpoint l i j, ((cut_body_polytope l hl).2.2.2 i j hij).1⟩ =
        (forward8halfspace l hl hdet).corner i j := by
  apply lift_injective
  rw [forwardRadial_lift]
  exact ((forward8halfspace_spec l hl hdet).2.2.1 i j hij).symm

/-- Exact support values at every radial point, including strict values. -/
private theorem radial_support_values (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (v : cutBody l) (i : Fin 4) :
    let d := forward8halfspace l hl hdet
    let r := Real.sqrt (-gramQuadratic l v.val)
    0 < r ∧ B (d.cap i) (lift (forwardRadial l hl hdet v)) =
      (∑ j, lengthGram l i j * v.val j) / r ∧
    B (d.side i) (lift (forwardRadial l hl hdet v)) =
      B (d.cap i) (d.side i) * (v.val i / r) ∧
    B (d.cap i) (d.side i) < 0 := by
  let d := forward8halfspace l hl hdet
  have hlen : actualLengths d = l := (forward8halfspace_spec l hl hdet).2.2.2
  obtain ⟨_, hbeta, hsupport⟩ := temporary_dual_support_conclusion d
  have hc := (hsupport (radial l v.val)).1 i
  have hs := (hsupport (radial l v.val)).2.1 i
  rw [hlen] at hc
  refine ⟨Real.sqrt_pos.mpr (neg_pos.mpr
    ((shared_radial_body l hl).2.2.2.1 v.val v.property)), ?_, ?_, hbeta i⟩
  · rw [forwardRadial_lift]
    change B (d.cap i) (radial l v.val ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) = _
    rw [hc]
    simp only [Matrix.mulVec, dotProduct, radial, mul_div_assoc, Finset.sum_div]
  · rw [forwardRadial_lift]
    exact hs

private theorem radial_support_zeros (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (v : cutBody l) (i : Fin 4) :
    let d := forward8halfspace l hl hdet
    (B (d.cap i) (lift (forwardRadial l hl hdet v)) = 0 ↔
      (∑ j, lengthGram l i j * v.val j) = 0) ∧
    (B (d.side i) (lift (forwardRadial l hl hdet v)) = 0 ↔ v.val i = 0) := by
  obtain ⟨hr, hc, hs, hb⟩ := radial_support_values l hl hdet v i
  constructor
  · rw [hc]
    simp only [div_eq_zero_iff, hr.ne', or_false]
  · rw [hs]
    simp only [mul_eq_zero, hb.ne, false_or, div_eq_zero_iff, hr.ne', or_false]

/-- Both original support-defined facets are images of their exact affine support slices
and of the convex hulls of precisely their original labeled endpoints. -/
theorem forward_full_facet_images (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (i : Fin 4) :
    let d := forward8halfspace l hl hdet
    (capFacet d.P d.cap i = radialImage l hl hdet
      (cutBody l ∩ {v | (∑ j, lengthGram l i j * v j) = 0})) ∧
    (capFacet d.P d.cap i = radialImage l hl hdet (convexHull ℝ (cap3vertex l i))) ∧
    (sideFacet d.P d.side i = radialImage l hl hdet
      (cutBody l ∩ {v | v i = 0})) ∧
    (sideFacet d.P d.side i = radialImage l hl hdet (convexHull ℝ (side6vertex l i))) := by
  let d := forward8halfspace l hl hdet
  let h := forwardHomeomorph l hl hdet
  have hc : capFacet d.P d.cap i = radialImage l hl hdet
      (cutBody l ∩ {v | (∑ j, lengthGram l i j * v j) = 0}) := by
    ext p
    constructor
    · rintro ⟨hp, hz⟩
      let v := h.symm ⟨p, hp⟩
      have hv : forwardRadial l hl hdet v = p :=
        congrArg Subtype.val (h.apply_symm_apply ⟨p, hp⟩)
      refine ⟨v, ⟨v.property, ?_⟩, hv⟩
      exact (radial_support_zeros l hl hdet v i).1.mp (by rw [hv]; exact hz)
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(h v).property, (radial_support_zeros l hl hdet v i).1.mpr hv.2⟩
  have hs : sideFacet d.P d.side i = radialImage l hl hdet
      (cutBody l ∩ {v | v i = 0}) := by
    ext p
    constructor
    · rintro ⟨hp, hz⟩
      let v := h.symm ⟨p, hp⟩
      have hv : forwardRadial l hl hdet v = p :=
        congrArg Subtype.val (h.apply_symm_apply ⟨p, hp⟩)
      refine ⟨v, ⟨v.property, ?_⟩, hv⟩
      exact (radial_support_zeros l hl hdet v i).2.mp (by rw [hv]; exact hz)
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(h v).property, (radial_support_zeros l hl hdet v i).2.mpr hv.2⟩
  exact ⟨hc, by rw [hc, cap3vertex_affine_face l hl i],
    hs, by rw [hs, side6vertex_affine_face l hl i]⟩

/-- Literal full ambient distance-between set in the actual H3 metric. -/
def metricBetween (p q : HyperbolicThreeSpace) : Set HyperbolicThreeSpace :=
  {z | dist p z + dist z q = dist p q}

/-- Closure under every ambient point satisfying distance additivity. -/
def FullMetricSegmentConvex (P : Set HyperbolicThreeSpace) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, metricBetween p q ⊆ P

/-- Coordinate recovery only: supplies the public theorem's frame contract.
No hyperbolic interpolation, distance calculation or geodesic proof occurs. -/
private theorem coordinates_from_lift (p : HyperbolicThreeSpace) :
    p.coordinates.val = WithLp.toLp 2
      (Complex.mk (lift p 0 / (lift p 3-lift p 2))
        (lift p 1 / (lift p 3-lift p 2)), 1/(lift p 3-lift p 2)) := by
  have he : project (lift p) (lift_unit p) (lift_time p) = p := by
    apply lift_injective
    exact lift_of_coordinates _ _ (lift_unit p) (lift_time p) rfl
  exact (congrArg (fun q : HyperbolicThreeSpace => q.coordinates.val) he).symm

/-- Direct consumption of same_body_metric_segments, with both range
identities retained. This is bind-only and adds no segment mathematics. -/
theorem forward_metric_segments (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (v w : cutBody l) :
    ∃ gamma : Icc (0 : ℝ)
        (dist (forwardRadial l hl hdet v) (forwardRadial l hl hdet w)) →
        HyperbolicThreeSpace,
      Isometry gamma ∧
      gamma ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = forwardRadial l hl hdet v ∧
      gamma ⟨dist (forwardRadial l hl hdet v) (forwardRadial l hl hdet w),
        ⟨dist_nonneg, le_rfl⟩⟩ = forwardRadial l hl hdet w ∧
      range gamma = radialImage l hl hdet (segment ℝ v.val w.val) ∧
      range gamma = metricBetween (forwardRadial l hl hdet v) (forwardRadial l hl hdet w) := by
  have hinj : Function.Injective (forwardRadial l hl hdet) := by
    intro v w h
    exact (forwardHomeomorph l hl hdet).injective (Subtype.ext h)
  have hframe (v : cutBody l) : ∃ y : V,
      y = radial l v.val ᵥ* ((forward8halfspace l hl hdet).cap : Matrix (Fin 4) (Fin 4) ℝ) ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (forwardRadial l hl hdet v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)) :=
    ⟨lift (forwardRadial l hl hdet v), forwardRadial_lift l hl hdet v,
      lift_unit _, lift_time _, coordinates_from_lift _⟩
  obtain ⟨gamma, hiso, h0, h1, himage, hbetween⟩ :=
    D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.same_body_metric_segments
      l hl (forward8halfspace l hl hdet).cap (forwardRadial l hl hdet) hinj hframe v w
  exact ⟨gamma, hiso, h0, h1, by simpa only [radialImage, Set.image, Set.mem_setOf_eq] using himage,
    hbetween⟩

/-- The entire affine segment, including coincident endpoints, has exactly
the full ambient distance-between set as image. A supplier consequence. -/
theorem forward_whole_segment_image (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (v w : cutBody l) :
    radialImage l hl hdet (segment ℝ v.val w.val) =
      metricBetween (forwardRadial l hl hdet v) (forwardRadial l hl hdet w) := by
  obtain ⟨_, _, _, _, himage, hbetween⟩ := forward_metric_segments l hl hdet v w
  exact himage.symm.trans hbetween

/-- Exact consumer: arbitrary affine convex subsets transport to full
ambient metric-segment convex subsets of the SAME body. -/
theorem radialImage_full_metric_convex (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (S : Set V) (hS : Convex ℝ S) :
    FullMetricSegmentConvex (radialImage l hl hdet S) := by
  rintro p ⟨v, hv, rfl⟩ q ⟨w, hw, rfl⟩ z hz
  rw [← forward_whole_segment_image l hl hdet v w] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact ⟨u, hS.segment_subset hv hw hu, rfl⟩

/-- Full metric convexity of the original P and of all eight full facets. -/
theorem forward_body_and_facets_metric_convex (l : Fin 6 → ℝ)
    (hl : ∀ k, 0 < l k) (hdet : (lengthGram l).det < 0) :
    let d := forward8halfspace l hl hdet
    FullMetricSegmentConvex d.P ∧
      (∀ i, FullMetricSegmentConvex (capFacet d.P d.cap i)) ∧
      (∀ i, FullMetricSegmentConvex (sideFacet d.P d.side i)) := by
  let d := forward8halfspace l hl hdet
  have hrange : radialImage l hl hdet (cutBody l) = d.P := by
    ext p
    constructor
    · rintro ⟨v, _, rfl⟩
      exact (forwardHomeomorph l hl hdet v).property
    · intro hp
      let v := (forwardHomeomorph l hl hdet).symm ⟨p, hp⟩
      exact ⟨v, v.property,
        congrArg Subtype.val ((forwardHomeomorph l hl hdet).apply_symm_apply ⟨p, hp⟩)⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← hrange]
    apply radialImage_full_metric_convex
    rw [← (cut_body_polytope l hl).2.1]
    exact convex_convexHull ℝ _
  · intro i
    rw [(forward_full_facet_images l hl hdet i).2.1]
    exact radialImage_full_metric_convex l hl hdet _ (convex_convexHull ℝ _)
  · intro i
    rw [(forward_full_facet_images l hl hdet i).2.2.2]
    exact radialImage_full_metric_convex l hl hdet _ (convex_convexHull ℝ _)

/-- The generator images themselves are exactly the marked actual corners.
This consumes the endpoint identification, without claiming a metric hull. -/
theorem forward_facet_generators (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (i : Fin 4) :
    let d := forward8halfspace l hl hdet
    (radialImage l hl hdet (cap3vertex l i) =
      {p | ∃ j, j ≠ i ∧ d.corner i j = p}) ∧
    (radialImage l hl hdet (side6vertex l i) =
      {p | ∃ j k, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧ d.corner j k = p}) := by
  have he := (cut_body_polytope l hl).2.2.2
  constructor
  · ext p
    constructor
    · rintro ⟨v, ⟨j, hji, hv⟩, rfl⟩
      refine ⟨j, hji, ?_⟩
      rw [← forwardRadial_endpoint l hl hdet i j hji.symm]
      exact congrArg (forwardRadial l hl hdet) (Subtype.ext hv)
    · rintro ⟨j, hji, rfl⟩
      exact ⟨⟨endpoint l i j, (he i j hji.symm).1⟩, ⟨j, hji, rfl⟩,
        forwardRadial_endpoint l hl hdet i j hji.symm⟩
  · ext p
    constructor
    · rintro ⟨v, ⟨j, k, hji, hki, hjk, hv⟩, rfl⟩
      refine ⟨j, k, hji, hki, hjk, ?_⟩
      rw [← forwardRadial_endpoint l hl hdet j k hjk]
      exact congrArg (forwardRadial l hl hdet) (Subtype.ext hv)
    · rintro ⟨j, k, hji, hki, hjk, rfl⟩
      exact ⟨⟨endpoint l j k, (he j k hjk).1⟩, ⟨j, k, hji, hki, hjk, rfl⟩,
        forwardRadial_endpoint l hl hdet j k hjk⟩

/-- Continuity in actual H3 topology, through the existing coordinate
homeomorphism and the positive-height rational lift. -/
private theorem continuous_actual_lift : Continuous lift := by
  have hc : Continuous (fun p : HyperbolicThreeSpace => WithLp.ofLp p.coordinates.val) :=
    (WithLp.prod_continuous_ofLp 2 ℂ ℝ).comp
      (continuous_subtype_val.comp coordinatesHomeomorph.continuous)
  have hx : Continuous (fun p : HyperbolicThreeSpace => p.coordinates.val.fst.re) :=
    Complex.continuous_re.comp hc.fst
  have hy : Continuous (fun p : HyperbolicThreeSpace => p.coordinates.val.fst.im) :=
    Complex.continuous_im.comp hc.fst
  have hh : Continuous (fun p : HyperbolicThreeSpace => height p.coordinates) := hc.snd
  have hh0 (p : HyperbolicThreeSpace) : height p.coordinates ≠ 0 :=
    p.coordinates.property.ne'
  apply continuous_pi
  intro k
  fin_cases k
  · exact hx.div hh hh0
  · exact hy.div hh hh0
  · change Continuous (fun p : HyperbolicThreeSpace =>
      (p.coordinates.val.fst.re^2 + p.coordinates.val.fst.im^2 +
        (height p.coordinates)^2 - 1) / (2 * height p.coordinates))
    exact ((((hx.pow 2).add (hy.pow 2)).add (hh.pow 2)).sub continuous_const).div
      (continuous_const.mul hh) (fun p => mul_ne_zero (by norm_num) (hh0 p))
  · change Continuous (fun p : HyperbolicThreeSpace =>
      (p.coordinates.val.fst.re^2 + p.coordinates.val.fst.im^2 +
        (height p.coordinates)^2 + 1) / (2 * height p.coordinates))
    exact ((((hx.pow 2).add (hy.pow 2)).add (hh.pow 2)).add continuous_const).div
      (continuous_const.mul hh) (fun p => mul_ne_zero (by norm_num) (hh0 p))

private theorem continuous_actual_support (n : V) :
    Continuous (fun p : HyperbolicThreeSpace => B n (lift p)) := by
  have hf : Continuous (fun v : V => B n v) := by
    simp only [B_apply, lorentz]
    fun_prop
  exact hf.comp continuous_actual_lift

/-- An explicit strict witness for all eight actual supports, with an OPEN
H3 neighborhood contained in the original P. This is ambient interior,
not only relative interior in the affine coefficient simplex. -/
theorem forward_strict_barycenter (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) :
    let d := forward8halfspace l hl hdet
    let b : cutBody l := ⟨fun _ => (1 : ℝ)/4, (shared_radial_body l hl).2.1⟩
    let p := forwardRadial l hl hdet b
    p ∈ interior d.P ∧
      (∀ i, B (d.cap i) (lift p) < 0) ∧
      (∀ i, B (d.side i) (lift p) < 0) := by
  let d := forward8halfspace l hl hdet
  let b : cutBody l := ⟨fun _ => (1 : ℝ)/4, (shared_radial_body l hl).2.1⟩
  let p := forwardRadial l hl hdet b
  have hcap (i : Fin 4) : B (d.cap i) (lift p) < 0 := by
    obtain ⟨hr, hc, _, _⟩ := radial_support_values l hl hdet b i
    rw [hc]
    exact div_neg_of_neg_of_pos ((shared_radial_body l hl).2.2.1 i) hr
  have hside (i : Fin 4) : B (d.side i) (lift p) < 0 := by
    obtain ⟨hr, _, hs, hb⟩ := radial_support_values l hl hdet b i
    rw [hs]
    exact mul_neg_of_neg_of_pos hb (div_pos (by norm_num [b]) hr)
  let U : Set HyperbolicThreeSpace :=
    (⋂ i : Fin 4, {q | B (d.cap i) (lift q) < 0}) ∩
    (⋂ i : Fin 4, {q | B (d.side i) (lift q) < 0})
  have hU : IsOpen U :=
    (isOpen_iInter_of_finite (fun i =>
      isOpen_lt (continuous_actual_support (d.cap i)) continuous_const)).inter
    (isOpen_iInter_of_finite (fun i =>
      isOpen_lt (continuous_actual_support (d.side i)) continuous_const))
  have hUP : U ⊆ d.P := by
    intro q hq
    rw [d.body_halfspaces]
    exact ⟨fun i => (Set.mem_iInter.mp hq.1 i).le,
      fun i => (Set.mem_iInter.mp hq.2 i).le⟩
  have hpU : p ∈ U := ⟨Set.mem_iInter.mpr hcap, Set.mem_iInter.mpr hside⟩
  exact ⟨interior_maximal hUP hU hpU, hcap, hside⟩

/-- Direct consequence of the displayed ambient strict witness. -/
theorem forward_interior_nonempty (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) :
    (interior (forward8halfspace l hl hdet).P).Nonempty :=
  ⟨_, (forward_strict_barycenter l hl hdet).1⟩

/-- Exact support witnesses and properness for every one of the eight full
facets. The strict barycenter witnesses exclusion; marked corners witness
nonemptiness. This does not assert relative-plane dimension or polygon type. -/
theorem forward_facets_nonempty_proper (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (i : Fin 4) :
    let d := forward8halfspace l hl hdet
    (capFacet d.P d.cap i).Nonempty ∧ capFacet d.P d.cap i ⊂ d.P ∧
    (sideFacet d.P d.side i).Nonempty ∧ sideFacet d.P d.side i ⊂ d.P := by
  let d := forward8halfspace l hl hdet
  obtain ⟨j, hji⟩ : ∃ j : Fin 4, j ≠ i := by fin_cases i <;> decide
  obtain ⟨k, m, hki, hmi, hkm⟩ :
      ∃ k m : Fin 4, k ≠ i ∧ m ≠ i ∧ k ≠ m := by fin_cases i <;> decide
  let b : cutBody l := ⟨fun _ => (1 : ℝ)/4, (shared_radial_body l hl).2.1⟩
  let p := forwardRadial l hl hdet b
  have hp := forward_strict_barycenter l hl hdet
  have hpP : p ∈ d.P := interior_subset hp.1
  refine ⟨⟨d.corner i j, (d.cap_incidence i j hji.symm i).mpr rfl⟩, ?_,
    ⟨d.corner k m, (d.side_incidence k m hkm i).mpr ⟨hki.symm, hmi.symm⟩⟩, ?_⟩
  · apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨fun _ h => h.1, ?_⟩
    intro heq
    have hm : p ∈ capFacet d.P d.cap i := heq.symm ▸ hpP
    exact (ne_of_lt (hp.2.1 i)) hm.2
  · apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨fun _ h => h.1, ?_⟩
    intro heq
    have hm : p ∈ sideFacet d.P d.side i := heq.symm ▸ hpP
    exact (ne_of_lt (hp.2.2 i)) hm.2

/- Residual interfaces intentionally not asserted:
(1) metric-geodesic convex-hull minimality/transport for the three/six actual
    corner sets (full segment convexity and exact affine hull images above
    do not silently supply that named hull interface);
(2) relative support-plane interior, affine dimension two, cyclic edge
    boundary and conventional hyperbolic triangle/hexagon recognition;
(3) native tangent/metric normal compatibility, actual right angles,
    diffeomorphic truncated-tetrahedron type and full native recognition.
Canonical retention of every declaration remains undecided. -/
end NativeFacets
end NativeCornerExtractionSource

#check @NativeCornerExtractionSource.NativeFacets.convexHull_zero_support
#check @NativeCornerExtractionSource.NativeFacets.cap3vertex
#check @NativeCornerExtractionSource.NativeFacets.side6vertex
#check @NativeCornerExtractionSource.NativeFacets.cap3vertex_affine_face
#check @NativeCornerExtractionSource.NativeFacets.side6vertex_affine_face
#check @NativeCornerExtractionSource.NativeFacets.forwardHomeomorph
#check @NativeCornerExtractionSource.NativeFacets.forwardRadial
#check @NativeCornerExtractionSource.NativeFacets.forwardRadial_lift
#check @NativeCornerExtractionSource.NativeFacets.radialImage
#check @NativeCornerExtractionSource.NativeFacets.forwardRadial_endpoint
#check @NativeCornerExtractionSource.NativeFacets.forward_full_facet_images
#check @NativeCornerExtractionSource.NativeFacets.metricBetween
#check @NativeCornerExtractionSource.NativeFacets.FullMetricSegmentConvex
#check @NativeCornerExtractionSource.NativeFacets.forward_metric_segments
#check @NativeCornerExtractionSource.NativeFacets.forward_whole_segment_image
#check @NativeCornerExtractionSource.NativeFacets.radialImage_full_metric_convex
#check @NativeCornerExtractionSource.NativeFacets.forward_body_and_facets_metric_convex
#check @NativeCornerExtractionSource.NativeFacets.forward_facet_generators
#check @NativeCornerExtractionSource.NativeFacets.forward_strict_barycenter
#check @NativeCornerExtractionSource.NativeFacets.forward_interior_nonempty
#check @NativeCornerExtractionSource.NativeFacets.forward_facets_nonempty_proper
#print axioms NativeCornerExtractionSource.NativeFacets.convexHull_zero_support
#print axioms NativeCornerExtractionSource.NativeFacets.cap3vertex
#print axioms NativeCornerExtractionSource.NativeFacets.side6vertex
#print axioms NativeCornerExtractionSource.NativeFacets.cap3vertex_affine_face
#print axioms NativeCornerExtractionSource.NativeFacets.side6vertex_affine_face
#print axioms NativeCornerExtractionSource.NativeFacets.forwardHomeomorph
#print axioms NativeCornerExtractionSource.NativeFacets.forwardRadial
#print axioms NativeCornerExtractionSource.NativeFacets.forwardRadial_lift
#print axioms NativeCornerExtractionSource.NativeFacets.radialImage
#print axioms NativeCornerExtractionSource.NativeFacets.forwardRadial_endpoint
#print axioms NativeCornerExtractionSource.NativeFacets.forward_full_facet_images
#print axioms NativeCornerExtractionSource.NativeFacets.metricBetween
#print axioms NativeCornerExtractionSource.NativeFacets.FullMetricSegmentConvex
#print axioms NativeCornerExtractionSource.NativeFacets.forward_metric_segments
#print axioms NativeCornerExtractionSource.NativeFacets.forward_whole_segment_image
#print axioms NativeCornerExtractionSource.NativeFacets.radialImage_full_metric_convex
#print axioms NativeCornerExtractionSource.NativeFacets.forward_body_and_facets_metric_convex
#print axioms NativeCornerExtractionSource.NativeFacets.forward_facet_generators
#print axioms NativeCornerExtractionSource.NativeFacets.forward_strict_barycenter
#print axioms NativeCornerExtractionSource.NativeFacets.forward_interior_nonempty
#print axioms NativeCornerExtractionSource.NativeFacets.forward_facets_nonempty_proper
