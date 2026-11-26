/- GID: D5/S3/Quantum/Foundation/ActualExclusionBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ActualExclusionBoundary
   mirror-E: none(waiver:abstract-convex-geometric-construction)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Intrinsic]
   utility: none
   digest: Whole exclusions cover the actual boundary and detect its boundary midpoints. -/

import D5.S3.Quantum.Foundation.ExclusionBallFaces
import D5.S3.Quantum.Foundation.OriginalFacePolarity
import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Quantum.Foundation.MixedExclusionGeometry
import D5.S3.Topology.FiniteConvexFiberMap
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Ray
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Normalize
import D5.S3.Topology.TauCeti.AlgebraicTopology.Sphere.Contractible
import D5.S3.Topology.TauCeti.Analysis.Normed.Module.Normalize

/-! Relative-boundary geometry of the entire original normalized cone base. -/

noncomputable section
open Set Topology

namespace D5.S3.Quantum.Foundation.ActualExclusionBoundary

open CircuitBalancedConfirmation WeightedRelationConfirmation FacetZeroGluing
open WholePairBallConfirmation ExclusionBallFaces

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

private theorem exclusion_boundary
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) : exclusion C u p ⊆ intrinsicFrontier ℝ (base C u) := by
  exact MixedExclusionGeometry.exclusion_frontier hclosed hstrict hgen hB p

/-- With the original full effects and variable positive exclusion dimensions,
whole exclusions cover the entire actual relative boundary. Two base points
have a boundary midpoint exactly when they belong to one whole exclusion ball.
No repeated-label, Pair or quotient regularity assumption is used. -/
theorem original_boundary_cover_and_midpoint
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    (∀ x ∈ intrinsicFrontier ℝ (base C u), ∃ p : pure C u, x ∈ exclusion C u p) ∧
    ∀ x ∈ base C u, ∀ y ∈ base C u,
      midpoint ℝ x y ∈ intrinsicFrontier ℝ (base C u) ↔
        ∃ p : pure C u, x ∈ exclusion C u p ∧ y ∈ exclusion C u p := by
  have all := exclusion_ball_faces hclosed hstrict hgen hB
  have hcover : ∀ x ∈ intrinsicFrontier ℝ (base C u),
      ∃ p : pure C u, x ∈ exclusion C u p := by
    intro x hx
    exact MixedExclusionGeometry.frontier_covered hclosed hstrict hgen hx
  refine ⟨hcover, ?_⟩
  intro x hx y hy
  constructor
  · intro hm
    obtain ⟨p, hp⟩ := hcover _ hm
    have hseg : midpoint ℝ x y ∈ openSegment ℝ x y := midpoint_mem_openSegment x y
    have hf := (all.1 p).2.2.2.2.1
    exact ⟨p, hf.left_mem_of_mem_openSegment hx hy hp hseg,
      hf.right_mem_of_mem_openSegment hx hy hp hseg⟩
  · rintro ⟨p, hp, hq⟩
    exact exclusion_boundary hclosed hstrict hgen hB p
      ((all.1 p).2.2.1.midpoint_mem hp hq)

private theorem original_whole_balls_eq_of_two
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (a b : pure C u) {x y : V}
    (hx : x ∈ exclusion C u a ∩ exclusion C u b)
    (hy : y ∈ exclusion C u a ∩ exclusion C u b) (hxy : x ≠ y) :
    exclusion C u a = exclusion C u b := by
  exact SingleLabelNormalBody.equal_of_two_points hclosed hstrict hgen hB a b hxy hx hy

theorem repeated_ball_isolated
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p s : pure C u) (hps : p ≠ s) (hs : exclusion C u s = exclusion C u p)
    (q : pure C u) :
    exclusion C u p = exclusion C u q ∨ Disjoint (exclusion C u p) (exclusion C u q) := by
  classical
  have all := exclusion_ball_faces hclosed hstrict hgen hB
  have two := original_whole_balls_eq_of_two hclosed hstrict hgen hB
  by_cases he : exclusion C u p = exclusion C u q
  · exact Or.inl he
  right
  apply Set.disjoint_left.mpr
  intro x hxp hxq
  have hsingle : exclusion C u p ∩ exclusion C u q = {x} := by
    apply Set.Subsingleton.eq_singleton_of_mem (s := exclusion C u p ∩ exclusion C u q)
      _ (show x ∈ exclusion C u p ∩ exclusion C u q from ⟨hxp, hxq⟩)
    intro a ha b hb
    by_contra hab
    exact he (two p q ha hb hab)
  have hxP : x ∈ pure C u := by
    apply isExtreme_singleton.mp
    rw [← hsingle]
    exact (all.1 p).2.2.2.2.1.inter (all.1 q).2.2.2.2.1
  let r : pure C u := ⟨x, hxP⟩
  have hpr : (p : V) ∈ exclusion C u r := (exclusion_symmetric p r).mp hxp
  have hsr : (s : V) ∈ exclusion C u r := (exclusion_symmetric s r).mp (hs.symm ▸ hxp)
  have hqr : (q : V) ∈ exclusion C u r := (exclusion_symmetric q r).mp hxq
  have hpure : (exclusion C u p).extremePoints ℝ ⊆ exclusion C u q := by
    intro y hy
    have hyP : y ∈ pure C u := (all.1 p).2.2.2.2.1.extremePoints_subset_extremePoints hy
    let t : pure C u := ⟨y, hyP⟩
    have hpt : (p : V) ∈ exclusion C u t := (exclusion_symmetric p t).mp hy.1
    have hst : (s : V) ∈ exclusion C u t :=
      (exclusion_symmetric s t).mp (hs.symm ▸ hy.1)
    have htr : exclusion C u t = exclusion C u r :=
      two t r ⟨hpt, hpr⟩ ⟨hst, hsr⟩ (fun h => hps (Subtype.ext h))
    exact (exclusion_symmetric q t).mpr (htr.symm ▸ hqr)
  have hsub : exclusion C u p ⊆ exclusion C u q := by
    rw [← closure_convexHull_extremePoints (all.1 p).2.1 (all.1 p).2.2.1]
    exact closure_minimal (convexHull_min hpure (all.1 q).2.2.1) (all.1 q).2.1.isClosed
  exact he (chart_face_eq (hB q).some (all.1 p).2.2.1
    ((all.1 p).2.2.2.2.1.mono (all.1 q).2.2.2.2.1.subset hsub) (all.1 p).1)

/-- In the all-repeated contradiction branch, the literal midpoint relation on
all of the actual relative boundary is a closed equivalence relation. Its actual
quotient is compact Hausdorff, and the canonical projection is continuous,
surjective and closed. No regularity of the quotient is assumed. -/
theorem original_all_repeated_boundary_quotient
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hrepeated : ∀ p : pure C u, ∃ s : pure C u,
      p ≠ s ∧ exclusion C u s = exclusion C u p) :
    ∃ r : Setoid (intrinsicFrontier ℝ (base C u)),
      (∀ x y, r x y ↔ midpoint ℝ (x : V) (y : V) ∈ intrinsicFrontier ℝ (base C u)) ∧
      (∀ x y, r x y ↔ ∃ p : pure C u, (x : V) ∈ exclusion C u p ∧
        (y : V) ∈ exclusion C u p) ∧
      IsClosed {z : intrinsicFrontier ℝ (base C u) × intrinsicFrontier ℝ (base C u) |
        r z.1 z.2} ∧
      CompactSpace (Quotient r) ∧ T2Space (Quotient r) ∧
      Continuous (Quotient.mk r) ∧ Function.Surjective (Quotient.mk r) ∧
      IsClosedMap (Quotient.mk r) ∧
      ∀ b : Quotient r, ∃ p : pure C u,
        Subtype.val '' ((Quotient.mk r) ⁻¹' {b}) = exclusion C u p := by
  classical
  let S := intrinsicFrontier ℝ (base C u)
  have hSclosed : IsClosed S :=
    isClosed_intrinsicFrontier (affineSpan ℝ (base C u)).closed_of_finiteDimensional
  have hSK : S ⊆ base C u := intrinsicFrontier_subset (base_compact hclosed hstrict).isClosed
  have hScompact : IsCompact S := (base_compact hclosed hstrict).of_isClosed_subset hSclosed hSK
  let : CompactSpace S := isCompact_iff_compactSpace.mp hScompact
  have crit := (original_boundary_cover_and_midpoint hclosed hstrict hgen hB).2
  let r : Setoid S :=
    { r := fun x y => midpoint ℝ (x : V) (y : V) ∈ S
      iseqv := ⟨by intro x; simpa only [midpoint_self] using x.property,
        by intro x y h; simpa only [midpoint_comm] using h,
        by
          intro x y z hxy hyz
          obtain ⟨p, hxp, hyp⟩ := (crit x (hSK x.property) y (hSK y.property)).mp hxy
          obtain ⟨q, hyq, hzq⟩ := (crit y (hSK y.property) z (hSK z.property)).mp hyz
          obtain ⟨s, hps, hs⟩ := hrepeated p
          rcases repeated_ball_isolated hclosed hstrict hgen hB p s hps hs q with he | hd
          · exact (crit x (hSK x.property) z (hSK z.property)).mpr ⟨p, hxp, he.symm ▸ hzq⟩
          · exact ((Set.disjoint_left.mp hd) hyp hyq).elim⟩ }
  have hgraph : IsClosed {z : S × S | r z.1 z.2} := by
    apply hSclosed.preimage
    rw [show (fun z : S × S => midpoint ℝ (z.1 : V) (z.2 : V)) =
      (fun z => (1 / 2 : ℝ) • ((z.1 : V) + (z.2 : V))) by
        funext z; simp [midpoint_eq_smul_add, invOf_eq_inv]]
    exact ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)).const_smul _
  let q : S → Quotient r := Quotient.mk r
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  have hqclosed : IsClosedMap q := by
    intro F hF
    apply hq.isCoinducing.isClosed_preimage.mp
    have he : q ⁻¹' (q '' F) = Prod.snd ''
        ({z : S × S | r z.1 z.2} ∩ (F ×ˢ univ)) := by
      ext b
      constructor
      · rintro ⟨a, ha, hab⟩
        exact ⟨(a,b), ⟨Quotient.exact hab, ha, mem_univ b⟩, rfl⟩
      · rintro ⟨⟨a,c⟩, ⟨hac, ha, _⟩, rfl⟩
        exact ⟨a, ha, Quotient.sound hac⟩
    rw [he]
    exact isClosedMap_snd_of_compactSpace _ (hgraph.inter (hF.prod isClosed_univ))
  have hproper : IsProperMap q := by
    apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    refine ⟨hq.continuous, hqclosed, ?_⟩
    intro b
    obtain ⟨a, rfl⟩ := Quotient.exists_rep b
    have he : q ⁻¹' {q a} = {c | r a c} := by
      ext c
      simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
      exact ⟨fun h => Quotient.exact h.symm, fun h => (Quotient.sound h).symm⟩
    rw [he]
    exact (hgraph.preimage (continuous_const.prodMk continuous_id)).isCompact
  have hprod : IsQuotientMap (Prod.map q q) :=
    (hproper.prodMap hproper).isClosedMap.isQuotientMap
      (hq.continuous.prodMap hq.continuous) (hq.surjective.prodMap hq.surjective)
  have hT2 : T2Space (Quotient r) := by
    apply t2_iff_isClosed_diagonal.mpr
    apply hprod.isCoinducing.isClosed_preimage.mp
    convert hgraph using 1
    ext z
    exact Quotient.eq
  refine ⟨r, (by intros; rfl), ?_, hgraph, inferInstance, hT2,
    hq.continuous, hq.surjective, hqclosed, ?_⟩
  · intro x y
    exact crit x (hSK x.property) y (hSK y.property)
  · intro b
    obtain ⟨x, rfl⟩ := Quotient.exists_rep b
    obtain ⟨p, hxp⟩ := (original_boundary_cover_and_midpoint hclosed hstrict hgen hB).1
      x x.property
    refine ⟨p, ?_⟩
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hxz : r x z := Quotient.exact (mem_singleton_iff.mp hz).symm
      obtain ⟨a, hxa, hza⟩ := (crit x (hSK x.property) z (hSK z.property)).mp hxz
      obtain ⟨s, hps, hs⟩ := hrepeated p
      rcases repeated_ball_isolated hclosed hstrict hgen hB p s hps hs a with he | hd
      · exact he.symm ▸ hza
      · exact ((Set.disjoint_left.mp hd) hxp hxa).elim
    · intro hy
      let z : S := ⟨y, exclusion_boundary hclosed hstrict hgen hB p hy⟩
      have hxz : r x z := (crit x (hSK x.property) z (hSK z.property)).mpr ⟨p, hxp, hy⟩
      exact ⟨z, (Quotient.sound hxz).symm, rfl⟩

private theorem intrinsic_level_of_straddling {K : Set V} (hK : Convex ℝ K)
    (f : V →ₗ[ℝ] ℝ) {x y : V} (hx : x ∈ K) (hy : y ∈ K)
    {t : ℝ} (hxt : f x < t) (hty : t < f y) :
    ∃ z ∈ intrinsicInterior ℝ K, f z = t := by
  obtain ⟨c, hc⟩ := Set.Nonempty.intrinsicInterior hK ⟨x, hx⟩
  rcases lt_trichotomy (f c) t with hct | hct | htc
  · have ht : t ∈ f.toAffineMap '' openSegment ℝ c y := by
      rw [image_openSegment]
      exact Ioo_subset_openSegment ⟨hct, hty⟩
    obtain ⟨z, hz, he⟩ := ht
    exact ⟨z, hK.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      hc (subset_intrinsicClosure hy) hz, he⟩
  · exact ⟨c, hc, hct⟩
  · have ht : t ∈ f.toAffineMap '' openSegment ℝ x c := by
      rw [image_openSegment]
      exact Ioo_subset_openSegment ⟨hxt, htc⟩
    obtain ⟨z, hz, he⟩ := ht
    rw [openSegment_symm] at hz
    exact ⟨z, hK.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      hc (subset_intrinsicClosure hx) hz, he⟩

private theorem boundary_ray_unique {K : Set V} (hK : Convex ℝ K) (hclosed : IsClosed K)
    {c x y : V} (hc : c ∈ intrinsicInterior ℝ K)
    (hx : x ∈ intrinsicFrontier ℝ K) (hy : y ∈ intrinsicFrontier ℝ K)
    (hxy : SameRay ℝ (x - c) (y - c)) : x = y := by
  have hn (z : V) (hz : z ∈ intrinsicFrontier ℝ K) : z ≠ c := by
    intro he
    rw [← closure_sdiff_intrinsicInterior] at hz
    exact hz.2 (he ▸ hc)
  obtain ⟨a, ha, he⟩ := hxy.exists_pos_left (sub_ne_zero.mpr (hn x hx))
    (sub_ne_zero.mpr (hn y hy))
  have hnot (z : V) (hz : z ∈ intrinsicFrontier ℝ K) : z ∉ intrinsicInterior ℝ K := by
    rw [← closure_sdiff_intrinsicInterior] at hz
    exact hz.2
  rcases lt_trichotomy a 1 with ha1 | ha1 | h1a
  · have hyline : y = AffineMap.lineMap c x a := by
      rw [AffineMap.lineMap_apply_module', he]
      abel
    apply (hnot y hy).elim
    apply hK.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hc
      (subset_intrinsicClosure (intrinsicFrontier_subset hclosed hx))
    rw [hyline]
    exact lineMap_mem_openSegment (𝕜 := ℝ) c x (t := a) ⟨ha,ha1⟩
  · rw [ha1, one_smul] at he
    exact sub_left_injective he
  · have hxline : x = AffineMap.lineMap c y a⁻¹ := by
      rw [AffineMap.lineMap_apply_module', ← he, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
      abel
    apply (hnot x hx).elim
    apply hK.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hc
      (subset_intrinsicClosure (intrinsicFrontier_subset hclosed hy))
    rw [hxline]
    exact lineMap_mem_openSegment (𝕜 := ℝ) c y (t := a⁻¹)
      ⟨inv_pos.mpr ha, inv_lt_one_of_one_lt₀ h1a⟩

private theorem finite_shifted_fiber_controls
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (r : Setoid (intrinsicFrontier ℝ (base C u)))
    [CompactSpace (Quotient r)] [T2Space (Quotient r)]
    (hq : Continuous (Quotient.mk r)) (hqc : IsClosedMap (Quotient.mk r))
    (hfib : ∀ b : Quotient r, ∃ p : pure C u,
      Subtype.val '' ((Quotient.mk r) ⁻¹' {b}) = exclusion C u p)
    {c : V} (hc : c ∈ intrinsicInterior ℝ (base C u))
    (O : Set (Quotient r)) (hOo : IsOpen O) (R : Set V) (hR : IsClosed R)
    (hBR : ∀ b, b ∉ O → Disjoint
      ((fun z : V => z - c) '' (Subtype.val '' ((Quotient.mk r) ⁻¹' {b}))) R) :
    ∃ (n : ℕ) (W : Fin n → Set (Quotient r)) (N : Fin n → Set V),
      (∀ j, IsOpen (W j)) ∧ (∀ b, ∃ j, b ∈ W j) ∧
      (∀ j, Convex ℝ (N j)) ∧ (∀ j, (0 : V) ∉ N j) ∧
      (∀ j, Disjoint (N j) R ∨ W j ⊆ O) ∧
      ∀ j b, b ∈ W j → ∀ x : intrinsicFrontier ℝ (base C u),
        Quotient.mk r x = b → (x : V) - c ∈ N j := by
  classical
  let S := intrinsicFrontier ℝ (base C u)
  let q : S → Quotient r := Quotient.mk r
  let shift : V →ᵃ[ℝ] V := (AffineEquiv.vaddConst ℝ c).symm.toAffineMap
  let B (b : Quotient r) : Set V := shift '' (Subtype.val '' (q ⁻¹' {b}))
  have hSclosed : IsClosed S :=
    isClosed_intrinsicFrontier (affineSpan ℝ (base C u)).closed_of_finiteDimensional
  have hSK : S ⊆ base C u := intrinsicFrontier_subset (base_compact hclosed hstrict).isClosed
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    ((base_compact hclosed hstrict).of_isClosed_subset hSclosed hSK)
  have hBcompact (b) : IsCompact (B b) := by
    exact (((isClosed_singleton.preimage hq).isCompact).image continuous_subtype_val).image
      shift.continuous_of_finiteDimensional
  have hBconvex (b) : Convex ℝ (B b) := by
    obtain ⟨p, hp⟩ := hfib b
    dsimp [B]
    rw [hp]
    exact ((exclusion_ball_faces hclosed hstrict hgen hB).1 p).2.2.1.affine_image shift
  have hBzero (b) : (0 : V) ∉ B b := by
    rintro ⟨z, ⟨x, hx, rfl⟩, he⟩
    have he' : (x : V) = c := sub_eq_zero.mp he
    have hxS : c ∈ S := he' ▸ x.property
    change c ∈ intrinsicFrontier ℝ (base C u) at hxS
    rw [← closure_sdiff_intrinsicInterior] at hxS
    exact hxS.2 hc
  let T (b : Quotient r) : Set V := if b ∈ O then {0} else {0} ∪ R
  have neighborhoods (b : Quotient r) : ∃ N : Set V,
      IsOpen N ∧ Convex ℝ N ∧ Disjoint N (T b) ∧ B b ⊆ N := by
    have hT : IsClosed (T b) := by
      dsimp [T]
      split_ifs
      · exact isClosed_singleton
      · exact isClosed_singleton.union hR
    have hdis : Disjoint (B b) (T b) := by
      dsimp [T]
      split_ifs with hb
      · exact disjoint_singleton_right.mpr (hBzero b)
      · exact (disjoint_union_right).mpr
          ⟨disjoint_singleton_right.mpr (hBzero b), hBR b hb⟩
    obtain ⟨δ, hδ, hsub⟩ := (hBcompact b).exists_thickening_subset_open
      hT.isOpen_compl hdis.subset_compl_right
    exact ⟨Metric.thickening δ (B b), Metric.isOpen_thickening,
      (hBconvex b).thickening δ, Set.disjoint_left.mpr (fun z hz ht => hsub hz ht),
      Metric.self_subset_thickening hδ _⟩
  choose N hNo hNc hNT hBN using neighborhoods
  have hNz (b) : (0 : V) ∉ N b := by
    intro hz
    apply Set.disjoint_left.mp (hNT b) hz
    by_cases hb : b ∈ O <;> simp [T,hb]
  let W (b : Quotient r) : Set (Quotient r) :=
    (q '' {x : S | shift x ∉ N b})ᶜ ∩ (if b ∈ O then O else univ)
  have hWo (b) : IsOpen (W b) := by
    refine ((hqc _ ((hNo b).preimage
      (shift.continuous_of_finiteDimensional.comp continuous_subtype_val)).isClosed_compl).isOpen_compl).inter ?_
    split_ifs
    · exact hOo
    · exact isOpen_univ
  have hWcontrol (b d : Quotient r) (hd : d ∈ W b) (x : S) (hx : q x = d) :
      shift x ∈ N b := by
    by_contra hn
    exact hd.1 ⟨x, hn, hx⟩
  have hWself (b) : b ∈ W b := by
    refine ⟨?_, by by_cases hb : b ∈ O <;> simp [hb]⟩
    rintro ⟨x,hx,hxb⟩
    exact hx (hBN b ⟨x,⟨x,hxb,rfl⟩,rfl⟩)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover W hWo
    (by intro b _; exact mem_iUnion.mpr ⟨b,hWself b⟩)
  let e := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, (fun j => W (e j)), (fun j => N (e j)),
    (fun j => hWo _), ?_, (fun j => hNc _), (fun j => hNz _), ?_, ?_⟩
  · intro b
    obtain ⟨d, hd⟩ := mem_iUnion.mp (hs (mem_univ b))
    obtain ⟨hd,hbd⟩ := mem_iUnion.mp hd
    exact ⟨e.symm ⟨d,hd⟩, by simpa [e] using hbd⟩
  · intro j
    by_cases hb : (e j : Quotient r) ∈ O
    · exact Or.inr (fun d hd => by simpa [hb] using hd.2)
    · exact Or.inl ((hNT _).mono_right (by intro z hz; simp [T,hb,hz]))
  · intro j b hb x hx
    exact hWcontrol _ _ hb x hx

/-- Actual rational slices of the original boundary quotient. The open set is
chosen within closed crossing sets, so every one of its whole fibers has points
on both sides of the very same slice. -/
theorem original_all_repeated_rational_slice [Nontrivial V]
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hrepeated : ∀ p : pure C u, ∃ s : pure C u,
      p ≠ s ∧ exclusion C u s = exclusion C u p) :
    ∃ r : Setoid (intrinsicFrontier ℝ (base C u)),
      (∀ x y, r x y ↔ midpoint ℝ (x : V) (y : V) ∈ intrinsicFrontier ℝ (base C u)) ∧
      CompactSpace (Quotient r) ∧ T2Space (Quotient r) ∧
      Continuous (Quotient.mk r) ∧ IsClosedMap (Quotient.mk r) ∧
      (∀ b : Quotient r, ∃ p : pure C u,
        Subtype.val '' ((Quotient.mk r) ⁻¹' {b}) = exclusion C u p) ∧
      ∃ (f : V →ₗ[ℝ] ℝ) (t : ℚ) (O : Set (Quotient r)),
        f ≠ 0 ∧ IsOpen O ∧ O.Nonempty ∧
        (∃ c ∈ intrinsicInterior ℝ (base C u), f c = (t : ℝ) ∧
          ∃ v : intrinsicFrontier ℝ (base C u), Quotient.mk r v ∈ O ∧ (t : ℝ) < f v ∧
          ∃ (n : ℕ) (W : Fin n → Set (Quotient r)) (N : Fin n → Set V),
            (∀ j, IsOpen (W j)) ∧ (∀ b, ∃ j, b ∈ W j) ∧
            (∀ j, Convex ℝ (N j)) ∧ (∀ j, (0 : V) ∉ N j) ∧
            (∀ j, Disjoint (N j) {z | SameRay ℝ ((v : V) - c) z} ∨ W j ⊆ O) ∧
            (∀ j b, b ∈ W j → ∀ x : intrinsicFrontier ℝ (base C u),
              Quotient.mk r x = b → (x : V) - c ∈ N j) ∧
            ∃ A : C(Quotient r, V),
              (∀ b, A b ∈ (fun z : V => z - c) '' base C u) ∧
              (∀ b, ¬ SameRay ℝ ((v : V) - c) (A b)) ∧
              ∀ x : intrinsicFrontier ℝ (base C u),
                (0 : V) ∉ segment ℝ ((x : V) - c) (A (Quotient.mk r x))) ∧
        O ⊆ (Quotient.mk r) '' {x | f (x : V) = (t : ℝ)} ∧
        ∀ b ∈ O, ∃ x y : intrinsicFrontier ℝ (base C u),
          Quotient.mk r x = b ∧ Quotient.mk r y = b ∧
          f (x : V) < (t : ℝ) ∧ (t : ℝ) < f (y : V) := by
  classical
  obtain ⟨r, hr, _, _, hcompact, ht2, hq, _, hqc, hfib⟩ :=
    original_all_repeated_boundary_quotient hclosed hstrict hgen hB hrepeated
  let S := intrinsicFrontier ℝ (base C u)
  let q : S → Quotient r := Quotient.mk r
  let := hcompact
  let := ht2
  have hSclosed : IsClosed S :=
    isClosed_intrinsicFrontier (affineSpan ℝ (base C u)).closed_of_finiteDimensional
  have hSK : S ⊆ base C u := intrinsicFrontier_subset (base_compact hclosed hstrict).isClosed
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    ((base_compact hclosed hstrict).of_isClosed_subset hSclosed hSK)
  have hP : (pure C u).Nonempty := by
    by_contra hn
    have hh := pure_span (base_compact hclosed hstrict) hstrict hgen
    rw [Set.not_nonempty_iff_eq_empty.mp hn, Submodule.span_empty] at hh
    exact bot_ne_top hh
  obtain ⟨p₀, hp₀⟩ := hP
  obtain ⟨z₀, hz₀⟩ := ((exclusion_ball_faces hclosed hstrict hgen hB).1 ⟨p₀, hp₀⟩).1.nonempty
  let : Nonempty S := ⟨⟨z₀, exclusion_boundary hclosed hstrict hgen hB ⟨p₀,hp₀⟩ hz₀⟩⟩
  let : Nonempty (Quotient r) := ⟨q (Classical.choice inferInstance)⟩
  let e := (Module.finBasis ℝ V).equivFun
  let f (i : Fin (Module.finrank ℝ V)) : V →ₗ[ℝ] ℝ :=
    (LinearMap.proj i).comp e.toLinearMap
  let J := Fin (Module.finrank ℝ V) × ℚ × ℚ
  let F (j : J) : Set (Quotient r) :=
    if j.2.1 < j.2.2 then
      q '' {x : S | f j.1 x ≤ (j.2.1 : ℝ)} ∩
      q '' {x : S | (j.2.2 : ℝ) ≤ f j.1 x}
    else ∅
  have hFclosed (j : J) : IsClosed (F j) := by
    dsimp [F]
    split_ifs
    · exact (hqc _ (isClosed_le
        ((f j.1).continuous_of_finiteDimensional.comp continuous_subtype_val) continuous_const)).inter
        (hqc _ (isClosed_le continuous_const
        ((f j.1).continuous_of_finiteDimensional.comp continuous_subtype_val)))
    · exact isClosed_empty
  have hcover : ⋃ j, F j = univ := by
    apply eq_univ_of_forall
    intro b
    obtain ⟨p, hp⟩ := hfib b
    obtain ⟨x, hx, y, hy, hxy⟩ := ((exclusion_ball_faces hclosed hstrict hgen hB).1 p).1
    have hcoord : ∃ i, f i x ≠ f i y := by
      by_contra hn
      push Not at hn
      exact hxy (e.injective (funext hn))
    obtain ⟨i, hi⟩ := hcoord
    have across : ∃ x y : S, q x = b ∧ q y = b ∧ f i x < f i y := by
      obtain ⟨a, ha, hax⟩ := hp.symm ▸ hx
      obtain ⟨c, hc, hcy⟩ := hp.symm ▸ hy
      have ha' : q a = b := ha
      have hc' : q c = b := hc
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · exact ⟨a, c, ha', hc', by simpa [hax, hcy] using hlt⟩
      · exact ⟨c, a, hc', ha', by simpa [hax, hcy] using hgt⟩
    obtain ⟨a, c, ha, hc, hac⟩ := across
    obtain ⟨v, hav, hvc⟩ := exists_rat_btwn hac
    obtain ⟨w, hvw, hwc⟩ := exists_rat_btwn hvc
    have hvw' : v < w := by exact_mod_cast hvw
    apply mem_iUnion.mpr
    refine ⟨(i,v,w), ?_⟩
    simp only [F, hvw', ↓reduceIte]
    exact ⟨⟨a, hav.le, ha⟩, ⟨c, hwc.le, hc⟩⟩
  obtain ⟨j, hj⟩ := nonempty_interior_of_iUnion_of_closed hFclosed hcover
  have hab : j.2.1 < j.2.2 := by
    by_contra hn
    simp [F, hn] at hj
  have habR : (j.2.1 : ℝ) < (j.2.2 : ℝ) := by exact_mod_cast hab
  let t : ℚ := (j.2.1 + j.2.2) / 2
  have hat : (j.2.1 : ℝ) < (t : ℝ) := by dsimp [t]; push_cast; linarith
  have htb : (t : ℝ) < (j.2.2 : ℝ) := by dsimp [t]; push_cast; linarith
  have across (b : Quotient r) (hb : b ∈ interior (F j)) :
      ∃ x y : S, q x = b ∧ q y = b ∧ f j.1 x < (t : ℝ) ∧ (t : ℝ) < f j.1 y := by
    have hh := interior_subset hb
    simp only [F, hab, ↓reduceIte] at hh
    obtain ⟨⟨x, hx, hxb⟩, ⟨y, hy, hyb⟩⟩ := hh
    exact ⟨x,y,hxb,hyb,hx.trans_lt hat,htb.trans_le hy⟩
  have hjcopy := hj
  obtain ⟨b, hb⟩ := hjcopy
  obtain ⟨x,y,hxb,hyb,hx,hy⟩ := across b hb
  refine ⟨r, hr, hcompact, ht2, hq, hqc, hfib, f j.1, t, interior (F j),
    ?_, isOpen_interior, hj, ?_, ?_, across⟩
  · intro he
    have hx' := hx
    have hy' := hy
    rw [he] at hx' hy'
    simp only [LinearMap.zero_apply] at hx' hy'
    linarith
  · obtain ⟨c, hc, hct⟩ := intrinsic_level_of_straddling (base_convex C u) (f j.1)
      (hSK x.property) (hSK y.property) hx hy
    let R : Set V := {z | SameRay ℝ ((y : V) - c) z}
    have hR : IsClosed R := by
      simp only [R, sameRay_iff_norm_smul_eq]
      exact isClosed_eq (continuous_const.smul continuous_id) (continuous_norm.smul continuous_const)
    have hBR (d : Quotient r) (hd : d ∉ interior (F j)) : Disjoint
        ((fun z : V => z - c) '' (Subtype.val '' (q ⁻¹' {d}))) R := by
      apply Set.disjoint_left.mpr
      rintro z ⟨w,⟨a,ha,rfl⟩,rfl⟩ hz
      have he : (y : V) = (a : V) := boundary_ray_unique (base_convex C u)
        (base_compact hclosed hstrict).isClosed hc y.property a.property hz
      have hea : y = a := Subtype.ext he
      apply hd
      have hda : d = b := ha.symm.trans ((congrArg q hea).symm.trans hyb)
      exact hda.symm ▸ hb
    obtain ⟨n,W,N,hWo,hWcover,hNc,hNz,hNR,hcontrol⟩ :=
      finite_shifted_fiber_controls hclosed hstrict hgen hB r hq hqc hfib hc
        (interior (F j)) isOpen_interior R hR hBR
    have hslicerep (d : Quotient r) : ∃ a : S, q a = d ∧
        (d ∈ interior (F j) → f j.1 a = (t : ℝ)) := by
      by_cases hd : d ∈ interior (F j)
      · obtain ⟨x',y',hxd,hyd,hxt,hty⟩ := across d hd
        obtain ⟨p,hp⟩ := hfib d
        have hxD : (x' : V) ∈ exclusion C u p := hp ▸ ⟨x',hxd,rfl⟩
        have hyD : (y' : V) ∈ exclusion C u p := hp ▸ ⟨y',hyd,rfl⟩
        have ht : (t : ℝ) ∈ (f j.1).toAffineMap '' segment ℝ (x' : V) (y' : V) := by
          rw [image_segment]
          exact Icc_subset_segment ⟨hxt.le,hty.le⟩
        obtain ⟨z,hz,hzt⟩ := ht
        have hzD := ((exclusion_ball_faces hclosed hstrict hgen hB).1 p).2.2.1.segment_subset hxD hyD hz
        obtain ⟨a,ha,haz⟩ := hp.symm ▸ hzD
        exact ⟨a,ha,fun _ => by simpa [haz] using hzt⟩
      · obtain ⟨a,ha⟩ := Quotient.exists_rep d
        exact ⟨a,ha,fun h => (hd h).elim⟩
    choose a ha haL using hslicerep
    let B (d : Quotient r) : Set V :=
      (fun z : V => z - c) '' (Subtype.val '' (q ⁻¹' {d}))
    let shift : V →ᵃ[ℝ] V := (AffineEquiv.vaddConst ℝ c).symm.toAffineMap
    have hBK (d) : B d ⊆ shift '' base C u := by
      rintro z ⟨w,⟨a,ha,rfl⟩,rfl⟩
      exact ⟨a,hSK a.property,rfl⟩
    have hVN : ∀ k d, d ∈ W k → B d ⊆ N k := by
      rintro k d hd z ⟨w,⟨a,ha,rfl⟩,rfl⟩
      exact hcontrol k d hd a ha
    have hLR : {z : V | f j.1 z = 0} ∩ R ⊆ {0} := by
      rintro z ⟨hzL,hzR⟩
      change f j.1 z = 0 at hzL
      have he := congrArg (f j.1) (sameRay_iff_norm_smul_eq.mp hzR)
      simp only [map_smul, smul_eq_mul, hzL, mul_zero] at he
      have hvpos : 0 < f j.1 ((y : V) - c) := by rw [map_sub,hct]; linarith
      have hn : ‖z‖ = 0 := (mul_eq_zero.mp he.symm).resolve_right hvpos.ne'
      exact mem_singleton_iff.mpr (norm_eq_zero.mp hn)
    obtain ⟨A,hAK,hAR,hseg⟩ :=
      _root_.D5.S3.Topology.FiniteConvexFiberMap.exists_continuous_ray_avoiding_fiber_map
        W hWo hWcover B N (shift '' base C u) {z : V | f j.1 z = 0} R (interior (F j))
        ((base_convex C u).affine_image shift) ((convex_singleton (0 : ℝ)).linear_preimage (f j.1))
        hNc hBK hVN hNz hNR hLR (fun d => (a d : V) - c)
        (fun d => ⟨a d,⟨a d,ha d,rfl⟩,rfl⟩)
        (by intro d hd; change f j.1 ((a d : V) - c) = 0; rw [map_sub,haL d hd,hct]; simp)
    refine ⟨c,hc,hct,y,(by change q y ∈ _; rw [hyb]; exact hb),hy,n,W,N,hWo,hWcover,hNc,hNz,hNR,hcontrol,A,hAK,hAR,?_⟩
    intro x
    exact hseg (q x) ((x : V) - c) ⟨x,⟨x,rfl,rfl⟩,rfl⟩
  · intro b hb
    obtain ⟨x,y,hxb,hyb,hx,hy⟩ := across b hb
    obtain ⟨p,hp⟩ := hfib b
    have hxD : (x : V) ∈ exclusion C u p := hp ▸ ⟨x,hxb,rfl⟩
    have hyD : (y : V) ∈ exclusion C u p := hp ▸ ⟨y,hyb,rfl⟩
    have ht : (t : ℝ) ∈ (f j.1).toAffineMap '' segment ℝ (x : V) (y : V) := by
      rw [image_segment]
      exact Icc_subset_segment ⟨hx.le,hy.le⟩
    obtain ⟨z,hz,hzt⟩ := ht
    have hzD := ((exclusion_ball_faces hclosed hstrict hgen hB).1 p).2.2.1.segment_subset hxD hyD hz
    obtain ⟨a,ha,haz⟩ := hp.symm ▸ hzD
    exact ⟨a, by simpa [haz] using hzt, ha⟩


/-- In the all-repeated branch the entire original boundary admits a zero-free
homotopy in its actual affine direction space, from its translate by an actual
relative interior point to the opposite of an actual boundary direction. -/
theorem original_all_repeated_zero_free_homotopy [Nontrivial V]
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hrepeated : ∀ p : pure C u, ∃ s : pure C u,
      p ≠ s ∧ exclusion C u s = exclusion C u p) :
    let E := (affineSpan ℝ (base C u)).direction
    ∃ c ∈ intrinsicInterior ℝ (base C u),
      ∃ v : intrinsicFrontier ℝ (base C u),
        Nontrivial E ∧ ∃ H : C(unitInterval × intrinsicFrontier ℝ (base C u), E),
          (∀ x, (H (0, x) : V) = (x : V) - c) ∧
          (∀ x, (H (1, x) : V) = c - (v : V)) ∧
          ∀ z, H z ≠ 0 := by
  classical
  obtain ⟨r, _, _, _, hq, _, _, f, t, O, _, _, _,
    ⟨c, hc, _, v, _, _, n, W, N, _, _, _, _, _, _, A, hAK, hAR, hseg⟩, _, _⟩ :=
    original_all_repeated_rational_slice hclosed hstrict hgen hB hrepeated
  let K := base C u
  let S := intrinsicFrontier ℝ K
  let E := (affineSpan ℝ K).direction
  have hKclosed : IsClosed K := (base_compact hclosed hstrict).isClosed
  have hSK : S ⊆ K := intrinsicFrontier_subset hKclosed
  have hcK : c ∈ K := intrinsicInterior_subset hc
  have hca : c ∈ affineSpan ℝ K := subset_affineSpan ℝ K hcK
  have hnz (x : S) : (x : V) - c ≠ 0 := by
    intro heq
    have hx : (x : V) = c := sub_eq_zero.mp heq
    have hdis := intrinsicClosure_sdiff_intrinsicInterior (𝕜 := ℝ) K
    have hb : c ∈ intrinsicFrontier ℝ K := hx ▸ x.property
    rw [← hdis] at hb
    exact hb.2 hc
  let d : S → E := fun x => ⟨(x : V) - c,
    (affineSpan ℝ K).vsub_mem_direction (subset_affineSpan ℝ K (hSK x.property)) hca⟩
  have hd : Continuous d := (continuous_subtype_val.sub continuous_const).subtype_mk _
  let a : S → E := fun x => ⟨A (Quotient.mk r x), by
    obtain ⟨y, hy, he⟩ := hAK (Quotient.mk r x)
    rw [← he]
    exact (affineSpan ℝ K).vsub_mem_direction (subset_affineSpan ℝ K hy) hca⟩
  have ha : Continuous a := (A.continuous.comp hq).subtype_mk _
  let w : E := -d v
  have hw : w ≠ 0 := by
    intro hh
    have he := congrArg (fun z : E => (z : V)) hh
    exact hnz v (sub_eq_zero.mpr (sub_eq_zero.mp (by simpa [w, d] using he)).symm)
  have ha0 (x : S) : a x ≠ 0 := by
    intro hh
    apply hAR (Quotient.mk r x)
    have he := congrArg (fun z : E => (z : V)) hh
    change A (Quotient.mk r x) = 0 at he
    rw [he]
    exact SameRay.zero_right _
  have hsecond (x : S) : (0 : V) ∉ segment ℝ (a x : V) (w : V) := by
    intro hh
    have hray := (mem_segment_iff_sameRay.mp hh).symm
    apply hAR (Quotient.mk r x)
    simpa only [zero_sub, sub_zero, w, d, Submodule.coe_neg,
      Submodule.coe_mk, sameRay_neg_iff] using hray
  let P := {z : E // z ≠ 0}
  let dP : C(S, P) := ⟨fun x => ⟨d x, fun h => hnz x (congrArg Subtype.val h)⟩,
    hd.subtype_mk _⟩
  let aP : C(S, P) := ⟨fun x => ⟨a x, ha0 x⟩, ha.subtype_mk _⟩
  let wP : P := ⟨w, hw⟩
  let line (b e : S → E) (z : unitInterval × S) : E :=
    (1 - (z.1 : ℝ)) • b z.2 + (z.1 : ℝ) • e z.2
  have hline (b e : S → E) (hb : Continuous b) (he : Continuous e) :
      Continuous (line b e) := by dsimp [line]; fun_prop
  have hfirst0 (z : unitInterval × S) : line d a z ≠ 0 := by
    intro hh
    apply hseg z.2
    have he := congrArg (fun z : E => (z : V)) hh
    simp only [Submodule.coe_zero] at he
    rw [← he]
    exact ⟨1 - (z.1 : ℝ), (z.1 : ℝ), sub_nonneg.mpr z.1.property.2,
      z.1.property.1, sub_add_cancel _ _, rfl⟩
  have hsecond0 (z : unitInterval × S) : line a (fun _ => w) z ≠ 0 := by
    intro hh
    apply hsecond z.2
    have he := congrArg (fun z : E => (z : V)) hh
    simp only [Submodule.coe_zero] at he
    rw [← he]
    exact ⟨1 - (z.1 : ℝ), (z.1 : ℝ), sub_nonneg.mpr z.1.property.2,
      z.1.property.1, sub_add_cancel _ _, rfl⟩
  let H₁ : dP.Homotopy aP :=
    { toFun := fun z => ⟨line d a z, hfirst0 z⟩
      continuous_toFun := (hline d a hd ha).subtype_mk _
      map_zero_left := by intro x; apply Subtype.ext; simp [line, dP, aP]
      map_one_left := by intro x; apply Subtype.ext; simp [line, dP, aP] }
  let H₂ : aP.Homotopy (ContinuousMap.const S wP) :=
    { toFun := fun z => ⟨line a (fun _ => w) z, hsecond0 z⟩
      continuous_toFun := (hline a (fun _ => w) ha continuous_const).subtype_mk _
      map_zero_left := by intro x; apply Subtype.ext; simp [line, aP]
      map_one_left := by intro x; apply Subtype.ext; simp [line, wP] }
  let H := H₁.trans H₂
  have hnontrivial : Nontrivial E := ⟨⟨w, 0, hw⟩⟩
  refine ⟨c, hc, v, hnontrivial,
    ⟨fun z => (H z : E), continuous_subtype_val.comp H.continuous⟩, ?_, ?_, ?_⟩
  · intro x
    have hh := congrArg (fun z : P => ((z : E) : V)) (H.map_zero_left x)
    exact hh
  · intro x
    have hh := congrArg (fun z : P => ((z : E) : V)) (H.map_one_left x)
    simpa [wP, w, d] using hh
  · intro z
    exact (H z).property


/-- Some original whole exclusion has exactly one label in the entire original
pure-state domain. -/
theorem original_singleton_label_exists [Nontrivial V]
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    ∃ p : pure C u, ∀ q : pure C u, exclusion C u q = exclusion C u p → q = p := by
  classical
  by_contra hn
  have hrepeated : ∀ p : pure C u, ∃ s : pure C u,
      p ≠ s ∧ exclusion C u s = exclusion C u p := by
    push Not at hn
    intro p
    obtain ⟨s, hs, hsp⟩ := hn p
    exact ⟨s, Ne.symm hsp, hs⟩
  obtain ⟨c, hc, v, hnontrivial, H, H0, H1, Hnz⟩ :=
    original_all_repeated_zero_free_homotopy hclosed hstrict hgen hB hrepeated
  let K := base C u
  let B := affineSpan ℝ K
  let E := B.direction
  letI : Nontrivial E := hnontrivial
  let S := intrinsicFrontier ℝ K
  have hca : c ∈ B := subset_affineSpan ℝ K (intrinsicInterior_subset hc)
  let cB : B := ⟨c, hca⟩
  letI : Nonempty B := ⟨cB⟩
  let e : E ≃ₜ B := Homeomorph.vaddConst cB
  let T : Set E := e ⁻¹' (Subtype.val ⁻¹' K)
  have hTconvex : Convex ℝ T :=
    (base_convex C u).affine_preimage
      (B.subtype.comp (AffineEquiv.vaddConst ℝ cB).toAffineMap)
  have hTcompact : IsCompact T := e.isCompact_preimage.mpr
    (Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (base_compact hclosed hstrict) (by
        intro x hx
        exact ⟨⟨x, subset_affineSpan ℝ K hx⟩, rfl⟩))
  have hTinterior : (0 : E) ∈ interior T := by
    rw [← e.preimage_interior]
    obtain ⟨b, hb, hbc⟩ := mem_intrinsicInterior.mp hc
    have he : e 0 = b := by apply Subtype.ext; simpa [e, cB] using hbc.symm
    change e 0 ∈ interior (Subtype.val ⁻¹' K : Set B)
    exact he.symm ▸ hb
  let ball : Set E := Metric.closedBall 0 1
  let g : E ≃ₜ E := gaugeRescaleHomeomorph T ball hTconvex
    (mem_interior_iff_mem_nhds.mp hTinterior)
    (NormedSpace.isVonNBounded_of_isBounded ℝ hTcompact.isBounded)
    (convex_closedBall 0 1) (Metric.closedBall_mem_nhds 0 one_pos)
    (NormedSpace.isVonNBounded_closedBall ℝ E 1)
  have g0 : g 0 = 0 := gaugeRescale_zero T ball
  have gfront : g '' frontier T = Metric.sphere 0 1 := by
    rw [← closure_sdiff_interior, image_sdiff g.injective]
    rw [image_gaugeRescaleHomeomorph_closure, image_gaugeRescaleHomeomorph_interior]
    exact closure_sdiff_interior ball |>.trans (by simp [ball, frontier_closedBall, one_ne_zero])
  let eA : frontier (Subtype.val ⁻¹' K : Set B) ≃ₜ S :=
    Topology.IsEmbedding.subtypeVal.homeomorphImage _
  have ef : e '' frontier T = frontier (Subtype.val ⁻¹' K : Set B) := by
    rw [← e.preimage_frontier, e.image_preimage]
  let eB : frontier T ≃ₜ S := ((e.image _).trans (Homeomorph.setCongr ef)).trans eA
  let eG : frontier T ≃ₜ Metric.sphere (0 : E) 1 :=
    (g.image _).trans (Homeomorph.setCongr gfront)
  let J : S ≃ₜ Metric.sphere (0 : E) 1 := eB.symm.trans eG
  have eBval (x : frontier T) : (eB x : V) = (x : E) + c := by
    rfl
  have Jval (x : S) : (J x : E) = g ⟨(x : V) - c,
      B.vsub_mem_direction (subset_affineSpan ℝ K
        (intrinsicFrontier_subset (base_compact hclosed hstrict).isClosed x.property)) hca⟩ := by
    change g (eB.symm x : E) = g _
    apply congrArg g
    apply Subtype.ext
    have he := eBval (eB.symm x)
    rw [eB.apply_symm_apply] at he
    exact eq_sub_iff_add_eq.mpr he.symm
  let F : unitInterval × Metric.sphere (0 : E) 1 → E :=
    fun z => g (H (z.1, J.symm z.2))
  have hF : Continuous F :=
    g.continuous.comp (H.continuous.comp
      (continuous_fst.prodMk (J.symm.continuous.comp continuous_snd)))
  have hF0 (z) : F z ≠ 0 := by
    intro hz
    exact Hnz _ (g.injective (hz.trans g0.symm))
  let Hsphere := TauCeti.normalizeToSphere F hF hF0
  let endpoint : Metric.sphere (0 : E) 1 := Hsphere (1, J v)
  have hzero (x : Metric.sphere (0 : E) 1) : Hsphere (0, x) = x := by
    apply Subtype.ext
    change NormedSpace.normalize (F (0, x)) = (x : E)
    have he : F (0, x) = (x : E) := by
      rw [show F (0, x) = g (H (0, J.symm x)) from rfl]
      have hh : H (0, J.symm x) = ⟨(J.symm x : V) - c,
          B.vsub_mem_direction (subset_affineSpan ℝ K
            (intrinsicFrontier_subset (base_compact hclosed hstrict).isClosed
              (J.symm x).property)) hca⟩ := Subtype.ext (H0 _)
      rw [hh, ← Jval (J.symm x), J.apply_symm_apply]
    rw [he]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.mp x.property)
  have hone (x : Metric.sphere (0 : E) 1) : Hsphere (1, x) = endpoint := by
    apply Subtype.ext
    change NormedSpace.normalize (g (H (1, J.symm x))) =
      NormedSpace.normalize (g (H (1, J.symm (J v))))
    have he : H (1, J.symm x) = H (1, J.symm (J v)) :=
      Subtype.ext ((H1 _).trans (H1 _).symm)
    rw [he]
  apply TauCeti.not_contractibleSpace_sphere (E := E)
  apply (contractible_iff_id_nullhomotopic _).mpr
  exact ⟨endpoint, ⟨{
    toContinuousMap := Hsphere
    map_zero_left := hzero
    map_one_left := hone }⟩⟩


/-- Every original pure boundary point of a singleton-label whole ball is itself
a singleton label, with uniqueness tested against all original pure labels. -/
theorem original_singleton_label_propagation
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u)
    (hp : ∀ s : pure C u, exclusion C u s = exclusion C u p → s = p)
    (q : pure C u) (hq : (q : V) ∈ exclusion C u p) :
    ∀ s : pure C u, exclusion C u s = exclusion C u q → s = q := by
  exact SingleLabelNormalBody.single_label_neighbor hclosed hstrict hgen hB p q hp hq


/-- The original global singleton-label theorem, including propagation over the
entire selected ball boundary and continuum many distinct whole balls when all
original ball dimensions are at least two. -/
theorem original_singleton_label_family [Nontrivial V]
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    ∃ p : pure C u,
      (∀ s : pure C u, exclusion C u s = exclusion C u p → s = p) ∧
      (∀ q : pure C u, (q : V) ∈ exclusion C u p →
        ∀ s : pure C u, exclusion C u s = exclusion C u q → s = q) ∧
      ((∀ q : pure C u, ∃ b : ExclusionChart C u q, 2 ≤ b.dim) →
        ∃ labels : ℝ ↪ pure C u,
          (∀ t, (labels t : V) ∈ exclusion C u p) ∧
          Function.Injective (fun t => exclusion C u (labels t)) ∧
          ∀ t, ∀ s : pure C u,
            exclusion C u s = exclusion C u (labels t) → s = labels t) := by
  classical
  obtain ⟨p, hp⟩ := original_singleton_label_exists hclosed hstrict hgen hB
  have hprop := original_singleton_label_propagation hclosed hstrict hgen hB p hp
  refine ⟨p, hp, hprop, ?_⟩
  intro hthick
  obtain ⟨b, hb⟩ := hthick p
  let i₀ : Fin b.dim := ⟨0, by omega⟩
  let i₁ : Fin b.dim := ⟨1, by omega⟩
  let w (t : ℝ) : EuclideanSpace ℝ (Fin b.dim) :=
    WithLp.toLp 2 (fun i => if i = i₀ then 1 else if i = i₁ then t else 0)
  have wi₀ (t : ℝ) : w t i₀ = 1 := by simp [w]
  have wi₁ (t : ℝ) : w t i₁ = t := by simp [w, i₀, i₁]
  have wnz (t : ℝ) : w t ≠ 0 := by
    intro hz
    have he := congrArg (fun z : EuclideanSpace ℝ (Fin b.dim) => z i₀) hz
    exact one_ne_zero (by simpa only [wi₀, PiLp.zero_apply] using he)
  let point (t : ℝ) := NormedSpace.normalize (w t)
  have hsphere (t : ℝ) : point t ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin b.dim)) 1 :=
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (wnz t))
  have hpoint (t : ℝ) : b.param (point t) ∈ exclusion C u p ∩ pure C u := by
    rw [OriginalFacePolarity.chart_boundary hclosed hstrict hgen hB p b]
    exact ⟨point t, hsphere t, rfl⟩
  let labels : ℝ → pure C u := fun t => ⟨b.param (point t), (hpoint t).2⟩
  have hinj : Function.Injective labels := by
    intro t s he
    have hn : point t = point s := b.injective (congrArg Subtype.val he)
    have hray : SameRay ℝ (w t) (w s) :=
      (sameRay_iff_inv_norm_smul_eq_of_ne (wnz t) (wnz s)).mpr hn
    obtain ⟨a, _, ha⟩ := hray.exists_pos_left (wnz t) (wnz s)
    have ha1 : a = 1 := by
      simpa only [PiLp.smul_apply, wi₀, smul_eq_mul, mul_one] using
        congrArg (fun z : EuclideanSpace ℝ (Fin b.dim) => z i₀) ha
    have hts := congrArg (fun z : EuclideanSpace ℝ (Fin b.dim) => z i₁) ha
    simpa only [ha1, one_smul, wi₁] using hts
  refine ⟨⟨labels, hinj⟩, (fun t => (hpoint t).1), ?_, ?_⟩
  · intro t s he
    exact hinj (hprop (labels s) (hpoint s).1 (labels t) he)
  · intro t s hs
    exact hprop (labels t) (hpoint t).1 s hs

end D5.S3.Quantum.Foundation.ActualExclusionBoundary
