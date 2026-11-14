/- GID: D5/S3/Quantum/Foundation/BinaryCenterReflection
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/BinaryCenterReflection
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The original binary center graph reflects a singleton ball into an entire pure sphere. -/

import D5.S3.Quantum.Foundation.BinaryCenterNoncollapse

/-! Reflection of the actual original center graph and its entire pure sphere. -/

noncomputable section
open Set Metric

namespace D5.S3.Quantum.Foundation.BinaryCenterReflection

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalFacePolarity SingleLabelNormalBody ContinuousFrameSum BinaryCenterGeometry
open BinaryCenterNoncollapse ReciprocalExclusionLimits

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
variable (hc : IsClosed (C : Set V))
  (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤) (B : exclusionBalls C u)

include hc hs hg B in
private theorem reflected_original_point (p q : pure C u)
    (hq : (q : V) ∈ exclusion C u p) :
    ∃ r : pure C u, (r : V) = (2 : ℝ) • center B q - p ∧
      (r : V) ∈ exclusion C u q := by
  let a := (B q).some
  have hp : (p : V) ∈ exclusion C u q ∩ pure C u :=
    ⟨(exclusion_symmetric p q).mp hq, p.property⟩
  rw [chart_boundary hc hs hg B q a] at hp
  obtain ⟨z, hz, hzp⟩ := hp
  have hzn : ‖z‖ = 1 := by simpa using hz
  let r := chartPure hc hs hg B q a (-z) (by simpa using hzn)
  refine ⟨r, ?_, chart_mem a (by simpa using hzn.le)⟩
  have hh := a.param.map_midpoint z (-z)
  have hh' : (1/2 : ℝ) • (a.param z + a.param (-z)) = center B q := by
    change (1/2 : ℝ) • (a.param z + a.param (-z)) = a.param 0
    simpa [midpoint_eq_smul_add] using hh.symm
  change a.param (-z) = _
  rw [← hzp, ← hh']
  module

include hc hs hg B in
/-- The actual reflected sphere is pure, and equality with the source ball
is equivalent to the original antipodal boundary-center identity. -/
theorem reflected_center_ball (hBC : binaryCompatible B)
    (p : pure C u) (hp : SingleLabel C u p) (b : ExclusionChart C u p) :
    ∃ g k : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
      (∀ x (hx : ‖x‖ = 1), g x = center B (chartPure hc hs hg B p b x hx)) ∧
      (∀ x, k x = (2 : ℝ) • g x - p) ∧ Function.Injective k ∧
      Module.finrank ℝ k.linear.range = b.dim ∧
      k '' Metric.closedBall 0 1 ⊆ base C u ∧
      k '' Metric.sphere 0 1 ⊆ pure C u ∧
      (k '' Metric.closedBall 0 1 = exclusion C u p ↔
        ∀ x (hx : ‖x‖ = 1), g x =
          (1/2 : ℝ) • ((p : V) + (2 : ℝ) • center B p - b.param x)) := by
  classical
  obtain ⟨g, hb, hi, hrank, hint, hsec, ht⟩ :=
    whole_ball_center_section hc hs hg B hBC p hp b
  let k : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V :=
    (2 : ℝ) • g - AffineMap.const ℝ _ (p : V)
  have hk (x) : k x = (2 : ℝ) • g x - p := rfl
  have hki : Function.Injective k := by
    intro x y h
    apply hi
    have he : (2 : ℝ) • g x = (2 : ℝ) • g y := sub_left_injective h
    exact (smul_right_injective V (by norm_num : (2 : ℝ) ≠ 0)) he
  have hkr : Module.finrank ℝ k.linear.range = b.dim := by
    rw [LinearMap.finrank_range_of_inj (k.linear_injective_iff.mpr hki)]
    exact finrank_euclideanSpace_fin
  have hpure : k '' Metric.sphere 0 1 ⊆ pure C u := by
    rintro y ⟨x, hx, rfl⟩
    have hxn : ‖x‖ = 1 := by simpa using hx
    let q := chartPure hc hs hg B p b x hxn
    obtain ⟨r, hre, hr⟩ := reflected_original_point hc hs hg B p q (chart_mem b hxn.le)
    rw [hk, hb x hxn, ← hre]
    exact r.property
  letI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  have hull : convexHull ℝ (Metric.sphere (0 : EuclideanSpace ℝ (Fin b.dim)) 1) =
      Metric.closedBall 0 1 := convexHull_sphere_eq_closedBall 0 zero_le_one
  have hK : k '' Metric.closedBall 0 1 ⊆ base C u := by
    rw [← hull, k.image_convexHull]
    exact convexHull_min (fun _ h => (hpure h).1) (base_convex C u)
  refine ⟨g, k, hb, hk, hki, hkr, hK, hpure, ?_⟩
  constructor
  · intro he x hx
    let q := chartPure hc hs hg B p b x hx
    obtain ⟨r, hre, hr⟩ := reflected_original_point hc hs hg B p q (chart_mem b hx.le)
    have hrF : (r : V) ∈ exclusion C u p := by
      rw [← he]
      refine ⟨x, by simpa using hx.le, ?_⟩
      rw [hk, hb x hx]
      exact hre.symm
    have horth := orthogonal_center_sum hc hs hg B p q r (chart_mem b hx.le) hrF hr.2
    rw [hre] at horth
    rw [hb x hx]
    change center B q = (1/2 : ℝ) • ((p : V) + (2 : ℝ) • center B p - (q : V))
    rw [← horth]
    module
  · intro he
    have hsphere : k '' Metric.sphere 0 1 = b.param '' Metric.sphere 0 1 := by
      have hanti (x) (hx : ‖x‖ = 1) : k x = b.param (-x) := by
        rw [hk, he x hx]
        have hh := b.param.map_midpoint x (-x)
        have hc0 : (1/2 : ℝ) • (b.param x + b.param (-x)) = center B p := by
          -- Centers of equal whole balls agree; b need not be the chosen chart.
          have hcenter : b.param 0 = center B p := by
            let a := (B p).some
            apply D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq
              (b.param 0) (a.param 0) b.param.linear.toContinuousLinearMap
              a.param.linear.toContinuousLinearMap
            have hbfun : (fun x => b.param 0 + b.param.linear.toContinuousLinearMap x) = b.param :=
              funext (fun x => (add_comm _ _).trans (congrFun b.param.decomp x).symm)
            have hafun : (fun x => a.param 0 + a.param.linear.toContinuousLinearMap x) = a.param :=
              funext (fun x => (add_comm _ _).trans (congrFun a.param.decomp x).symm)
            rw [hbfun, hafun]
            exact b.whole.trans a.whole.symm
          simpa [midpoint_eq_smul_add, hcenter] using hh.symm
        rw [← hc0]
        module
      apply Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        exact ⟨-x, by simpa using hx, (hanti x (by simpa using hx)).symm⟩
      · rintro y ⟨x, hx, rfl⟩
        exact ⟨-x, by simpa using hx, by simpa using hanti (-x) (by simpa using hx)⟩
    rw [← hull, k.image_convexHull, hsphere, ← b.param.image_convexHull, hull, b.whole]

include hc hs hg in
set_option maxHeartbeats 500000 in
/-- The reflected original pure sphere bounds either an entire original
exclusion ball or an exact nonfacial interior section. Neither alternative
is discarded. -/
theorem original_reflected_alternatives [Nontrivial V]
    (h3 : threeBallExclusions C u)
    (hBC : binaryCompatible (CommonOldExclusionConfirmation.three_implies_balls h3))
    (p : pure C u) (hp : SingleLabel C u p) :
    ∃ b : ExclusionChart C u p, b.dim = 3 ∧
    ∃ g k : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
      (∀ x (hx : ‖x‖ = 1), g x = center
        (CommonOldExclusionConfirmation.three_implies_balls h3)
        (chartPure hc hs hg (CommonOldExclusionConfirmation.three_implies_balls h3) p b x hx)) ∧
      (∀ x, k x = (2 : ℝ) • g x - p) ∧ Function.Injective k ∧
      Module.finrank ℝ k.linear.range = 3 ∧
      k '' Metric.closedBall 0 1 ⊆ base C u ∧
      intrinsicFrontier ℝ (k '' Metric.closedBall 0 1) = k '' Metric.sphere 0 1 ∧
      k '' Metric.sphere 0 1 ⊆ pure C u ∧
      (∀ y ∈ k '' Metric.closedBall 0 1,
        (2 : ℝ) • k 0 - y ∈ k '' Metric.closedBall 0 1) ∧
      ((k 0 ∈ intrinsicFrontier ℝ (base C u) ∧
          ∃ r : pure C u, k '' Metric.closedBall 0 1 = exclusion C u r) ∨
       (k 0 ∈ intrinsicInterior ℝ (base C u) ∧
          k '' Metric.closedBall 0 1 =
            base C u ∩ (affineSpan ℝ (k '' Metric.closedBall 0 1) : Set V) ∧
          ¬ IsExtreme ℝ (base C u) (k '' Metric.closedBall 0 1))) ∧
      (k '' Metric.closedBall 0 1 = exclusion C u p ↔
        ∀ x (hx : ‖x‖ = 1), g x =
          (1/2 : ℝ) • ((p : V) + (2 : ℝ) • center
            (CommonOldExclusionConfirmation.three_implies_balls h3) p - b.param x)) := by
  classical
  let B := CommonOldExclusionConfirmation.three_implies_balls h3
  let chart (r : pure C u) : ExclusionChart C u r :=
    ⟨3, by norm_num, CommonOldExclusionConfirmation.oldChart h3 r,
      (h3 r).choose_spec.1, (h3 r).choose_spec.2⟩
  let b := chart p
  obtain ⟨g, k, hb, hk, hi, hrank, hK, hP, heq⟩ :=
    reflected_center_ball hc hs hg B hBC p hp b
  let A := k '' Metric.closedBall 0 1
  have hA0 : k 0 ∈ A := ⟨0, by simp, rfl⟩
  have hfront : k '' Metric.sphere 0 1 ⊆ intrinsicFrontier ℝ (base C u) := by
    intro y hy
    let q : pure C u := ⟨y, hP hy⟩
    obtain ⟨r, s, hr, hs', hrs⟩ := pure_pair_in_ball hc hs hg B q
    exact MixedExclusionGeometry.exclusion_frontier hc hs hg B r
      ((exclusion_symmetric q r).mp hr)
  have hspan : (affineSpan ℝ A : Set V) = Set.range k := by
    have hsphere : affineSpan ℝ (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin b.dim)) 1) = ⊤ :=
      (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
        ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
    dsimp only [A]
    rw [← AffineSubspace.map_span, hsphere]
    ext y
    simp
  have hreflect : ∀ y ∈ A, (2 : ℝ) • k 0 - y ∈ A := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨-x, by simpa using hx, ?_⟩
    rw [show k (-x) = k.linear (-x) + k 0 from congrFun k.decomp (-x),
      show k x = k.linear x + k 0 from congrFun k.decomp x, map_neg]
    module
  have hbranches :
      (k 0 ∈ intrinsicFrontier ℝ (base C u) ∧ ∃ r : pure C u, A = exclusion C u r) ∨
      (k 0 ∈ intrinsicInterior ℝ (base C u) ∧
        A = base C u ∩ (affineSpan ℝ A : Set V) ∧ ¬ IsExtreme ℝ (base C u) A) := by
    by_cases hri : k 0 ∈ intrinsicInterior ℝ (base C u)
    · right
      have hsection : A = base C u ∩ Set.range k := by
        apply Subset.antisymm
        · rintro y hy
          exact ⟨hK hy, by obtain ⟨x, hx, rfl⟩ := hy; exact ⟨x, rfl⟩⟩
        · rintro y ⟨hy, z, rfl⟩
          have hn : ‖z‖ ≤ 1 := by
            by_contra hn
            have hz : 1 < ‖z‖ := lt_of_not_ge hn
            have hz0 : 0 < ‖z‖ := lt_trans zero_lt_one hz
            let w := ‖z‖⁻¹ • z
            have hw : ‖w‖ = 1 := by simp [w, norm_smul, hz0.ne']
            have hseg : k w ∈ openSegment ℝ (k 0) (k z) := by
              refine ⟨1 - ‖z‖⁻¹, ‖z‖⁻¹, ?_, inv_pos.mpr hz0, by ring, ?_⟩
              · exact sub_pos.mpr ((inv_lt_one₀ hz0).mpr hz)
              · rw [← Convex.combo_affine_apply (by ring)]
                congr 1
                simp [w]
            have hint := (base_convex C u).openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
              hri (subset_intrinsicClosure hy) hseg
            have hbd := hfront ⟨w, by simpa using hw, rfl⟩
            rw [← closure_sdiff_intrinsicInterior] at hbd
            exact hbd.2 hint
          exact ⟨z, by simpa using hn, rfl⟩
      have hneq : A ≠ base C u := by
        intro he
        have hd := (original_center_sections hc hs hg h3 hBC).1
        have had := CommonSourceLiftObstruction.ball_affine_span k
        change (affineSpan ℝ A).direction = k.linear.range at had
        rw [he] at had
        rw [had, hrank] at hd
        norm_num [b, chart] at hd
      have hnon : A.Nontrivial := by
        let e := EuclideanSpace.basisFun (Fin b.dim) ℝ ⟨0, b.dim_pos⟩
        have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin b.dim) ℝ).norm_eq_one _
        refine ⟨k 0, hA0, k e, ⟨e, by simpa using he.le, rfl⟩, ?_⟩
        intro heq'
        have he0 := hi heq'
        rw [← he0, norm_zero] at he
        norm_num at he
      have hnotface : ¬ IsExtreme ℝ (base C u) A := by
        intro hface
        have hconv : Convex ℝ A := (convex_closedBall _ _).affine_image k
        rcases (exclusion_ball_faces hc hs hg B).2.1 A ⟨k 0, hA0⟩ hconv hface hneq with hsingle | hball
        · obtain ⟨r, hr⟩ := hsingle
          exact (Set.not_nontrivial_iff.mpr (hr ▸ Set.subsingleton_singleton)) hnon
        · obtain ⟨r, hr⟩ := hball
          have hf := MixedExclusionGeometry.exclusion_frontier hc hs hg B r (hr ▸ hA0)
          rw [← closure_sdiff_intrinsicInterior] at hf
          exact hf.2 hri
      exact ⟨hri, by rw [hspan]; exact hsection, hnotface⟩
    · left
      have hbd : k 0 ∈ intrinsicFrontier ℝ (base C u) := by
        rw [← closure_sdiff_intrinsicInterior]
        exact ⟨subset_closure (hK hA0), hri⟩
      obtain ⟨r, hr⟩ := MixedExclusionGeometry.frontier_covered hc hs hg hbd
      obtain ⟨f, hf, hfzero⟩ := ((exclusion_ball_faces hc hs hg B).1 r).2.2.2.2.2.2
      have hvan := UniqueConfirmationDensity.affine_zero_inside_ball (f.toAffineMap.comp k)
        (fun x hx => (hf.1 (k x) (hK ⟨x, by simpa using hx, rfl⟩).1).1)
        (by simp : ‖(0 : EuclideanSpace ℝ (Fin b.dim))‖ < 1)
        (show f (k 0) = 0 from (hfzero ▸ hr).2)
      have hsub : A ⊆ exclusion C u r := by
        rintro y ⟨x, hx, rfl⟩
        rw [hfzero]
        exact ⟨hK ⟨x, hx, rfl⟩, hvan x⟩
      let a := chart r
      have kfun : (fun x => k 0 + k.linear.toContinuousLinearMap x) = k :=
        funext (fun x => (add_comm _ _).trans (congrFun k.decomp x).symm)
      have afun : (fun x => a.param 0 + a.param.linear.toContinuousLinearMap x) = a.param :=
        funext (fun x => (add_comm _ _).trans (congrFun a.param.decomp x).symm)
      have he := D5.S3.Geometry.AffineBallRigidity.eq_of_subset_of_extreme_sphere
        (base C u) (k 0) (a.param 0) k.linear.toContinuousLinearMap
        a.param.linear.toContinuousLinearMap (k.linear_injective_iff.mpr hi)
        (a.param.linear_injective_iff.mpr a.injective)
        (by rw [kfun, afun, a.whole]; exact hsub)
        (by rw [afun, a.whole]; exact fun x hx => hx.1)
        (fun x hx => by rw [show k 0 + k.linear.toContinuousLinearMap x = k x from congrFun kfun x];
                       exact hP ⟨x, by simpa using hx, rfl⟩)
      rw [kfun, afun, a.whole] at he
      exact ⟨hbd, r, he⟩
  exact ⟨b, rfl, g, k, hb, hk, hi, hrank, hK, affine_ball_frontier k hi,
    hP, hreflect, hbranches, heq⟩

end D5.S3.Quantum.Foundation.BinaryCenterReflection
