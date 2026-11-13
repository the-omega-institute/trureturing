/- GID: D5/S3/Quantum/Foundation/OriginalNormalRestriction
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalNormalRestriction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole original normal restriction and its relative interior under EB3 and Inj. -/

import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! The normal cone is the entire original positive annihilator cone.  Relative
interior is taken in its actual linear span, and restriction is composition with
the entire affine chart, rather than evaluation at finitely many points. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OriginalNormalRestriction

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces SingleLabelNormalBody OrthogonalJointCompletion

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

private theorem interior_add_closed {W : Type*} [NormedAddCommGroup W]
    {S : Set W} (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S)
    {x y : W} (hx : x ∈ interior S) (hy : y ∈ S) : x + y ∈ interior S := by
  have hsub : (fun z : W => z + y) '' S ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact hadd z hz y hy
  apply interior_mono hsub
  rw [← (Homeomorph.addRight y).image_interior]
  exact ⟨x, hx, rfl⟩

private theorem interior_smul_closed {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {S : Set W}
    (hsmul : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ S, t • x ∈ S)
    {x : W} (hx : x ∈ interior S) {t : ℝ} (ht : 0 < t) :
    t • x ∈ interior S := by
  have hsub : t • S ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact hsmul t ht.le z hz
  apply interior_mono hsub
  rw [interior_smul₀ ht.ne']
  exact ⟨x, hx, rfl⟩

/-- The full original 120.7/8 unit.  `N` contains all original positive
annihilators and `R` is the actual affine restriction.  The singleton premise
concerns the whole confirming-effect fiber, independently of label injectivity.
The interior witnesses include neighborhoods in `L = span N`. -/
theorem original_normal_restriction
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ q : pure C u, ∃ b : ExclusionChart C u q, b.dim = 3)
    (hInj : ∀ q r : pure C u, exclusion C u q = exclusion C u r → q = r)
    (p : pure C u) (a : ExclusionChart C u p) (ha : a.dim = 3) :
    let N : Set (V →L[ℝ] ℝ) := {f | (∀ x ∈ C, 0 ≤ f x) ∧ f p = 0}
    let L := Submodule.span ℝ N
    let R : L →ₗ[ℝ] (EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ) :=
      { toFun := fun f => f.val.toLinearMap.toAffineMap.comp a.param
        map_add' := by intros; ext; rfl
        map_smul' := by intros; ext; rfl }
    Function.Surjective R ∧ 4 ≤ Module.finrank ℝ L ∧
    {f | f ∈ N ∧ ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin a.dim)) 1,
      f (a.param z) = 1} =
      {f | ∃ e : V →ₗ[ℝ] ℝ, common C u p e ∧ f = (u - e).toContinuousLinearMap} ∧
    (∃ f : L, f ∈ interior (L.subtype ⁻¹' N) ∧
      f.val ∈ intrinsicInterior ℝ N ∧ R f = AffineMap.const ℝ _ 1) ∧
    (∀ ep : V →ₗ[ℝ] ℝ, (∀ e, common C u p e ↔ e = ep) →
      ∃ (g : L) (e : L ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin a.dim) →ᵃ[ℝ] ℝ)),
        g.val = (u - ep).toContinuousLinearMap ∧
        g ∈ interior (L.subtype ⁻¹' N) ∧ g.val ∈ intrinsicInterior ℝ N ∧
        e.toLinearMap = R ∧ Function.Bijective R ∧ Module.finrank ℝ L = 4) := by
  classical
  dsimp only
  let E := EuclideanSpace ℝ (Fin a.dim)
  let N : Set (V →L[ℝ] ℝ) := {f | (∀ x ∈ C, 0 ≤ f x) ∧ f p = 0}
  let L := Submodule.span ℝ N
  let R : L →ₗ[ℝ] (E →ᵃ[ℝ] ℝ) :=
    { toFun := fun f => f.val.toLinearMap.toAffineMap.comp a.param
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  change Function.Surjective R ∧ _
  let S : Set L := L.subtype ⁻¹' N
  have hN0 : (0 : V →L[ℝ] ℝ) ∈ N := by constructor <;> simp
  have hadd : ∀ f ∈ N, ∀ g ∈ N, f + g ∈ N := by
    intro f hf g hg
    exact ⟨fun x hx => add_nonneg (hf.1 x hx) (hg.1 x hx), by simp [hf.2, hg.2]⟩
  have hsmul : ∀ t : ℝ, 0 ≤ t → ∀ f ∈ N, t • f ∈ N := by
    intro t ht f hf
    exact ⟨fun x hx => mul_nonneg ht (hf.1 x hx), by simp [hf.2]⟩
  have hSadd : ∀ f ∈ S, ∀ g ∈ S, f + g ∈ S :=
    fun f hf g hg => hadd f.val hf g.val hg
  have hSsmul : ∀ t : ℝ, 0 ≤ t → ∀ f ∈ S, t • f ∈ S :=
    fun t ht f hf => hsmul t ht f.val hf
  have hSconv : Convex ℝ S := by
    intro f hf g hg s t hs ht _
    exact hSadd _ (hSsmul s hs f hf) _ (hSsmul t ht g hg)
  have himage : L.subtype '' S = N := by
    ext f
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro hf
      exact ⟨⟨f, Submodule.subset_span hf⟩, hf, rfl⟩
  have hspan : Submodule.span ℝ S = ⊤ := by
    apply Submodule.map_injective_of_injective L.injective_subtype
    rw [Submodule.map_span, himage, Submodule.map_top, Submodule.range_subtype]
  have haffS : affineSpan ℝ S = ⊤ := by
    rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ S hN0), hspan]
    rfl
  have haffN : affineSpan ℝ N = L.toAffineSubspace :=
    affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ N hN0)
  have hri (f : L) (hf : f ∈ interior S) : f.val ∈ intrinsicInterior ℝ N := by
    rw [intrinsicInterior, haffN]
    exact ⟨f, hf, rfl⟩
  have hB : exclusionBalls C u := fun q => ⟨(hEB3 q).choose⟩
  have hp : SingleLabel C u p := fun q hq => hInj q p hq
  obtain ⟨rho, hrho, _, hball⟩ := slope_body_inradius hc hs hg hB p hp a
  have hballspan : affineSpan ℝ (Metric.closedBall (0 : E) 1) = ⊤ := by
    apply (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
    exact ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
  let affine (v : E) : E →ᵃ[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ E v).toLinearMap.toAffineMap + AffineMap.const ℝ E 1
  have hlift (v : E) (hv : ‖v‖ ≤ rho) :
      ∃ b : L, b ∈ S ∧ R b = affine v := by
    obtain ⟨b, hb, hbp, hbc, hformula⟩ :=
      (slope_body_original a v).mp (hball (by simpa using hv))
    let b' := b.toContinuousLinearMap
    have hbN : b' ∈ N := ⟨hb, hbp⟩
    refine ⟨⟨b', Submodule.subset_span hbN⟩, hbN, ?_⟩
    apply AffineMap.ext_on hballspan
    intro z hz
    simpa [R, affine, add_comm] using hformula z hz
  obtain ⟨b0, hb0, hb0R⟩ := hlift 0 (by simpa using hrho.le)
  have hb0val (z : E) : b0.val (a.param z) = 1 := by
    have h := congrArg (fun f : E →ᵃ[ℝ] ℝ => f z) hb0R
    simpa [R, affine] using h
  have hscale (v : E) : ∃ t : ℝ, 0 < t ∧ ‖t⁻¹ • v‖ ≤ rho := by
    refine ⟨(‖v‖ + 1) / rho, div_pos (by positivity) hrho, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (div_pos (by positivity) hrho))]
    rw [inv_div]
    have hn : 0 < ‖v‖ + 1 := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hn).mpr
    nlinarith [norm_nonneg v]
  have honto : Function.Surjective R := by
    intro f
    let v := (InnerProductSpace.toDual ℝ E).symm f.linear.toContinuousLinearMap
    obtain ⟨t, ht, hv⟩ := hscale v
    obtain ⟨b, hb, hbR⟩ := hlift (t⁻¹ • v) hv
    refine ⟨t • b + (f 0 - t) • b0, ?_⟩
    rw [map_add, map_smul, map_smul, hbR, hb0R]
    ext z
    have hvz : ⟪v, z⟫ = f.linear z := InnerProductSpace.toDual_symm_apply _ _
    have hfz := congrFun f.decomp z
    simp only [AffineMap.coe_add, Pi.add_apply, AffineMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, affine, AffineMap.const_apply, AffineMap.coe_linearMap,
      LinearMap.coe_coe, InnerProductSpace.toDual_apply, inner_smul_left,
      inner_zero_left] at *
    rw [hvz]
    field_simp
    linarith
  have hdim : Module.finrank ℝ (E →ᵃ[ℝ] ℝ) = 4 := by
    rw [AffineMap.finrank_eq]
    simp [E, ha]
  have hbound (f : V →L[ℝ] ℝ) (hf : f ∈ N)
      (hone : ∀ z ∈ Metric.closedBall (0 : E) 1, f (a.param z) = 1) :
      common C u p (u - f.toLinearMap) := by
    have hf0 : f.toLinearMap ≠ 0 := by
      intro he
      have he0 := LinearMap.congr_fun he (a.param 0)
      have h1 := hone 0 (by simp)
      change f (a.param 0) = 0 at he0
      linarith
    obtain ⟨s, hsD, _, hmax⟩ :=
      positive_annihilator_maximum hc hs hg p f.toLinearMap hf0 hf.1 hf.2
    obtain ⟨z, hz, hzs⟩ := a.whole.symm ▸ hsD
    have hfs : f s = 1 := hzs ▸ hone z hz
    have hproper : proper C u f.toLinearMap :=
      cone_bound (base_compact hc hs) hs (fun q =>
        ⟨hf.1 q (pure_mem q).1, hfs ▸ hmax q (pure_mem q)⟩)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x hx
      have hx' := hproper x hx
      change 0 ≤ u x - f x ∧ u x - f x ≤ u x
      constructor <;> linarith
    · simp [hf.2, (pure_mem p).2]
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := a.whole.symm ▸ hx
      simp [hone w hw, (show a.param w ∈ base C u from
        (a.whole ▸ mem_image_of_mem a.param hw).1).2]
  have heffect (e : V →ₗ[ℝ] ℝ) (he : common C u p e) :
      (u - e).toContinuousLinearMap ∈ N ∧
      ∀ z ∈ Metric.closedBall (0 : E) 1, (u - e) (a.param z) = 1 := by
    refine ⟨⟨?_, by simp [he.1.2, (pure_mem p).2]⟩, ?_⟩
    · intro x hx
      exact sub_nonneg.mpr (he.1.1 x hx).2
    · intro z hz
      have hx : a.param z ∈ exclusion C u p := a.whole ▸ mem_image_of_mem a.param hz
      have he0 : e (a.param z) = 0 := he.2 _ hx
      simp [he0, hx.1.2]
  have hfiber :
      {f : V →L[ℝ] ℝ | f ∈ N ∧ ∀ z ∈ Metric.closedBall (0 : E) 1,
        f (a.param z) = 1} =
      {f | ∃ e : V →ₗ[ℝ] ℝ, common C u p e ∧ f = (u - e).toContinuousLinearMap} := by
    ext f
    constructor
    · rintro ⟨hf, h1⟩
      refine ⟨u - f.toLinearMap, hbound f hf h1, ?_⟩
      ext x
      simp
    · rintro ⟨e, he, rfl⟩
      exact heffect e he
  -- Work inside the full span.  Add a genuine constant-one normal first, so
  -- the later slope cancellation has a strictly positive constant term.
  obtain ⟨x, hx⟩ := hSconv.interior_nonempty_iff_affineSpan_eq_top.mpr haffS
  let y := x + b0
  have hy : y ∈ interior S := interior_add_closed hSadd hx hb0
  have hyN : y ∈ S := interior_subset hy
  have hcC : a.param 0 ∈ C :=
    (show a.param 0 ∈ exclusion C u p from a.whole ▸ mem_image_of_mem a.param (by simp)).1.1
  have hyc : 0 < y.val (a.param 0) := by
    have hxc := (interior_subset hx : x ∈ S).1 _ hcC
    change 0 < x.val (a.param 0) + b0.val (a.param 0)
    rw [hb0val]
    linarith
  let v := (InnerProductSpace.toDual ℝ E).symm (R y).linear.toContinuousLinearMap
  obtain ⟨t, ht, hv⟩ := hscale (-v)
  obtain ⟨b, hb, hbR⟩ := hlift (t⁻¹ • (-v)) hv
  let z := y + t • b
  have hz : z ∈ interior S :=
    interior_add_closed hSadd hy (hSsmul t ht.le b hb)
  let alpha := y.val (a.param 0) + t
  have halpha : 0 < alpha := add_pos hyc ht
  have hzR : R z = AffineMap.const ℝ E alpha := by
    rw [map_add, map_smul, hbR]
    ext w
    have hvw : ⟪v, w⟫ = (R y).linear w := InnerProductSpace.toDual_symm_apply _ _
    have hyw := congrFun (R y).decomp w
    simp only [AffineMap.coe_add, Pi.add_apply, AffineMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, affine, AffineMap.const_apply, AffineMap.coe_linearMap,
      LinearMap.coe_coe, InnerProductSpace.toDual_apply, inner_smul_left,
      inner_neg_left] at *
    rw [hvw]
    dsimp [alpha, R] at *
    field_simp
    linarith
  let g := alpha⁻¹ • z
  have hgRI : g ∈ interior S := interior_smul_closed hSsmul hz (inv_pos.mpr halpha)
  have hgR : R g = AffineMap.const ℝ E 1 := by
    rw [map_smul, hzR]
    ext w
    simp [halpha.ne']
  refine ⟨honto, ?_, hfiber, ⟨g, hgRI, hri g hgRI, hgR⟩, ?_⟩
  · rw [← hdim]
    exact LinearMap.finrank_le_finrank_of_surjective R honto
  · intro ep hep
    have hsingleton (f : L) (hf : f ∈ S) (hfR : R f = AffineMap.const ℝ E 1) :
        f.val = (u - ep).toContinuousLinearMap := by
      have h1 (w : E) (_ : w ∈ Metric.closedBall (0 : E) 1) : f.val (a.param w) = 1 :=
        congrArg (fun q : E →ᵃ[ℝ] ℝ => q w) hfR
      have he := (hep _).mp (hbound f.val hf h1)
      ext w
      have hw := LinearMap.congr_fun he w
      change u w - f.val w = ep w at hw
      change f.val w = u w - ep w
      linarith
    have hgval := hsingleton g (interior_subset hgRI) hgR
    have hinj : Function.Injective R := by
      apply LinearMap.ker_eq_bot.mp
      apply Submodule.eq_bot_iff.mpr
      intro k hk
      have hkR : R k = 0 := hk
      obtain ⟨epsilon, hepsilon, heball⟩ := Metric.mem_interior_iff.mp hgRI
      let t : ℝ := epsilon / (2 * (‖k‖ + 1))
      have ht : 0 < t := div_pos hepsilon (by positivity)
      have hsmall : ‖t • k‖ < epsilon := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        dsimp [t]
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖k‖ + 1))).mpr
        nlinarith [norm_nonneg k]
      have hplus : g + t • k ∈ S := heball (by simpa [dist_eq_norm] using hsmall)
      have hminus : g - t • k ∈ S := heball (by simpa [dist_eq_norm] using hsmall)
      have hpR : R (g + t • k) = AffineMap.const ℝ E 1 := by simp [hgR, hkR]
      have hmR : R (g - t • k) = AffineMap.const ℝ E 1 := by simp [hgR, hkR]
      have hp := hsingleton _ hplus hpR
      have hm := hsingleton _ hminus hmR
      have hzero : (2 * t) • k = 0 := by
        apply Subtype.val_injective
        have hsub := congrArg (fun f : V →L[ℝ] ℝ => f - (g - t • k).val) hp
        rw [← hm] at hsub
        simpa [two_smul, add_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
      exact (smul_eq_zero.mp hzero).resolve_left (by positivity)
    let e := LinearEquiv.ofBijective R ⟨hinj, honto⟩
    refine ⟨g, e, hgval, hgRI, hri g hgRI, rfl, ⟨hinj, honto⟩, ?_⟩
    exact e.finrank_eq.trans hdim

end D5.S3.Quantum.Foundation.OriginalNormalRestriction
