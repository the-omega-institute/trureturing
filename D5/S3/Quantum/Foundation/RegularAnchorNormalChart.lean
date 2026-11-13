/- GID: D5/S3/Quantum/Foundation/RegularAnchorNormalChart
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/RegularAnchorNormalChart
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original regular anchors determine a bounded full normal coordinate chart. -/

import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Quantum.Foundation.CommonPositiveExtension
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import D5.S3.Quantum.Foundation.OriginalWidthContact

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
abbrev nativeChart {p : V} (a : FullBall3Chart C u p) : ExclusionChart C u p :=
  ⟨3, by decide, a.param, a.injective, a.whole⟩

/-- The original regular-anchor condition is uniqueness of the full family A_p. -/
def Regular (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : V) : Prop :=
  ∃! e : V →ₗ[ℝ] ℝ, common C u p e

/-- Signed span of the entire original positive annihilator cone. -/
abbrev NormalSpan (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : V) :=
  Submodule.span ℝ (zeroPositive C u p)

omit [FiniteDimensional ℝ V] in
private theorem complement_normal {p : pure C u} {e : V →ₗ[ℝ] ℝ}
    (he : common C u p e) : u - e ∈ zeroPositive C u p := by
  refine ⟨fun x hx => sub_nonneg.mpr (he.1.1 x hx).2, ?_⟩
  simp [LinearMap.sub_apply, (pure_mem p).2, he.1.2]

omit [FiniteDimensional ℝ V] in
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
    (e : V →ₗ[ℝ] ℝ)
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
  have hb : proper C u b := by
    have hn := OriginalWidthContact.normalized_effect (base_compact hc hs) hs
      (a := (p : V)) (z := q)
      (fun x hx => by simpa only [hf.2] using hf.1 x hx.1)
      (fun x hx => hmax x hx) (by simpa only [hf.2, sub_zero] using hqpos)
    simpa only [hf.2, sub_zero, zero_smul, hqc] using hn
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
      rw [(chart_mem a (by simpa using hz)).1.2, hformula z, inv_mul_cancel₀ hpos.ne']
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
    · simp only [map_add, Prod.snd_add]
  map_smul' t f := by
    apply Prod.ext
    · rfl
    · simp only [map_smul, Prod.smul_snd, RingHom.id_apply]

private theorem complement_coordinates {p : pure C u} {e : V →ₗ[ℝ] ℝ}
    (he : common C u p e) (a : ExclusionChart C u p) :
    coordinates a (u - e) = (1, 0) := by
  apply Prod.ext
  · exact complement_chart he a 0
  · apply ext_inner_right ℝ
    intro z
    have hh := slope_formula a (u - e).toContinuousLinearMap z
    change (u - e) (a.param z) = (u - e) (a.param 0) + _ at hh
    rw [complement_chart he a z, complement_chart he a 0] at hh
    change ⟪slope a (u - e).toContinuousLinearMap, z⟫ = ⟪(0 : EuclideanSpace ℝ (Fin a.dim)), z⟫
    simp only [inner_zero_left]
    linarith

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
  have hnorm : ‖(-t) • v‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos ht), neg_neg]
    dsimp [t]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1 + ‖v‖)]
    nlinarith
  obtain ⟨b, hb, hbv⟩ := hball (show (-t) • v ∈ Metric.closedBall 0 r by simpa using hnorm)
  let d : V →ₗ[ℝ] ℝ := t⁻¹ • b.toLinearMap
  have hd : d ∈ zeroPositive C u p :=
    ⟨fun x hx => mul_nonneg (inv_nonneg.mpr ht.le) (hb.1 x hx), by simp [d, hb.2.1]⟩
  have hfadd : f + d ∈ zeroPositive C u p :=
    ⟨fun x hx => add_nonneg (hf.1 x hx) (hd.1 x hx), by simp [hf.2, hd.2]⟩
  have hkadd : k + d ∈ zeroPositive C u p :=
    ⟨fun x hx => add_nonneg (hk.1 x hx) (hd.1 x hx), by simp [hk.2, hd.2]⟩
  have hfslope : slope a (f + d).toContinuousLinearMap = 0 := by
    simp only [d, map_add, map_smul]
    change slope a f.toContinuousLinearMap + t⁻¹ • slope a b = 0
    rw [hbv, smul_smul]
    change v + (t⁻¹ * -t) • v = 0
    simp [ht.ne']
  have hkslope : slope a (k + d).toContinuousLinearMap = 0 := by
    have hv := congrArg Prod.snd heq
    change slope a f.toContinuousLinearMap = slope a k.toContinuousLinearMap at hv
    simpa only [map_add, ← hv] using hfslope
  have hfconst := constant_normal hc hs hg p a e huniq (f + d) hfadd hfslope
  have hkconst := constant_normal hc hs hg p a e huniq (k + d) hkadd hkslope
  have hcenter := congrArg Prod.fst heq
  change f (a.param 0) = k (a.param 0) at hcenter
  apply add_right_cancel (b := d)
  rw [hfconst, hkconst]
  simp only [LinearMap.add_apply, hcenter]

private theorem coordinates_bijective
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (hp : SingleLabel C u p) (a : ExclusionChart C u p)
    (e : V →ₗ[ℝ] ℝ) (he : common C u p e)
    (huniq : ∀ f, common C u p f → f = e) :
    Function.Bijective ((coordinates a).comp (NormalSpan C u p).subtype) := by
  let S := NormalSpan C u p
  let R := (coordinates a).comp S.subtype
  have hgS : u - e ∈ S := Submodule.subset_span (complement_normal he)
  have hgin := complement_coordinates he a
  constructor
  · intro f k hfk
    obtain ⟨b, hb, d, hd, hbd⟩ := positive_span_difference (S.sub_mem f.property k.property)
    have hco : coordinates a b = coordinates a d := by
      apply sub_eq_zero.mp
      rw [← map_sub, ← hbd]
      change R (f - k) = 0
      rw [map_sub, hfk, sub_self]
    have heq := positive_coordinates_injective hc hs hg hB p hp a e he huniq hb hd hco
    apply Subtype.ext
    apply sub_eq_zero.mp
    rw [hbd, heq, sub_self]
  · rintro ⟨s, v⟩
    obtain ⟨r, hr, _, hball⟩ := slope_body_inradius hc hs hg hB p hp a
    let t := r / (1 + ‖v‖)
    have ht : 0 < t := div_pos hr (by positivity)
    have hnorm : ‖t • v‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      dsimp [t]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1 + ‖v‖)]
      nlinarith
    obtain ⟨b, hb, hbv⟩ := hball (show t • v ∈ Metric.closedBall 0 r by simpa using hnorm)
    have hbS : b.toLinearMap ∈ S := Submodule.subset_span ⟨hb.1, hb.2.1⟩
    have hbco : coordinates a b.toLinearMap = (1, t • v) :=
      Prod.ext hb.2.2 hbv
    refine ⟨⟨t⁻¹ • b.toLinearMap + (s - t⁻¹) • (u - e),
      S.add_mem (S.smul_mem _ hbS) (S.smul_mem _ hgS)⟩, ?_⟩
    change coordinates a (t⁻¹ • b.toLinearMap + (s - t⁻¹) • (u - e)) = (s, v)
    rw [map_add, map_smul, map_smul, hbco, hgin]
    apply Prod.ext
    · simp
    · simp [smul_smul, ht.ne']

private theorem common_peak_unique
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : pure C u) (e : V →ₗ[ℝ] ℝ) (he : common C u p e) :
    ∀ x ∈ base C u, e x = 1 → x = p := by
  intro x hx hxe
  exact OriginalWidthContact.top_subsingleton_of_zero_exclusion hc hs hg hB hinj
    he.1.1 p he.2 ⟨hx, hxe⟩ ⟨pure_mem p, he.1.2⟩

/-- The full original affine restriction is reconstructed by constant and slope. -/
def affineCoordinates (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : (E →ᵃ[ℝ] ℝ) ≃ₗ[ℝ] (ℝ × E) :=
  (AffineMap.toConstProdLinearMap ℝ).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ)
      (LinearMap.toContinuousLinearMap.trans (InnerProductSpace.toDual ℝ E).symm.toLinearEquiv))

/-- Proved original-domain data for the actual three-dimensional normal chart. -/
structure NativeChart (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (p : pure C u) (e : V →ₗ[ℝ] ℝ) (a : FullBall3Chart C u p) where
  restrictEquiv : NormalSpan C u p ≃ₗ[ℝ] (ThreeSpace →ᵃ[ℝ] ℝ)
  restrict_eq : ∀ f, restrictEquiv f = restriction (nativeChart a) f
  H : V →ₗ[ℝ] ThreeSpace
  chart_eq : ∀ w, H (a.param w) = w
  coordinate_mem : ∀ i : Fin 3, (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).toLinearMap.comp H ∈
    NormalSpan C u p
  at_anchor : H p = 0
  gap_normal : u - e ∈ zeroPositive C u p
  gap_chart : ∀ w, (u - e) (a.param w) = 1
  gap_positive : ∀ x ∈ base C u, x ≠ (p : V) → 0 < (u - e) x
  uniform_bound : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ C, ‖H x‖ ≤ M * (u - e) x
  zero_comparison : ∀ x ∈ base C u, comparison C u p x = 0 ↔ x ∈ exclusion C u p
  cone_salient : C.toConvexCone.Salient
  chart_unit_linear : ∀ w, u (a.param.linear w) = 0
  normal_dimension : Module.finrank ℝ (NormalSpan C u p) = 4


/-- EB3, exclusion-label injectivity and actual regularity derive the entire native
normal chart and a finite bound on the whole original cone. -/
theorem regular_anchor_native
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : EB3 C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : pure C u) (e : V →ₗ[ℝ] ℝ) (he : common C u p e)
    (hreg : Regular C u p) (a : FullBall3Chart C u p) :
    Nonempty (NativeChart C u p e a) := by
  classical
  have hB : exclusionBalls C u := fun q => by
    obtain ⟨b⟩ := h3 q
    exact ⟨(nativeChart b)⟩
  have hp : SingleLabel C u p := fun q hq => hinj hq
  have huniq : ∀ f, common C u p f → f = e := fun f hf => hreg.unique hf he
  let S := NormalSpan C u p
  let R := (coordinates (nativeChart a)).comp S.subtype
  let Q : S ≃ₗ[ℝ] (ℝ × ThreeSpace) := LinearEquiv.ofBijective R
    (coordinates_bijective hc hs hg hB p hp (nativeChart a) e he huniq)
  let A := affineCoordinates ThreeSpace
  let E : S ≃ₗ[ℝ] (ThreeSpace →ᵃ[ℝ] ℝ) := Q.trans A.symm
  have hE (f : S) : E f = restriction (nativeChart a) f := by
    apply A.injective
    change A (A.symm (Q f)) = A (restriction (nativeChart a) f)
    rw [A.apply_symm_apply]
    rfl
  let k : Fin 3 → S := fun i => Q.symm (0, EuclideanSpace.single i 1)
  have hk (i : Fin 3) : coordinates (nativeChart a) (k i) = (0, EuclideanSpace.single i 1) :=
    Q.apply_symm_apply _
  let H : V →ₗ[ℝ] ThreeSpace :=
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap.comp
      (LinearMap.pi (fun i => (k i : V →ₗ[ℝ] ℝ)))
  have hHi (x : V) (i : Fin 3) : H x i = (k i : V →ₗ[ℝ] ℝ) x := rfl
  have hchart (w : ThreeSpace) : H (a.param w) = w := by
    ext i
    rw [hHi]
    have hh := slope_formula (nativeChart a) (k i : V →ₗ[ℝ] ℝ).toContinuousLinearMap w
    change (k i : V →ₗ[ℝ] ℝ) (a.param w) =
      (coordinates (nativeChart a) (k i)).1 + ⟪(coordinates (nativeChart a) (k i)).2, w⟫ at hh
    rw [hk] at hh
    change (k i : V →ₗ[ℝ] ℝ) (a.param w) =
      0 + ⟪(EuclideanSpace.single i (1 : ℝ) : ThreeSpace), w⟫ at hh
    simpa only [EuclideanSpace.inner_single_left, conj_trivial, one_mul, zero_add] using hh
  have hspan (i : Fin 3) : (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).toLinearMap.comp H ∈ S := by
    exact (k i).property
  have hanchor : H p = 0 := by
    ext i
    obtain ⟨b, hb, d, hd, hbd⟩ := positive_span_difference (k i).property
    change (k i : V →ₗ[ℝ] ℝ) p = 0
    rw [hbd]
    simp [hb.2, hd.2]
  obtain ⟨r, hr, _, hball⟩ := slope_body_inradius hc hs hg hB p hp (nativeChart a)
  have hgS : u - e ∈ S := Submodule.subset_span (complement_normal he)
  have hpositive (i : Fin 3) (t : ℝ) (ht : |t| ≤ r) :
      u - e + t • (k i : V →ₗ[ℝ] ℝ) ∈ zeroPositive C u p := by
    have hnorm : ‖t • EuclideanSpace.single i (1 : ℝ)‖ ≤ r := by
      simpa [norm_smul, EuclideanSpace.single] using ht
    have hbmem : t • EuclideanSpace.single i (1 : ℝ) ∈
        Metric.closedBall (0 : ThreeSpace) r := by
      rwa [Metric.mem_closedBall, dist_zero_right]
    obtain ⟨b, hb, hbco⟩ := hball hbmem
    change (slope (nativeChart a) b : ThreeSpace) =
      t • (EuclideanSpace.single i 1 : ThreeSpace) at hbco
    have hbS : b.toLinearMap ∈ S := Submodule.subset_span ⟨hb.1, hb.2.1⟩
    have heq : u - e + t • (k i : V →ₗ[ℝ] ℝ) = b.toLinearMap := by
      have hh : (⟨u - e + t • (k i : V →ₗ[ℝ] ℝ),
          S.add_mem hgS (S.smul_mem t (k i).property)⟩ : S) = ⟨b.toLinearMap, hbS⟩ := by
        apply Q.injective
        change coordinates (nativeChart a) (u - e + t • (k i : V →ₗ[ℝ] ℝ)) =
          coordinates (nativeChart a) b.toLinearMap
        rw [map_add, map_smul, complement_coordinates he, hk]
        apply Prod.ext
        · change 1 + t * 0 = b ((nativeChart a).param 0)
          simpa using hb.2.2.symm
        · change (0 : ThreeSpace) + t • (EuclideanSpace.single i 1 : ThreeSpace) =
            (slope (nativeChart a) b : ThreeSpace)
          rw [zero_add]
          exact hbco.symm
      exact congrArg Subtype.val hh
    rw [heq]
    exact ⟨hb.1, hb.2.1⟩
  have hcoord (x : V) (hx : x ∈ C) (i : Fin 3) : |H x i| ≤ r⁻¹ * (u - e) x := by
    have hp' := (hpositive i r (by rw [abs_of_pos hr])).1 x hx
    have hm' := (hpositive i (-r) (by rw [abs_neg, abs_of_pos hr])).1 x hx
    change 0 ≤ (u - e) x + r * H x i at hp'
    change 0 ≤ (u - e) x + -r * H x i at hm'
    rw [abs_le]
    constructor
    · have hh : -(H x i) ≤ r⁻¹ * (u - e) x :=
        (le_inv_mul_iff₀ hr).mpr (by linarith)
      linarith
    · exact (le_inv_mul_iff₀ hr).mpr (by linarith)
  have hbound : ∀ x ∈ C, ‖H x‖ ≤ (3 * r⁻¹) * (u - e) x := by
    intro x hx
    have heq : H x = ∑ i : Fin 3, EuclideanSpace.single i (H x i) := by
      ext j
      simp [EuclideanSpace.single, Finset.sum_apply]
    calc
      ‖H x‖ = ‖∑ i : Fin 3, EuclideanSpace.single i (H x i)‖ := congrArg norm heq
      _ ≤ ∑ i : Fin 3, ‖EuclideanSpace.single i (H x i)‖ := norm_sum_le _ _
      _ = ∑ i : Fin 3, |H x i| := by simp [EuclideanSpace.single]
      _ ≤ ∑ _i : Fin 3, r⁻¹ * (u - e) x := Finset.sum_le_sum (fun i _ => hcoord x hx i)
      _ = (3 * r⁻¹) * (u - e) x := by simp; ring
  have hsalient : C.toConvexCone.Salient := by
    intro x hx hx0 hneg
    have hpx := hs x hx hx0
    have hnx := hs (-x) hneg (neg_ne_zero.mpr hx0)
    rw [map_neg] at hnx
    linarith
  have hdim : Module.finrank ℝ S = 4 := by
    have hh := Q.finrank_eq
    simpa [Module.finrank_prod, Module.finrank_self, ThreeSpace, finrank_euclideanSpace_fin] using hh
  refine ⟨⟨E, hE, H, hchart, hspan, hanchor, complement_normal he,
    complement_chart he (nativeChart a), ?_, ⟨3 * r⁻¹, by positivity, hbound⟩,
    fun x hx => ExclusionWidthCompactness.comparison_zero_iff hs hg p hx,
    hsalient,
    SingleLabelNormalBody.chart_unit_linear (nativeChart a), hdim⟩⟩
  intro x hx hxp
  have hnonneg := (complement_normal he).1 x hx.1
  apply lt_of_le_of_ne hnonneg
  intro hz
  have heone : e x = 1 := by
    change 0 = u x - e x at hz
    rw [hx.2] at hz
    linarith
  exact hxp (common_peak_unique hc hs hg hB hinj p e he x hx heone)

end D5.S3.Quantum.Foundation.RegularAnchorNormalChart
