/- GID: D5/S3/Quantum/Foundation/RegularAnchorContactCriterion
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/RegularAnchorContactCriterion
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original width, support minimum, shell contact and strict distance share one chart. -/

import D5.S3.Quantum.Foundation.OriginalNormalRestriction
import D5.S3.Quantum.Foundation.CommonPositiveExtension
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import D5.S3.Quantum.Foundation.OriginalWidthContact

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.RegularAnchorContactCriterion

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
  let T : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  let N : Set (V →L[ℝ] ℝ) := {f | (∀ x ∈ C, 0 ≤ f x) ∧ f p = 0}
  let L := Submodule.span ℝ N
  have hmap : S.map T.toLinearMap = L := by
    rw [S, NormalSpan, Submodule.map_span]
    congr 1
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨f.toLinearMap, hf, rfl⟩
  let J : S ≃ₗ[ℝ] L := T.ofSubmodules S L hmap
  obtain ⟨_, _, _, _, hrestriction⟩ :=
    OriginalNormalRestriction.original_normal_restriction hc hs hg
      (fun q => by obtain ⟨b⟩ := h3 q; exact ⟨nativeChart b, rfl⟩)
      (fun q r h => hinj h) p (nativeChart a) rfl
  obtain ⟨g, E0, _, _, _, hE0, _, _⟩ :=
    hrestriction e (fun f => ⟨huniq f, fun h => h ▸ he⟩)
  let E : S ≃ₗ[ℝ] (ThreeSpace →ᵃ[ℝ] ℝ) := J.trans E0
  have hE (f : S) : E f = restriction (nativeChart a) f := by
    have hh := LinearMap.congr_fun hE0 (J f)
    exact hh
  let A := affineCoordinates ThreeSpace
  let Q : S ≃ₗ[ℝ] (ℝ × ThreeSpace) := E.trans A
  have hQ (f : S) : Q f = coordinates (nativeChart a) f := by
    rw [show Q f = A (E f) from rfl, hE]
    rfl
  let k : Fin 3 → S := fun i => Q.symm (0, EuclideanSpace.single i 1)
  have hk (i : Fin 3) : coordinates (nativeChart a) (k i) = (0, EuclideanSpace.single i 1) :=
    (hQ (k i)).symm.trans (Q.apply_symm_apply _)
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
        rw [hQ, hQ]
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


open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OrthogonalJointCompletion CommonPositiveExtension SingleLabelNormalBody
open WholePairBallConfirmation OriginalFacePolarity ContinuousFrameSum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
  {p : pure C u} {e : V →ₗ[ℝ] ℝ} {a : FullBall3Chart C u p}

/-- Actual normalized images of every original base state other than the anchor. -/
def actualImage (n : NativeChart C u p e a) : Set ThreeSpace :=
  (fun x : V => ((u - e) x)⁻¹ • n.H x) '' (base C u \ {(p : V)})

/-- The perspective of the entire original base is convex. -/
theorem actual_image_convex (n : NativeChart C u p e a) : Convex ℝ (actualImage n) := by
  rintro z ⟨x,hx,rfl⟩ w ⟨y,hy,rfl⟩ s t hs ht hst
  have gx := n.gap_positive x hx.1 (by simpa using hx.2)
  have gy := n.gap_positive y hy.1 (by simpa using hy.2)
  let d := s / (u-e) x + t / (u-e) y
  have hd : 0 < d := by
    dsimp [d]
    by_cases h : 0 < s
    · exact add_pos_of_pos_of_nonneg (div_pos h gx) (div_nonneg ht gy.le)
    · have hsz : s = 0 := le_antisymm (le_of_not_gt h) hs
      have htz : t = 1 := by linarith
      rw [hsz,htz]
      simpa only [LinearMap.sub_apply,zero_div,one_div,zero_add] using inv_pos.mpr gy
  let q := (s / (u-e) x / d) • x + (t / (u-e) y / d) • y
  have hsum : s / (u-e) x / d + t / (u-e) y / d = 1 := by
    rw [← add_div]; exact div_self hd.ne'
  have hq : q ∈ base C u := base_convex C u hx.1 hy.1
    (div_nonneg (div_nonneg hs gx.le) hd.le)
    (div_nonneg (div_nonneg ht gy.le) hd.le) hsum
  have hgap : (u-e) q = d⁻¹ := by
    simp only [q,map_add,map_smul,smul_eq_mul]
    field_simp
    nlinarith [hst]
  have hqp : q ≠ (p : V) := by
    intro h
    rw [h,n.gap_normal.2] at hgap
    exact (inv_ne_zero hd.ne') hgap.symm
  refine ⟨q,⟨hq,by simpa using hqp⟩,?_⟩
  change ((u-e) q)⁻¹ • n.H q = _
  rw [hgap,inv_inv]
  simp only [q,map_add,map_smul,smul_add,smul_smul]
  congr 1 <;> congr 1 <;> field_simp

/-- The source direction function, with the full original base in its supremum. -/
def rho (n : NativeChart C u p e a) (v : ThreeSpace) : ℝ :=
  sSup ((fun z => -⟪v, z⟫) '' actualImage n)

theorem actual_image_bound (n : NativeChart C u p e a) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ actualImage n, ‖z‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := n.uniform_bound
  refine ⟨M, hM, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  have hpos := n.gap_positive x hx.1 (by simpa using hx.2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact (inv_mul_le_iff₀ hpos).mpr (by simpa [mul_comm] using hb x hx.1.1)

private theorem chart_not_anchor (n : NativeChart C u p e a) (w : ThreeSpace) :
    a.param w ≠ (p : V) := by
  intro h
  have hh := n.gap_chart w
  rw [h, n.gap_normal.2] at hh
  norm_num at hh

theorem ball_subset_actual (n : NativeChart C u p e a) :
    Metric.closedBall (0 : ThreeSpace) 1 ⊆ actualImage n := by
  intro w hw
  refine ⟨a.param w, ⟨(chart_mem (nativeChart a) (by simpa using hw)).1,
    by simpa using chart_not_anchor n w⟩, ?_⟩
  change ((u-e) (a.param w))⁻¹ • n.H (a.param w) = w
  rw [n.gap_chart, n.chart_eq]
  simp

theorem rho_values_bdd (n : NativeChart C u p e a) (v : ThreeSpace) :
    BddAbove ((fun z => -⟪v, z⟫) '' actualImage n) := by
  obtain ⟨M, _, hb⟩ := actual_image_bound n
  refine ⟨‖v‖ * M, ?_⟩
  rintro r ⟨z, hz, rfl⟩
  calc
    -⟪v, z⟫ ≤ |⟪v, z⟫| := neg_le_abs _
    _ ≤ ‖v‖ * ‖z‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * M := mul_le_mul_of_nonneg_left (hb z hz) (norm_nonneg _)

/-- The support bound is exactly the original all-state ratio inequality. -/
theorem rho_le_iff (n : NativeChart C u p e a) (v : ThreeSpace) (r : ℝ) :
    rho n v ≤ r ↔ ∀ x ∈ base C u, x ≠ (p : V) →
      -⟪v, n.H x⟫ ≤ r * (u - e) x := by
  have hne : (((fun z => -⟪v, z⟫) '' actualImage n) : Set ℝ).Nonempty :=
    ⟨0, 0, ball_subset_actual n (by simp), by simp⟩
  rw [rho, csSup_le_iff (rho_values_bdd n v) hne]
  constructor
  · intro h x hx hxp
    have hh := h _ (mem_image_of_mem _ (show ((u-e) x)⁻¹ • n.H x ∈ actualImage n from
      ⟨x, ⟨hx, by simpa using hxp⟩, rfl⟩))
    change -⟪v, ((u-e) x)⁻¹ • n.H x⟫ ≤ r at hh
    rw [inner_smul_right] at hh
    have hp := n.gap_positive x hx hxp
    have heq : -((u-e) x)⁻¹ * ⟪v, n.H x⟫ = -⟪v, n.H x⟫ / (u-e) x := by ring
    rw [neg_mul_eq_neg_mul, heq, div_le_iff₀ hp] at hh
    exact hh
  · intro h r' hr'
    obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := hr'
    have hp := n.gap_positive x hx.1 (by simpa using hx.2)
    change -⟪v, ((u-e) x)⁻¹ • n.H x⟫ ≤ r
    rw [inner_smul_right]
    have heq : -(((u-e) x)⁻¹ * ⟪v, n.H x⟫) = -⟪v, n.H x⟫ / (u-e) x := by ring
    rw [heq, div_le_iff₀ hp]
    exact h x hx.1 (by simpa using hx.2)

/-- Every actual unit direction has support at least one. -/
theorem rho_unit_lower (n : NativeChart C u p e a) {v : ThreeSpace} (hv : ‖v‖ = 1) :
    1 ≤ rho n v := by
  have hz : -v ∈ actualImage n := ball_subset_actual n (by simpa [hv])
  have hh := le_csSup (rho_values_bdd n v) (mem_image_of_mem (fun z => -⟪v,z⟫) hz)
  simpa [rho, inner_neg_right, real_inner_self_eq_norm_sq, hv] using hh

/-- The actual linear directional coordinate on the entire original carrier. -/
def direction (n : NativeChart C u p e a) (v : ThreeSpace) : V →ₗ[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ ThreeSpace v).toLinearMap.comp n.H

private theorem direction_mem (n : NativeChart C u p e a) (v : ThreeSpace) :
    direction n v ∈ NormalSpan C u p := by
  have heq : direction n v = ∑ i : Fin 3,
      v i • (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).toLinearMap.comp n.H := by
    ext x
    simp [direction, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, mul_comm]
  rw [heq]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (n.coordinate_mem i))

private theorem normal_reconstruction (n : NativeChart C u p e a)
    {b : V →ₗ[ℝ] ℝ} (hb : b ∈ NormalSpan C u p) (v : ThreeSpace)
    (hformula : ∀ w, b (a.param w) = 1 + ⟪v,w⟫) :
    b = u - e + direction n v := by
  have hmem : u-e + direction n v ∈ NormalSpan C u p :=
    Submodule.add_mem _ (Submodule.subset_span n.gap_normal) (direction_mem n v)
  have heq : (⟨b,hb⟩ : NormalSpan C u p) = ⟨u-e+direction n v,hmem⟩ := by
    apply n.restrictEquiv.injective
    rw [n.restrict_eq, n.restrict_eq]
    ext w
    change b (a.param w) = (u-e) (a.param w) + ⟪v,n.H (a.param w)⟫
    rw [n.gap_chart, n.chart_eq, hformula]
  exact congrArg Subtype.val heq

private theorem rho_le_one_iff_slope (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (n : NativeChart C u p e a) (v : ThreeSpace) :
    rho n v ≤ 1 ↔ v ∈ slopeBody (nativeChart a) := by
  rw [slope_body_original]
  constructor
  · intro hr
    let b := u-e+direction n v
    have hformula (w) : b (a.param w) = 1 + ⟪v,w⟫ := by
      change (u-e) (a.param w) + ⟪v,n.H (a.param w)⟫ = _
      rw [n.gap_chart, n.chart_eq]
    have hbp : b p = 0 := by simp [b, direction, n.at_anchor, n.gap_normal.2]
    have hpos : ∀ x ∈ C, 0 ≤ b x := nonneg_on_cone (base_compact hc hs) hs (fun q => by
      by_cases hq : (q : V) = p
      · simpa [hq] using hbp.ge
      · have hh := (rho_le_iff n v 1).mp hr q (pure_mem q) hq
        change 0 ≤ (u-e) q + ⟪v,n.H q⟫
        linarith)
    exact ⟨b, hpos, hbp, by simpa using hformula 0, fun w _ => hformula w⟩
  · rintro ⟨b, hbpos, hbp, hbc, hformula⟩
    have hall (w) : b (a.param w) = 1 + ⟪v,w⟫ := by
      have hspan : affineSpan ℝ (Metric.closedBall (0 : ThreeSpace) 1) = ⊤ :=
        (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
          ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
      have heq : b.toAffineMap.comp a.param =
          (InnerProductSpace.toDual ℝ ThreeSpace v).toLinearMap.toAffineMap +
          AffineMap.const ℝ _ (1 : ℝ) :=
        AffineMap.ext_on hspan (fun w hw => by simpa [add_comm] using hformula w hw)
      have hh := congrArg (fun F => F w) heq
      simpa [add_comm] using hh
    have heq := normal_reconstruction n (Submodule.subset_span ⟨hbpos,hbp⟩) v hall
    apply (rho_le_iff n v 1).mpr
    intro x hx _
    have hh := hbpos x hx.1
    rw [heq] at hh
    change 0 ≤ (u-e) x + ⟪v,n.H x⟫ at hh
    linarith

/-- Unit support is equivalent to an actual full original effect separating the
actual antipodal chart points. No positive or restriction bridge is assumed. -/
theorem rho_one_iff_antipodal (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : EB3 C u)
    (n : NativeChart C u p e a) (v : ThreeSpace) (hv : ‖v‖ = 1) :
    rho n v = 1 ↔ ∃ f : V →ₗ[ℝ] ℝ,
      proper C u f ∧ f (a.param v) = 1 ∧ f (a.param (-v)) = 0 := by
  have hB : exclusionBalls C u := fun q => (h3 q).map nativeChart
  have hq : a.param v ∈ pure C u := by
    have hh := chart_boundary hc hs hg hB p (nativeChart a)
    exact ((hh.symm ▸ (show a.param v ∈ a.param '' Metric.sphere 0 1 from
      ⟨v,by simpa using hv,rfl⟩))).2
  let q : pure C u := ⟨a.param v,hq⟩
  have hxm := chart_mem (nativeChart a) (by simpa using hv.le : ‖-v‖ ≤ 1)
  have hz := ExclusionWidthCompactness.comparison_zero_iff hs hg q hxm.1
  constructor
  · intro hr
    have hgap := (zero_gap_iff hc hs hg hB p (nativeChart a) v hv).mpr
      ((rho_le_one_iff_slope hc hs n v).mp hr.le)
    obtain ⟨_, f, hf, hfr⟩ := hz.mp hgap
    exact ⟨f, hf.1, hf.2, hfr⟩
  · rintro ⟨f,hf,hfv,hfm⟩
    have hgap : gap (nativeChart a) v = 0 := hz.mpr ⟨hxm.1,f,⟨hf,hfv⟩,hfm⟩
    exact le_antisymm ((rho_le_one_iff_slope hc hs n v).mpr
      ((zero_gap_iff hc hs hg hB p (nativeChart a) v hv).mp hgap)) (rho_unit_lower n hv)

/-- Full oscillation on the entire original exclusion, before taking effects. -/
def oscillation (a : FullBall3Chart C u p) (f : V →L[ℝ] ℝ) : ℝ :=
  ExclusionWidthCompactness.oscillation (exclusion C u p) f

/-- Width uses the whole original effect interval, including every linear effect. -/
def width (a : FullBall3Chart C u p) : ℝ :=
  sSup ((fun f : V →L[ℝ] ℝ => oscillation a f) '' effects C u)

private theorem chart_extrema (f : V →L[ℝ] ℝ) :
    ∃ v : ThreeSpace, ‖v‖ = 1 ∧
      f (a.param v) = f (a.param 0) + ‖slope (nativeChart a) f‖ ∧
      f (a.param (-v)) = f (a.param 0) - ‖slope (nativeChart a) f‖ ∧
      ∀ w : ThreeSpace, ‖w‖ ≤ 1 →
        f (a.param 0) - ‖slope (nativeChart a) f‖ ≤ f (a.param w) ∧
        f (a.param w) ≤ f (a.param 0) + ‖slope (nativeChart a) f‖ := by
  let z : ThreeSpace := slope (nativeChart a) f
  have hb (w : ThreeSpace) (hw : ‖w‖ ≤ 1) :
      f (a.param 0) - ‖z‖ ≤ f (a.param w) ∧
      f (a.param w) ≤ f (a.param 0) + ‖z‖ := by
    have hh := (abs_real_inner_le_norm z w).trans
      (mul_le_of_le_one_right (norm_nonneg _) hw)
    rw [abs_le] at hh
    rw [slope_formula (nativeChart a) f w]
    constructor <;> linarith
  by_cases hz : z = 0
  · let v : ThreeSpace := EuclideanSpace.single 0 1
    have hv : ‖v‖ = 1 := by simp [v, EuclideanSpace.single]
    refine ⟨v,hv,?_,?_,hb⟩
    · rw [slope_formula (nativeChart a) f v]
      change _ = _ + ‖z‖
      simp [hz, show slope (nativeChart a) f = z from rfl]
    · rw [slope_formula (nativeChart a) f (-v)]
      change _ = _ - ‖z‖
      simp [hz, show slope (nativeChart a) f = z from rfl]
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let v := ‖z‖⁻¹ • z
    have hv : ‖v‖ = 1 := by simp [v,norm_smul,hzpos.ne']
    have hi : ⟪z,v⟫ = ‖z‖ := by
      simp only [v,inner_smul_right,real_inner_self_eq_norm_sq]
      field_simp
    refine ⟨v,hv,?_,?_,hb⟩
    · rw [slope_formula (nativeChart a) f v]
      change _ = _ + ‖z‖
      rw [hi]
    · rw [slope_formula (nativeChart a) f (-v)]
      change _ = _ - ‖z‖
      rw [inner_neg_right, hi]
      ring

/-- A real original effect attains width, with actual unit antipodal maximizing
and minimizing states in the whole original chart. -/
theorem width_attained (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (a : FullBall3Chart C u p) :
    ∃ f : V →ₗ[ℝ] ℝ, proper C u f ∧ ∃ v : ThreeSpace, ‖v‖ = 1 ∧
      width a = f (a.param v) - f (a.param (-v)) ∧
      (∀ x ∈ exclusion C u p, f x ≤ f (a.param v)) ∧
      (∀ x ∈ exclusion C u p, f (a.param (-v)) ≤ f x) := by
  have hF : IsCompact (exclusion C u p) := by
    rw [← a.whole]
    exact (isCompact_closedBall (0 : ThreeSpace) 1).image a.param.continuous_of_finiteDimensional
  have hne : (exclusion C u p).Nonempty := ⟨a.param 0,chart_mem (nativeChart a) (by simp)⟩
  obtain ⟨f,hf,y,hy,z,hz,hw,_,horder⟩ :=
    ExclusionWidthCompactness.width_attained hs hg hF hne
  obtain ⟨v,hv,hmax,hmin,hbound⟩ := chart_extrema (a := a) f
  have hxp := chart_mem (nativeChart a) hv.le
  have hxm := chart_mem (nativeChart a) (by simpa using hv.le : ‖-v‖ ≤ 1)
  have htop (x) (hx : x ∈ exclusion C u p) : f x ≤ f (a.param v) := by
    obtain ⟨w,hw,rfl⟩ := a.whole.symm ▸ hx
    rw [hmax]
    exact (hbound w (by simpa using hw)).2
  have hbot (x) (hx : x ∈ exclusion C u p) : f (a.param (-v)) ≤ f x := by
    obtain ⟨w,hw,rfl⟩ := a.whole.symm ▸ hx
    rw [hmin]
    exact (hbound w (by simpa using hw)).1
  have hymax : f y = f (a.param v) := le_antisymm (htop y hy) (horder _ hxp).2
  have hzmin : f z = f (a.param (-v)) := le_antisymm (horder _ hxm).1 (hbot z hz)
  refine ⟨f.toLinearMap,hf,v,hv,?_,htop,hbot⟩
  change ExclusionWidthCompactness.width C u (exclusion C u p) = _
  rw [hw,hymax,hzmin]
  rfl

/-- Width one is exactly unit support in some actual original unit direction. -/
theorem width_one_iff_rho_one (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : EB3 C u)
    (n : NativeChart C u p e a) :
    width a = 1 ↔ ∃ v : ThreeSpace, ‖v‖ = 1 ∧ rho n v = 1 := by
  have hB : exclusionBalls C u := fun q => (h3 q).map nativeChart
  have hF : {x | x ∈ base C u ∧ comparison C u p x = 0} = exclusion C u p := by
    ext x
    exact ⟨fun hx => (ExclusionWidthCompactness.comparison_zero_iff hs hg p hx.1).mp hx.2,
      fun hx => ⟨hx.1,(ExclusionWidthCompactness.comparison_zero_iff hs hg p hx.1).mpr hx⟩⟩
  have hwidth : width a ≤ 1 := by
    have hh := (ExclusionWidthCompactness.original_exclusion_width hc hs hg hB p).1.2
    rw [hF] at hh
    exact hh
  constructor
  · intro hw
    obtain ⟨f,hf,v,hv,hwidth,_,_⟩ := width_attained hs hg a
    have hxp := chart_mem (nativeChart a) hv.le
    have hxm := chart_mem (nativeChart a) (by simpa using hv.le : ‖-v‖ ≤ 1)
    have hp := (hf _ hxp.1.1).2
    rw [hxp.1.2] at hp
    have hm := (hf _ hxm.1.1).1
    rw [hw] at hwidth
    refine ⟨v,hv,(rho_one_iff_antipodal hc hs hg h3 n v hv).mpr ⟨f,hf,?_,?_⟩⟩
    · linarith
    · linarith
  · rintro ⟨v,hv,hr⟩
    obtain ⟨f,hf,hfv,hfm⟩ := (rho_one_iff_antipodal hc hs hg h3 n v hv).mp hr
    have hcompact : IsCompact (exclusion C u p) := by
      rw [← a.whole]
      exact (isCompact_closedBall (0 : ThreeSpace) 1).image a.param.continuous_of_finiteDimensional
    have hle := ExclusionWidthCompactness.effect_difference_le_width hs hg hcompact
      (f := f.toContinuousLinearMap) hf (chart_mem (nativeChart a) hv.le)
      (chart_mem (nativeChart a) (by simpa using hv.le : ‖-v‖ ≤ 1))
    change f (a.param v) - f (a.param (-v)) ≤ width a at hle
    rw [hfv,hfm] at hle
    exact le_antisymm hwidth (by simpa using hle)


/-- The original closed shadow shell, without an assumed closed ratio image. -/
def shell (n : NativeChart C u p e a) : Set ThreeSpace := closure (actualImage n)

private theorem shell_geometry (n : NativeChart C u p e a) :
    IsCompact (shell n) ∧ Convex ℝ (shell n) ∧
    Metric.closedBall (0 : ThreeSpace) 1 ⊆ shell n := by
  obtain ⟨M,_,hb⟩ := actual_image_bound n
  have hbound : actualImage n ⊆ Metric.closedBall 0 M := by
    intro z hz; simpa using hb z hz
  refine ⟨(isCompact_closedBall (0 : ThreeSpace) M).of_isClosed_subset
    isClosed_closure (closure_minimal hbound Metric.isClosed_closedBall),
    (actual_image_convex n).closure,?_⟩
  exact (ball_subset_actual n).trans subset_closure

/-- Closing the actual image preserves exactly its directional support bounds. -/
theorem shell_support_le_iff (n : NativeChart C u p e a) (v : ThreeSpace) (r : ℝ) :
    (∀ z ∈ shell n, -⟪v,z⟫ ≤ r) ↔ rho n v ≤ r := by
  have hne : (((fun z => -⟪v,z⟫) '' actualImage n) : Set ℝ).Nonempty :=
    ⟨0,0,ball_subset_actual n (by simp),by simp⟩
  rw [rho, csSup_le_iff (rho_values_bdd n v) hne]
  constructor
  · intro h r hr
    obtain ⟨z,hz,rfl⟩ := hr
    exact h z (subset_closure hz)
  · intro h
    apply closure_minimal (fun z hz => h _ (mem_image_of_mem _ hz))
    exact isClosed_le
      (show Continuous (fun z : ThreeSpace => -⟪v,z⟫) from by fun_prop) continuous_const

/-- The same finite positive image bound makes rho globally Lipschitz. -/
theorem rho_lipschitz (n : NativeChart C u p e a) :
    ∃ M : ℝ, 0 < M ∧ ∀ v w : ThreeSpace,
      |rho n v - rho n w| ≤ M * ‖v-w‖ := by
  obtain ⟨M,hM,hb⟩ := actual_image_bound n
  have hle (v w : ThreeSpace) : rho n v ≤ rho n w + M * ‖v-w‖ := by
    have hne : (((fun z => -⟪v,z⟫) '' actualImage n) : Set ℝ).Nonempty :=
      ⟨0,0,ball_subset_actual n (by simp),by simp⟩
    apply (csSup_le_iff (rho_values_bdd n v) hne).mpr
    rintro r ⟨z,hz,rfl⟩
    have hw : -⟪w,z⟫ ≤ rho n w :=
      le_csSup (rho_values_bdd n w) (mem_image_of_mem _ hz)
    have hh := (neg_le_abs ⟪v-w,z⟫).trans (abs_real_inner_le_norm (v-w) z)
    have hm := mul_le_mul_of_nonneg_left (hb z hz) (norm_nonneg (v-w))
    rw [inner_sub_left] at hh
    nlinarith
  refine ⟨M,hM,fun v w => abs_le.mpr ⟨?_,?_⟩⟩
  · have hh := hle w v
    rw [norm_sub_rev] at hh
    linarith
  · linarith [hle v w]

private theorem rho_continuous (n : NativeChart C u p e a) : Continuous (rho n) := by
  obtain ⟨M,hM,hb⟩ := rho_lipschitz n
  apply (show LipschitzWith ⟨M,hM.le⟩ (rho n) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro v w
  change dist (rho n v) (rho n w) ≤ M * dist v w
  simpa [Real.dist_eq,dist_eq_norm] using hb v w

/-- The minimum is taken over the entire actual unit sphere. -/
def minimum (n : NativeChart C u p e a) : ℝ :=
  sInf (rho n '' Metric.sphere (0 : ThreeSpace) 1)

/-- The actual sphere minimum is attained and is at least one. -/
theorem minimum_attained (n : NativeChart C u p e a) :
    ∃ v : ThreeSpace, ‖v‖ = 1 ∧ rho n v = minimum n ∧
      1 ≤ minimum n ∧ ∀ w : ThreeSpace, ‖w‖ = 1 → minimum n ≤ rho n w := by
  have hne : (Metric.sphere (0 : ThreeSpace) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  obtain ⟨v,hv,hm⟩ := (isCompact_sphere (0 : ThreeSpace) 1).exists_isMinOn hne
    (rho_continuous n).continuousOn
  have hnorm : ‖v‖ = 1 := by simpa using hv
  have hleast : IsLeast (rho n '' Metric.sphere (0 : ThreeSpace) 1) (rho n v) :=
    ⟨mem_image_of_mem _ hv, by rintro _ ⟨w,hw,rfl⟩; exact hm hw⟩
  have heq : rho n v = minimum n := hleast.csInf_eq.symm
  refine ⟨v,hnorm,heq,?_,?_⟩
  · rw [← heq]; exact rho_unit_lower n hnorm
  · intro w hw
    rw [← heq]
    exact hm (by simpa using hw)

private theorem shell_support_bound (n : NativeChart C u p e a) (v : ThreeSpace)
    {z : ThreeSpace} (hz : z ∈ shell n) : -⟪v,z⟫ ≤ rho n v :=
  (shell_support_le_iff n v (rho n v)).mpr le_rfl z hz

/-- Every boundary point in the original inner ball is its own outward unit normal.
The source direction of rho is the negative of that actual contact point. -/
theorem ball_frontier_direction (n : NativeChart C u p e a) {z : ThreeSpace}
    (hz : z ∈ Metric.closedBall 0 1) (hb : z ∈ frontier (shell n)) :
    ‖z‖ = 1 ∧ rho n (-z) = 1 := by
  obtain ⟨hc,hconv,hball⟩ := shell_geometry n
  have hi : (interior (shell n)).Nonempty := ⟨0,interior_mono hball
    (Metric.ball_subset_interior_closedBall (by simp : (0 : ThreeSpace) ∈ Metric.ball 0 1))⟩
  obtain ⟨f,hf,hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point hconv hb.2 hi
  let w : ThreeSpace := (InnerProductSpace.toDual ℝ ThreeSpace).symm f
  have hw : w ≠ 0 := by
    intro h
    apply hf
    have hh := congrArg (InnerProductSpace.toDual ℝ ThreeSpace) h
    simpa [w] using hh
  let b : ThreeSpace := ‖w‖⁻¹ • w
  have hbn : ‖b‖ = 1 := norm_smul_inv_norm hw
  have hbw : ⟪b,w⟫ = ‖w‖ := by
    simp only [b,inner_smul_left,conj_trivial,real_inner_self_eq_norm_sq]
    field_simp
  have hbz : ⟪b,z⟫ ≥ 1 := by
    have hm := hmax b (hball (by simpa using hbn.le))
    have he (x : ThreeSpace) : f x = ⟪w,x⟫ := by simp [w]
    rw [he b,he z] at hm
    have hwbn : ⟪w,b⟫ = ‖w‖ := (real_inner_comm w b).symm.trans hbw
    rw [hwbn] at hm
    simp only [b,real_inner_smul_left]
    change ‖w‖⁻¹ * ⟪w,z⟫ ≥ 1
    exact (one_le_inv_mul₀ (norm_pos_iff.mpr hw)).mpr hm
  have hzn : ‖z‖ ≤ 1 := by simpa using hz
  have hub : ⟪b,z⟫ ≤ ‖z‖ := by
    simpa [hbn] using (le_abs_self ⟪b,z⟫).trans (abs_real_inner_le_norm b z)
  have hzone : ‖z‖ = 1 := by linarith
  have hbzone : ⟪b,z⟫ = 1 := by linarith
  have hb_eq : b = z := by
    have hh := (inner_eq_norm_mul_iff_real (x := b) (y := z)).mp
      (by simpa [hbn,hzone] using hbzone)
    simpa [hbn,hzone] using hh
  refine ⟨hzone,le_antisymm ?_ (rho_unit_lower n (by simpa using hzone))⟩
  apply (shell_support_le_iff n (-z) 1).mp
  intro y hy
  have hm := hmax y hy
  have he (x : ThreeSpace) : f x = ‖w‖ * ⟪b,x⟫ := by
    simp only [b,inner_smul_left,conj_trivial]
    rw [← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw),one_mul]
    simp [w]
  rw [he y,he z,hb_eq,real_inner_self_eq_norm_sq,hzone] at hm
  have hh := (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hw)).mp
    (show ‖w‖ * ⟪z,y⟫ ≤ ‖w‖ * 1 by simpa using hm)
  simpa using hh

/-- A unit support value one gives the actual inner-ball boundary point -v. -/
theorem rho_one_frontier (n : NativeChart C u p e a) {v : ThreeSpace}
    (hv : ‖v‖ = 1) (hr : rho n v = 1) : -v ∈ frontier (shell n) := by
  have hz := (shell_geometry n).2.2 (show -v ∈ Metric.closedBall 0 1 by simpa [hv])
  apply (mem_frontier_iff_notMem_interior hz).mpr
  intro hi
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  let y : ThreeSpace := -v + (ε/2) • (-v)
  have hy : y ∈ Metric.ball (-v) ε := by
    rw [Metric.mem_ball,dist_eq_norm]
    simp only [y,add_sub_cancel_left,norm_smul,norm_neg,hv,mul_one,
      Real.norm_eq_abs,abs_of_pos (half_pos hε)]
    linarith
  have hh := shell_support_bound n v (hsub hy)
  rw [hr] at hh
  simp only [y,inner_add_right,inner_smul_right,inner_neg_right,
    real_inner_self_eq_norm_sq,hv] at hh
  nlinarith

/-- Exact minimum/contact equivalence on the actual shell and entire sphere. -/
theorem minimum_one_iff_contact (n : NativeChart C u p e a) :
    minimum n = 1 ↔ (Metric.closedBall (0 : ThreeSpace) 1 ∩ frontier (shell n)).Nonempty := by
  constructor
  · intro hm
    obtain ⟨v,hv,hr,-,-⟩ := minimum_attained n
    exact ⟨-v,by simpa [hv],rho_one_frontier n hv (hr.trans hm)⟩
  · rintro ⟨z,hz,hb⟩
    obtain ⟨hn,hr⟩ := ball_frontier_direction n hz hb
    obtain ⟨v,hv,hmin,hlower,hle⟩ := minimum_attained n
    exact le_antisymm ((hle (-z) (by simpa using hn)).trans_eq hr) hlower

/-- The actual closed convex shell is the intersection of its unit support halfspaces. -/
theorem mem_shell_iff (n : NativeChart C u p e a) (z : ThreeSpace) :
    z ∈ shell n ↔ ∀ v : ThreeSpace, ‖v‖ = 1 → -⟪v,z⟫ ≤ rho n v := by
  constructor
  · intro hz v _; exact shell_support_bound n v hz
  · intro h
    by_contra hz
    obtain ⟨f,r,hs,hr⟩ := geometric_hahn_banach_closed_point
      (shell_geometry n).2.1 (shell_geometry n).1.isClosed hz
    let w : ThreeSpace := (InnerProductSpace.toDual ℝ ThreeSpace).symm f
    have hf0 : f 0 < f z := (hs 0 ((shell_geometry n).2.2 (by simp))).trans hr
    have hw : w ≠ 0 := by
      intro he
      have heq : f = 0 := by
        have hh := congrArg (InnerProductSpace.toDual ℝ ThreeSpace) he
        simpa [w] using hh
      simp [heq] at hf0
    let v : ThreeSpace := -(‖w‖⁻¹ • w)
    have hv : ‖v‖ = 1 := by simpa [v] using norm_smul_inv_norm (𝕜 := ℝ) hw
    have he (x : ThreeSpace) : -⟪v,x⟫ = ‖w‖⁻¹ * f x := by simp [v,real_inner_smul_left,w]
    have hub : rho n v ≤ ‖w‖⁻¹ * r := by
      apply (shell_support_le_iff n v _).mp
      intro y hy
      rw [he]
      exact mul_le_mul_of_nonneg_left (hs y hy).le (inv_nonneg.mpr (norm_nonneg _))
    have hh := (h v hv).trans hub
    rw [he] at hh
    have hlt := mul_lt_mul_of_pos_left hr (inv_pos.mpr (norm_pos_iff.mpr hw))
    exact (not_lt_of_ge hh) hlt

/-- The minimum support radius gives containment of the entire scaled inner ball. -/
theorem minimum_ball_subset (n : NativeChart C u p e a) :
    Metric.closedBall (0 : ThreeSpace) (minimum n) ⊆ shell n := by
  obtain ⟨w,hw,hr,hl,hm⟩ := minimum_attained n
  intro z hz
  apply (mem_shell_iff n z).mpr
  intro v hv
  have hn : ‖z‖ ≤ minimum n := by simpa using hz
  calc
    -⟪v,z⟫ ≤ |⟪v,z⟫| := neg_le_abs _
    _ ≤ ‖v‖ * ‖z‖ := abs_real_inner_le_norm _ _
    _ ≤ minimum n := by simpa [hv] using hn
    _ ≤ rho n v := hm v hv

/-- Strict support margin puts every original inner-ball state in the shell interior
and bounds every distance to every shell boundary point. -/
theorem strict_margin (n : NativeChart C u p e a) (hδ : 1 < minimum n) :
    Metric.closedBall (0 : ThreeSpace) 1 ⊆ interior (shell n) ∧
    ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1,
      ∀ y ∈ frontier (shell n), minimum n - 1 ≤ dist x y := by
  have hbi : Metric.ball (0 : ThreeSpace) (minimum n) ⊆ interior (shell n) :=
    (Metric.ball_subset_interior_closedBall).trans (interior_mono (minimum_ball_subset n))
  constructor
  · intro x hx
    exact hbi (by simpa using lt_of_le_of_lt (show ‖x‖ ≤ 1 by simpa using hx) hδ)
  · intro x hx y hy
    have hny : minimum n ≤ ‖y‖ := by
      by_contra h
      have hyi : y ∈ interior (shell n) := hbi (by simpa using lt_of_not_ge h)
      exact hy.2 hyi
    have hnx : ‖x‖ ≤ 1 := by simpa using hx
    have hh : ‖y‖ ≤ ‖x‖ + dist x y := by
      simpa [dist_eq_norm,norm_sub_rev] using norm_le_insert x y
    linarith

/-- The ordinary distance between the whole original inner ball and the shell boundary. -/
def boundaryDistance (n : NativeChart C u p e a) : ℝ :=
  sInf ((fun q : ThreeSpace × ThreeSpace => dist q.1 q.2) ''
    (Metric.closedBall (0 : ThreeSpace) 1 ×ˢ frontier (shell n)))

private theorem frontier_nonempty (n : NativeChart C u p e a) :
    (frontier (shell n)).Nonempty := by
  obtain ⟨hc,_,hb⟩ := shell_geometry n
  apply nonempty_frontier_iff.mpr
  refine ⟨⟨0,hb (by simp)⟩,?_⟩
  obtain ⟨R,hR,hr⟩ := hc.isBounded.exists_pos_norm_le
  obtain ⟨z,hz⟩ := exists_norm_eq ThreeSpace (show 0 ≤ R+1 by linarith)
  intro h
  have hh := hr z (by simp [h])
  linarith

/-- The strict original support margin bounds the actual set distance positively. -/
theorem strict_boundary_distance (n : NativeChart C u p e a) (hδ : 1 < minimum n) :
    minimum n - 1 ≤ boundaryDistance n ∧ 0 < minimum n - 1 := by
  obtain ⟨y,hy⟩ := frontier_nonempty n
  have hne : ((fun q : ThreeSpace × ThreeSpace => dist q.1 q.2) ''
      (Metric.closedBall (0 : ThreeSpace) 1 ×ˢ frontier (shell n))).Nonempty :=
    ⟨dist 0 y,⟨0,y⟩,⟨by simp,hy⟩,rfl⟩
  refine ⟨le_csInf hne ?_,by linarith⟩
  rintro d ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
  exact (strict_margin n hδ).2 x hx y hy


/-- The complete contact and strict-scale conclusion for the same actual coordinates. -/
def ContactCriterion {p : pure C u} {e : V →ₗ[ℝ] ℝ} {a : FullBall3Chart C u p}
    (n : NativeChart C u p e a) : Prop :=
  (width a = 1 ↔ minimum n = 1) ∧
  (minimum n = 1 ↔
    (Metric.closedBall (0 : ThreeSpace) 1 ∩ frontier (shell n)).Nonempty) ∧
  (1 < minimum n →
    minimum n • Metric.closedBall (0 : ThreeSpace) 1 ⊆ shell n ∧
    Metric.closedBall (0 : ThreeSpace) 1 ⊆ interior (shell n) ∧
    minimum n - 1 ≤ boundaryDistance n ∧ 0 < minimum n - 1)

/-- The full original cone/base/effect telescope derives its own normal chart and
all three equivalent contact conditions, with the entire strict-scale conclusion. -/
theorem regular_anchor_contact_criterion
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : EB3 C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : pure C u) (e : V →ₗ[ℝ] ℝ) (he : common C u p e)
    (hreg : Regular C u p) (a : FullBall3Chart C u p) :
    ∃ n : NativeChart C u p e a, ContactCriterion n := by
  obtain ⟨n⟩ := regular_anchor_native hc hs hg h3 hinj p e he hreg a
  have hm : (∃ v : ThreeSpace, ‖v‖ = 1 ∧ rho n v = 1) ↔ minimum n = 1 := by
    obtain ⟨w,hw,hr,hl,hmin⟩ := minimum_attained n
    constructor
    · rintro ⟨v,hv,hvone⟩
      exact le_antisymm ((hmin v hv).trans_eq hvone) hl
    · intro h
      exact ⟨w,hw,hr.trans h⟩
  refine ⟨n,(width_one_iff_rho_one hc hs hg h3 n).trans hm,
    minimum_one_iff_contact n,?_⟩
  intro hδ
  have hnonneg : 0 ≤ minimum n := le_trans zero_le_one hδ.le
  have hscale : minimum n • Metric.closedBall (0 : ThreeSpace) 1 =
      Metric.closedBall (0 : ThreeSpace) (minimum n) := by
    rw [smul_unitClosedBall, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  refine ⟨?_,(strict_margin n hδ).1,(strict_boundary_distance n hδ).1,
    (strict_boundary_distance n hδ).2⟩
  rw [hscale]
  exact minimum_ball_subset n


end D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
