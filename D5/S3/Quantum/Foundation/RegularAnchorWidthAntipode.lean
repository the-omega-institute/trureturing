/- GID: D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/RegularAnchorWidthAntipode
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Full original effect width detects actual regular-anchor antipodal contact. -/

import D5.S3.Quantum.Foundation.RegularAnchorNormalChart

/-! Width and support use the entire original effect interval and normalized base. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.RegularAnchorWidthAntipode

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OrthogonalJointCompletion CommonPositiveExtension SingleLabelNormalBody
open RegularAnchorNormalChart WholePairBallConfirmation OriginalFacePolarity ContinuousFrameSum


variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
  {p : pure C u} {e : V →ₗ[ℝ] ℝ} {a : FullBall3Chart C u p}

/-- Actual normalized images of every original base state other than the anchor. -/
def actualImage (n : NativeChart C u p e a) : Set ThreeSpace :=
  (fun x : V => ((u - e) x)⁻¹ • n.H x) '' (base C u \ {(p : V)})

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
  constructor
  · intro hr
    have hgap := (zero_gap_iff hc hs hg hB p (nativeChart a) v hv).mpr
      ((rho_le_one_iff_slope hc hs n v).mp hr.le)
    obtain ⟨f,hf,hfr⟩ := comparison_attained hs hg q (a.param (-v))
    exact ⟨f,hf.1,hf.2,hfr.trans hgap⟩
  · rintro ⟨f,hf,hfv,hfm⟩
    have hgap : gap (nativeChart a) v = 0 := by
      apply le_antisymm
      · change comparison C u (a.param v) (a.param (-v)) ≤ 0
        apply (csInf_le (a := f (a.param (-v))) ?_ (show f (a.param (-v)) ∈
          {r | ∃ k : V →ₗ[ℝ] ℝ, confirms C u (a.param v) k ∧ k (a.param (-v)) = r} from
          ⟨f,⟨hf,hfv⟩,rfl⟩)).trans_eq hfm
        exact ⟨0,by rintro r ⟨k,hk,rfl⟩; exact (hk.1 _
          (chart_mem (nativeChart a) (by simpa using hv.le : ‖-v‖ ≤ 1)).1.1).1⟩
      · change 0 ≤ comparison C u (a.param v) (a.param (-v))
        apply le_csInf (s := {r | ∃ k : V →ₗ[ℝ] ℝ, confirms C u (a.param v) k ∧
          k (a.param (-v)) = r}) ⟨0,f,⟨hf,hfv⟩,hfm⟩
        rintro r ⟨k,hk,rfl⟩
        exact (hk.1 _ (chart_mem (nativeChart a) (by simpa using hv.le : ‖-v‖ ≤ 1)).1.1).1
    exact le_antisymm ((rho_le_one_iff_slope hc hs n v).mpr
      ((zero_gap_iff hc hs hg hB p (nativeChart a) v hv).mp hgap)) (rho_unit_lower n hv)

/-- Full oscillation on the entire original exclusion, before taking effects. -/
def oscillation (a : FullBall3Chart C u p) (f : V →L[ℝ] ℝ) : ℝ :=
  sSup (f '' exclusion C u p) - sInf (f '' exclusion C u p)

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

private theorem oscillation_formula (f : V →L[ℝ] ℝ) :
    oscillation a f = 2 * ‖slope (nativeChart a) f‖ := by
  obtain ⟨v,hv,hmax,hmin,hbound⟩ := chart_extrema (a := a) f
  have hs : sSup (f '' exclusion C u p) = f (a.param v) := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨a.param v,chart_mem (nativeChart a) hv.le,rfl⟩,?_⟩
    rintro r ⟨x,hx,rfl⟩
    obtain ⟨w,hw,rfl⟩ := a.whole.symm ▸ hx
    rw [hmax]
    exact (hbound w (by simpa using hw)).2
  have hi : sInf (f '' exclusion C u p) = f (a.param (-v)) := by
    apply IsLeast.csInf_eq
    refine ⟨⟨a.param (-v),chart_mem (nativeChart a) (by simpa using hv.le : ‖-v‖ ≤ 1),rfl⟩,?_⟩
    rintro r ⟨x,hx,rfl⟩
    obtain ⟨w,hw,rfl⟩ := a.whole.symm ▸ hx
    rw [hmin]
    exact (hbound w (by simpa using hw)).1
  rw [oscillation, hs, hi, hmax, hmin]
  ring

private theorem width_slope : width a =
    sSup ((fun f : V →L[ℝ] ℝ => 2 * ‖slope (nativeChart a) f‖) '' effects C u) := by
  unfold width
  congr 1
  ext r
  simp only [mem_image]
  exact exists_congr fun f => and_congr_right fun _ => by rw [oscillation_formula]

/-- A real original effect attains width, with actual unit antipodal maximizing
and minimizing states in the whole original chart. -/
theorem width_attained (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (a : FullBall3Chart C u p) :
    ∃ f : V →ₗ[ℝ] ℝ, proper C u f ∧ ∃ v : ThreeSpace, ‖v‖ = 1 ∧
      width a = f (a.param v) - f (a.param (-v)) ∧
      (∀ x ∈ exclusion C u p, f x ≤ f (a.param v)) ∧
      (∀ x ∈ exclusion C u p, f (a.param (-v)) ≤ f x) := by
  have hne : (effects C u).Nonempty := ⟨0,fun x _ => ⟨by simp,by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hs x ‹x ∈ C› hx).le⟩⟩
  have hcont : Continuous (fun f : V →L[ℝ] ℝ => 2 * ‖slope (nativeChart a) f‖) :=
    continuous_const.mul ((slope (nativeChart a)).continuous_of_finiteDimensional.norm)
  obtain ⟨f,hf,hfwidth⟩ := (effects_compact hs hg).exists_sSup_image_eq hne hcont.continuousOn
  obtain ⟨v,hv,hmax,hmin,hbound⟩ := chart_extrema (a := a) f
  refine ⟨f.toLinearMap,hf,v,hv,?_,?_,?_⟩
  · change width a = f (a.param v) - f (a.param (-v))
    rw [width_slope, hfwidth, hmax, hmin]
    ring
  · intro x hx
    obtain ⟨w,hw,rfl⟩ := a.whole.symm ▸ hx
    change f (a.param w) ≤ f (a.param v)
    rw [hmax]
    exact (hbound w (by simpa using hw)).2
  · intro x hx
    obtain ⟨w,hw,rfl⟩ := a.whole.symm ▸ hx
    change f (a.param (-v)) ≤ f (a.param w)
    rw [hmin]
    exact (hbound w (by simpa using hw)).1

private theorem effect_slope_bound {f : V →L[ℝ] ℝ} (hf : proper C u f.toLinearMap) :
    2 * ‖slope (nativeChart a) f‖ ≤ 1 := by
  obtain ⟨v,hv,hmax,hmin,_⟩ := chart_extrema (a := a) f
  have hxp := chart_mem (nativeChart a) hv.le
  have hxm := chart_mem (nativeChart a) (by simpa using hv.le : ‖-v‖ ≤ 1)
  have hh := (hf (a.param v) hxp.1.1).2
  have hl := (hf (a.param (-v)) hxm.1.1).1
  change f (a.param v) ≤ u (a.param v) at hh
  change 0 ≤ f (a.param (-v)) at hl
  rw [hxp.1.2] at hh
  rw [hmax] at hh
  rw [hmin] at hl
  linarith

/-- Width one is exactly unit support in some actual original unit direction. -/
theorem width_one_iff_rho_one (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (h3 : EB3 C u)
    (n : NativeChart C u p e a) :
    width a = 1 ↔ ∃ v : ThreeSpace, ‖v‖ = 1 ∧ rho n v = 1 := by
  have hne : (effects C u).Nonempty := ⟨0,fun x hx => ⟨by simp,by
    by_cases hz : x = 0
    · simp [hz]
    · exact (hs x hx hz).le⟩⟩
  have hwidth : width a ≤ 1 := by
    rw [width_slope]
    apply csSup_le (hne.image _)
    rintro r ⟨f,hf,rfl⟩
    exact effect_slope_bound hf
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
    have hb : BddAbove ((fun f : V →L[ℝ] ℝ => 2 * ‖slope (nativeChart a) f‖) '' effects C u) :=
      ⟨1,by rintro r ⟨f,hf,rfl⟩; exact effect_slope_bound hf⟩
    have hle : 2 * ‖slope (nativeChart a) f.toContinuousLinearMap‖ ≤ width a := by
      rw [width_slope]
      exact le_csSup hb ⟨f.toContinuousLinearMap,hf,rfl⟩
    have hp := slope_formula (nativeChart a) f.toContinuousLinearMap v
    have hm := slope_formula (nativeChart a) f.toContinuousLinearMap (-v)
    change f (a.param v) = f (a.param 0) + _ at hp
    change f (a.param (-v)) = f (a.param 0) + _ at hm
    rw [hfv] at hp
    rw [hfm,inner_neg_right] at hm
    have hi := real_inner_le_norm (slope (nativeChart a) f.toContinuousLinearMap) v
    rw [hv,mul_one] at hi
    exact le_antisymm hwidth (by linarith)

end D5.S3.Quantum.Foundation.RegularAnchorWidthAntipode
