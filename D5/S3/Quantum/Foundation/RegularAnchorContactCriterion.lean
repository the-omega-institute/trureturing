/- GID: D5/S3/Quantum/Foundation/RegularAnchorContactCriterion
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/RegularAnchorContactCriterion
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Actual base perspectives determine shell contact and strict support-distance margins. -/

import D5.S3.Quantum.Foundation.OriginalNormalRestriction
import D5.S3.Quantum.Foundation.CommonPositiveExtension
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import D5.S3.Quantum.Foundation.OriginalWidthContact

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Full original normal coordinates, actual ratios and shell contact geometry. -/

noncomputable section
open Set
open scoped RealInnerProductSpace Pointwise

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

/-- The same chart in the existing native chart carrier. -/
abbrev nativeChart {p : V} (a : FullBall3Chart C u p) : ExclusionChart C u p :=
  ⟨3, by decide, a.param, a.injective, a.whole⟩

/-- Signed span of the entire original positive annihilator cone. -/
abbrev NormalSpan (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : V) :=
  Submodule.span ℝ (zeroPositive C u p)

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

/-- Every actual unit direction has support at least one. -/
theorem rho_unit_lower (n : NativeChart C u p e a) {v : ThreeSpace} (hv : ‖v‖ = 1) :
    1 ≤ rho n v := by
  have hz : -v ∈ actualImage n := ball_subset_actual n (by simpa [hv])
  have hh := le_csSup (rho_values_bdd n v) (mem_image_of_mem (fun z => -⟪v,z⟫) hz)
  simpa [rho, inner_neg_right, real_inner_self_eq_norm_sq, hv] using hh

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

end D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
