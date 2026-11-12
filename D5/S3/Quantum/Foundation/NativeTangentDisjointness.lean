/- GID: D5/S3/Quantum/Foundation/NativeTangentDisjointness
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/NativeTangentDisjointness
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.Arg]
   utility: none
   digest: Distinct original neighbor balls have disjoint native tangent spaces. -/

import D5.S3.Quantum.Foundation.CommonPositiveExtension
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Module

/-! Native VIII108.6 under the original weak orthogonal-pair hypotheses. -/

noncomputable section
open Set
open scoped RealInnerProductSpace Pointwise

namespace D5.S3.Quantum.Foundation.NativeTangentDisjointness

open CircuitBalancedConfirmation FacetZeroGluing WholePairBallConfirmation
open ExclusionBallFaces OrthogonalJointCompletion CommonPositiveExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The intrinsic linear directions of the entire original exclusion ball. -/
def directions {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {q : V}
    (_b : ExclusionChart C u q) : Submodule ℝ V := vectorSpan ℝ (exclusion C u q)

/-- The tangent at p, using the original common effect and the full ball. -/
def tangent {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {q : V}
    (b : ExclusionChart C u q) (ap : V →ₗ[ℝ] ℝ) : Submodule ℝ V :=
  directions b ⊓ LinearMap.ker ap

omit [FiniteDimensional ℝ V] in
private theorem directions_range {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {q : V}
    (b : ExclusionChart C u q) : directions b = LinearMap.range b.param.linear := by
  have hspan : affineSpan ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) 1) = ⊤ := by
    apply affineSpan_eq_top_of_nonempty_interior
    exact ⟨0, by
      rw [(convex_closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) (1 : ℝ)).convexHull_eq]
      exact Metric.ball_subset_interior_closedBall (by simp)⟩
  have hv : vectorSpan ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) 1) = ⊤ := by
    rw [← direction_affineSpan, hspan]
    exact AffineSubspace.direction_top _ _ _
  rw [directions, ← b.whole, ← b.param.map_vectorSpan, hv, Submodule.map_top]

private theorem circle_angle (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    ∃ t : ℝ, Real.cos t = c ∧ Real.sin t = s := by
  let z : ℂ := ⟨c,s⟩
  have hn : ‖z‖ = 1 := by
    have hh := Complex.sq_norm z
    simp only [Complex.normSq_apply, z] at hh
    nlinarith [norm_nonneg z]
  have hz : z ≠ 0 := by intro he; simp [he] at hn
  exact ⟨z.arg, by simpa [hn,z] using Complex.cos_arg hz,
    by simpa [hn,z] using Complex.sin_arg z⟩

private theorem tangent_coordinates [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p))
    (p q : pure C u) (hqp : (q : V) ∈ exclusion C u p)
    (b : ExclusionChart C u q) (z : V) (hz : z ∈ tangent b (a p)) (hz0 : z ≠ 0) :
    ∃ e w : EuclideanSpace ℝ (Fin b.dim), ‖e‖ = 1 ∧ b.param e = p ∧
      w ≠ 0 ∧ ⟪e,w⟫ = 0 ∧ b.param.linear w = z := by
  have hpq := (exclusion_symmetric p q).mp hqp
  obtain ⟨e,heball,hep⟩ := b.whole.symm ▸ hpq
  have he : ‖e‖ = 1 := by
    obtain ⟨r,hr,_⟩ := (whole_joint_completion hc hs hg hB hW).1 p q hqp.2
    obtain ⟨s,hsr,_⟩ := (whole_joint_completion hc hs hg hB hW).1 p r hr.2.2.2.1
    have hq : (q : V) ∈ exclusion C u p ∩ exclusion C u r :=
      ⟨hqp,(exclusion_symmetric q r).mp ⟨pure_mem r,hr.2.2.2.2.1⟩⟩
    have hqs : q = s := Subtype.ext (by simpa [hsr.1] using hq)
    have hpair : pairBase C u p r = exclusion C u q := hqs.symm ▸ hsr.2.1
    let bb : BallChart C u p r := {
      dim := b.dim
      dim_pos := b.dim_pos
      param := b.param
      injective := b.injective
      whole := b.whole.trans hpair.symm }
    exact chart_pure_norm bb (by simpa using heball) (hep.symm ▸ p.property)
  obtain ⟨w,hwz⟩ := (directions_range b ▸ hz.1 : z ∈ LinearMap.range b.param.linear)
  have hw0 : w ≠ 0 := by intro hw; apply hz0; simpa [hw] using hwz.symm
  let f := AffineMap.const ℝ (EuclideanSpace ℝ (Fin b.dim)) (1 : ℝ) -
    (a p).toAffineMap.comp b.param
  have hfpos (v) (hv : ‖v‖ ≤ 1) : 0 ≤ f v := by
    have hx : b.param v ∈ exclusion C u q := b.whole ▸ ⟨v,by simpa using hv,rfl⟩
    have hh := ((ha p).1.1 _ hx.1.1).2
    rw [hx.1.2] at hh
    exact sub_nonneg.mpr hh
  have hfe : f e = 0 := by simp [f,hep,(ha p).1.2]
  have hf := affine_zero_antipode f (n := -e) (by simpa using he) hfpos (by simpa using hfe)
  have hfne : f (-e) ≠ 0 := by
    intro hzero
    obtain ⟨r,hr,_⟩ := (whole_joint_completion hc hs hg hB hW).1 p q hqp.2
    have hrq : (r : V) ∈ exclusion C u q := ⟨pure_mem r,hr.2.2.2.2.1⟩
    obtain ⟨v,hv,hvr⟩ := b.whole.symm ▸ hrq
    have hpr : a p r = 0 := (ha p).2 _ ⟨pure_mem r,hr.2.2.2.1⟩
    have hh := hf v
    simp [f,hvr,hpr,hzero] at hh
  have hfw : f w = f 0 := by
    have hl : a p (b.param w) - a p (b.param 0) = 0 := by
      have hl := b.param.linear_apply_vsub w 0
      have hh := congrArg (a p) hl
      simp only [vsub_eq_sub, sub_zero, map_sub, hwz] at hh
      exact hh.symm.trans hz.2
    change 1-a p (b.param w) = 1-a p (b.param 0)
    linarith
  have hi : ⟪e,w⟫ = 0 := by
    have h1 := hf w
    have h0 := hf 0
    simp only [inner_neg_left, inner_zero_right] at h1 h0
    have hm : f (-e) * ⟪e,w⟫ = 0 := by nlinarith
    exact (mul_eq_zero.mp hm).resolve_left hfne
  exact ⟨e,w,he,hep,hw0,hi,hwz⟩

private structure NativeArc {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (a : pure C u → (V →ₗ[ℝ] ℝ)) (p q : pure C u) (z : V) where
  r : pure C u
  B : V →ₗ[ℝ] ℝ
  h : ℝ
  hpos : 0 < h
  joint : jointThird C u p q r
  sum : a p+a q+a r=u
  circle : ∀ c s : ℝ, c^2+s^2=1 → ∃ x : pure C u,
    (x : V) = ((1+c)/2) • (p : V) + ((1-c)/2) • (r : V) + (s*h) • z ∧
    a x = ((1+c)/2) • a p + ((1-c)/2) • a r + s • B
  at_z : B z = 1/(2*h)
  vanish : ∀ x ∈ Submodule.span ℝ (insert (p : V) (exclusion C u p)), B x = 0

private theorem native_arc [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p)) (harc : ArcFamily a)
    (p q : pure C u) (hqp : (q : V) ∈ exclusion C u p)
    (b : ExclusionChart C u q) (z : V) (hz : z ∈ tangent b (a p)) (hz0 : z ≠ 0) :
    Nonempty (NativeArc a p q z) := by
  obtain ⟨e,w,he,hep,hw,hew,hwz⟩ := tangent_coordinates hc hs hg hB hW a ha p q hqp b z hz hz0
  obtain ⟨r,γ,B,her,hsum,hrp,hγ,hag,hBp,hBr,hBz,hvan⟩ := harc q p b e w he hep hw hew
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hrq : (r : V) ∈ exclusion C u q :=
    b.whole ▸ ⟨-e,by simp [he],her⟩
  obtain ⟨r0,hr0,_⟩ := (whole_joint_completion hc hs hg hB hW).1 p q hqp.2
  have hrr : r = r0 := Subtype.ext (by
    have hh : (r : V) ∈ exclusion C u p ∩ exclusion C u q := ⟨hrp,hrq⟩
    simpa [hr0.1] using hh)
  have hj : jointThird C u p q r := hrr.symm ▸ hr0
  refine ⟨{
    r := r
    B := B
    h := ‖w‖⁻¹
    hpos := inv_pos.mpr hwpos
    joint := hj
    sum := hsum
    circle := ?_
    at_z := ?_
    vanish := hvan }⟩
  · intro c s hcs
    obtain ⟨t,hct,hst⟩ := circle_angle c s hcs
    refine ⟨γ t,?_,by simpa [hct,hst] using hag t⟩
    rw [hγ,hct,hst]
    have hb (v) : b.param v = b.param.linear v+b.param 0 := by
      simpa [add_comm] using congrFun b.param.decomp v
    rw [← hep,← her,hb (c • e+s • (‖w‖⁻¹ • w)),hb e,hb (-e)]
    simp only [map_add,map_smul,map_neg,smul_smul,← hwz]
    module
  · rw [← hwz,hBz]
    field_simp

omit [FiniteDimensional ℝ V] in
private theorem tangent_zero_readings
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p))
    {p q : pure C u} {z : V} (A : NativeArc a p q z)
    (s : pure C u) (hsp : (s : V) ∈ exclusion C u p) : a s z = 0 := by
  have hsp0 : a s p = 0 := (ha s).2 _ ((exclusion_symmetric p s).mp hsp)
  have hquad (t : ℝ) : 0 ≤ a s A.r * (t*t) + (2*A.h*a s z)*t + 0 := by
    let d := 1+t^2
    have hd : 0 < d := by dsimp [d]; positivity
    obtain ⟨x,hx,_⟩ := A.circle ((1-t^2)/d) (2*t/d) (by dsimp [d]; field_simp; ring)
    have hp := ((ha s).1.1 x (pure_mem x).1).1
    have hv := congrArg (a s) hx
    simp only [map_add,map_smul,smul_eq_mul] at hv
    rw [hsp0,mul_zero,zero_add] at hv
    have heval : a s x * d = a s A.r * (t*t) + (2*A.h*a s z)*t + 0 := by
      rw [hv]
      dsimp [d]
      field_simp
      ring
    rw [← heval]
    exact mul_nonneg hp hd.le
  have hd := discrim_le_zero hquad
  simp only [discrim,mul_zero,sub_zero] at hd
  have hz : 2*A.h*a s z = 0 := by nlinarith [sq_nonneg (2*A.h*a s z)]
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) A.hpos.ne')

private theorem cross_bound
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p))
    {p q q' : pure C u} {z : V} (hz : a p z = 0)
    (A : NativeArc a p q z) (A' : NativeArc a p q' z) : (A'.h/A.h)^2 ≤ a A.r A'.r := by
  have hrp : (A.r : V) ∈ exclusion C u p := ⟨pure_mem A.r,A.joint.2.2.2.1⟩
  have hr'p : (A'.r : V) ∈ exclusion C u p := ⟨pure_mem A'.r,A'.joint.2.2.2.1⟩
  have hapr' : a p A'.r = 0 := (ha p).2 _ hr'p
  have harp : a A.r p = 0 := (ha A.r).2 _ ((exclusion_symmetric p A.r).mp hrp)
  have harz := tangent_zero_readings a ha A A.r hrp
  have hBp : A.B p = 0 := A.vanish _ (Submodule.subset_span (Set.mem_insert _ _))
  have hBr' : A.B A'.r = 0 := A.vanish _ (Submodule.subset_span (Set.mem_insert_of_mem _ hr'p))
  obtain ⟨y,hy,_⟩ := A'.circle 0 1 (by norm_num)
  have heval (f : V →ₗ[ℝ] ℝ) : f y = (1/2 : ℝ)*f p+(1/2 : ℝ)*f A'.r+A'.h*f z := by
    have hh := congrArg f hy
    simpa only [map_add,map_smul,smul_eq_mul,add_zero,sub_zero,one_mul] using hh
  have hapy : a p y = 1/2 := by rw [heval,(ha p).1.2,hapr',hz]; ring
  have hary : a A.r y = a A.r A'.r/2 := by rw [heval,harp,harz]; ring
  have hBy : A.B y = A'.h/(2*A.h) := by rw [heval,hBp,hBr',A.at_z]; ring
  have hquad (t : ℝ) : 0 ≤ t^2+a A.r A'.r+2*(A'.h/A.h)*t := by
    let d := 1+t^2
    have hd : 0 < d := by dsimp [d]; positivity
    obtain ⟨x,_,hx⟩ := A.circle ((t^2-1)/d) (2*t/d) (by dsimp [d]; field_simp; ring)
    have hp := ((ha x).1.1 y (pure_mem y).1).1
    have hv := LinearMap.congr_fun hx y
    change a x y = ((1+(t^2-1)/d)/2)*a p y+
      ((1-(t^2-1)/d)/2)*a A.r y+(2*t/d)*A.B y at hv
    rw [hapy,hary,hBy] at hv
    have heval : a x y*(2*d)=t^2+a A.r A'.r+2*(A'.h/A.h)*t := by
      rw [hv]
      dsimp [d]
      field_simp
      ring
    rw [← heval]
    exact mul_nonneg hp (by positivity)
  have hh := hquad (-(A'.h/A.h))
  nlinarith

/-- Original VIII108.6: every two distinct original neighbors, every pair of
entire charts, and all vectors in their intrinsic tangent spaces. -/
theorem whole_native_tangent_disjointness [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) :
    ∃ a : pure C u → (V →ₗ[ℝ] ℝ),
      (∀ p : pure C u, common C u p (a p)) ∧
      (∀ (p : pure C u) f, common C u p f → f = a p) ∧
      ∀ p q q' : pure C u, (q : V) ∈ exclusion C u p →
        (q' : V) ∈ exclusion C u p → q ≠ q' →
        ∀ (b : ExclusionChart C u q) (b' : ExclusionChart C u q'),
          tangent b (a p) ⊓ tangent b' (a p) = ⊥ := by
  classical
  obtain ⟨a,ha,hu,harc⟩ := whole_arc_effect hc hs hg hB hW
  refine ⟨a,ha,hu,?_⟩
  intro p q q' hqp hq'p hqq' b b'
  apply le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  by_contra hz0
  obtain ⟨A⟩ := native_arc hc hs hg hB hW a ha harc p q hqp b z hz.1 hz0
  obtain ⟨A'⟩ := native_arc hc hs hg hB hW a ha harc p q' hq'p b' z hz.2 hz0
  have hrp : (A.r : V) ∈ exclusion C u p := ⟨pure_mem A.r,A.joint.2.2.2.1⟩
  have hr'p : (A'.r : V) ∈ exclusion C u p := ⟨pure_mem A'.r,A'.joint.2.2.2.1⟩
  have hrr' : A.r ≠ A'.r := by
    intro he
    obtain ⟨v,hv,_⟩ := (whole_joint_completion hc hs hg hB hW).1 p A.r hrp.2
    have hq : (q : V) ∈ exclusion C u p ∩ exclusion C u A.r :=
      ⟨hqp,(exclusion_symmetric q A.r).mp ⟨pure_mem A.r,A.joint.2.2.2.2.1⟩⟩
    have hq' : (q' : V) ∈ exclusion C u p ∩ exclusion C u A.r := by
      rw [he]
      exact ⟨hq'p,(exclusion_symmetric q' A'.r).mp ⟨pure_mem A'.r,A'.joint.2.2.2.2.1⟩⟩
    apply hqq'
    apply Subtype.ext
    have h1 : (q : V) = v := by simpa [hv.1] using hq
    have h2 : (q' : V) = v := by simpa [hv.1] using hq'
    exact h1.trans h2.symm
  have hstrict {q q' : pure C u} (A : NativeArc a p q z) (A' : NativeArc a p q' z)
      (hne : A.r ≠ A'.r) : a A.r A'.r < 1 := by
    have hle : a A.r A'.r ≤ 1 := by
      simpa [(pure_mem A'.r).2] using ((ha A.r).1.1 A'.r (pure_mem A'.r).1).2
    apply lt_of_le_of_ne hle
    intro he
    have hr'p : (A'.r : V) ∈ exclusion C u p := ⟨pure_mem A'.r,A'.joint.2.2.2.1⟩
    have hp0 : a p A'.r = 0 := (ha p).2 _ hr'p
    have hs := LinearMap.congr_fun A.sum A'.r
    change a p A'.r+a q A'.r+a A.r A'.r=u A'.r at hs
    have hq0 : a q A'.r=0 := by rw [hp0,he,(pure_mem A'.r).2] at hs; linarith
    have hh : (A'.r : V) ∈ exclusion C u p ∩ exclusion C u q :=
      ⟨hr'p,pure_mem A'.r,a q,(ha q).1,hq0⟩
    have heq : A'.r = A.r := Subtype.ext (by simpa [A.joint.1] using hh)
    exact hne heq.symm
  have hc0 : 0 ≤ a A.r A'.r := ((ha A.r).1.1 _ (pure_mem A'.r).1).1
  have hc'0 : 0 ≤ a A'.r A.r := ((ha A'.r).1.1 _ (pure_mem A.r).1).1
  have hc1 := hstrict A A' hrr'
  have hc'1 := hstrict A' A hrr'.symm
  have hb := cross_bound a ha hz.1.2 A A'
  have hb' := cross_bound a ha hz.1.2 A' A
  have hp : (A'.h/A.h)^2*(A.h/A'.h)^2=1 := by
    field_simp [A.hpos.ne',A'.hpos.ne']
  have hle := mul_le_mul hb hb' (sq_nonneg _) hc0
  rw [hp] at hle
  have hlt : a A.r A'.r * a A'.r A.r < 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1.le) hc'0]
  linarith

#print axioms whole_native_tangent_disjointness

end D5.S3.Quantum.Foundation.NativeTangentDisjointness
