/- GID: D5/S3/Quantum/Foundation/PositiveComplementaryProjections
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/PositiveComplementaryProjections
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Positive primal and algebraic-dual projections on the original cone. -/

import D5.S3.Quantum.Foundation.CommonPositiveExtension
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.LinearAlgebra.Projection

noncomputable section
open Set
open scoped RealInnerProductSpace Pointwise

namespace D5.S3.Quantum.Foundation.PositiveComplementaryProjections

open CircuitBalancedConfirmation FacetZeroGluing WholePairBallConfirmation
open ExclusionBallFaces OrthogonalJointCompletion CommonPositiveExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Linear range intersected with the actual positive cone. -/
def positiveImage {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : PointedCone ℝ E) (T : E →ₗ[ℝ] E) : Set E :=
  (LinearMap.range T : Set E) ∩ (C : Set E)

/-- Linear kernel intersected with the actual positive cone. -/
def positiveKernel {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : PointedCone ℝ E) (T : E →ₗ[ℝ] E) : Set E :=
  (LinearMap.ker T : Set E) ∩ (C : Set E)

/-- The original algebraic positive dual, paired by evaluation. -/
def positiveDual (C : PointedCone ℝ V) : PointedCone ℝ (Module.Dual ℝ V) :=
  PointedCone.dual (Module.Dual.eval ℝ V) (C : Set V)

/-- Genuine finite dimensional dual transport, without identifying V with V*. -/
def primal (S : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V) : V →ₗ[ℝ] V :=
  (Module.evalEquiv ℝ V).symm.toLinearMap.comp
    (S.dualMap.comp (Module.evalEquiv ℝ V).toLinearMap)

private theorem primal_eval (S : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V)
    (f : Module.Dual ℝ V) (x : V) : f (primal S x) = S f x := by
  exact Module.apply_evalEquiv_symm_apply ℝ V f _

private theorem dual_separates {x y : V} (h : ∀ f : Module.Dual ℝ V, f x = f y) : x = y := by
  apply (Module.evalEquiv ℝ V).injective
  exact LinearMap.ext h

private theorem affine_ball_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E →ᵃ[ℝ] ℝ} (h : ∀ z, ‖z‖ ≤ 1 → f z = g z) : f = g := by
  apply AffineMap.ext_on (s := Metric.closedBall (0 : E) 1)
    (affineSpan_eq_top_of_nonempty_interior ?_)
  · intro z hz
    exact h z (by simpa using hz)
  · exact ⟨0, by
      rw [(convex_closedBall (0 : E) (1 : ℝ)).convexHull_eq]
      exact Metric.ball_subset_interior_closedBall (by simp)⟩

private theorem chart_mem {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p : V}
    (b : ExclusionChart C u p) {z} (hz : ‖z‖ ≤ 1) : b.param z ∈ exclusion C u p := by
  rw [← b.whole]
  exact ⟨z, by simpa using hz, rfl⟩

/-- Annihilation of the entire original D_p forces the original positive ray.
The two antipode restrictions are reconstructed on ALL V by the actual
positive inverse at q; no spectrality premise is used. -/
private theorem annihilator_ray [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p))
    (hcharts : ∀ (p : pure C u) (b : ExclusionChart C u p),
      ∃ Λ, ExtensionLaws b (a p) Λ)
    (p : pure C u) (f : V →ₗ[ℝ] ℝ) (hf : ∀ x ∈ C, 0 ≤ f x)
    (hz : ∀ x ∈ exclusion C u p, f x = 0) : f = f p • a p := by
  have comp := (whole_joint_completion hc hs hg hB hW).1
  obtain ⟨q,r,hpqr⟩ := (whole_joint_completion hc hs hg hB hW).2.1 p
  have hqDp : (q : V) ∈ exclusion C u p := ⟨pure_mem q,hpqr.2.2.1⟩
  have hrDp : (r : V) ∈ exclusion C u p := ⟨pure_mem r,hpqr.2.2.2.1⟩
  obtain ⟨s,hrps,_⟩ := comp r p
    ((exclusion_symmetric p r).mp hrDp).2
  have hqs : q = s := Subtype.ext (by
    have hh : (q : V) ∈ exclusion C u r ∩ exclusion C u p :=
      ⟨(exclusion_symmetric q r).mp ⟨pure_mem r,hpqr.2.2.2.2.1⟩,hqDp⟩
    simpa [hrps.1] using hh)
  subst s
  obtain ⟨b⟩ := hB q
  let d : BallChart C u r p := {
    dim := b.dim, dim_pos := b.dim_pos, param := b.param,
    injective := b.injective, whole := b.whole.trans hrps.2.1.symm }
  obtain ⟨m,hm,hmr⟩ := endpoint_coordinates r p d
  have hmrb : b.param m = r := hmr
  have hF := affine_zero_antipode ((restriction b) f) (by simpa using hm : ‖-m‖ = 1)
    (fun z hz => hf _ (chart_mem b hz).1.1) (by simpa [restriction,hmrb] using hz r hrDp)
  have hA := affine_zero_antipode ((restriction b) (a p)) (by simpa using hm : ‖-m‖ = 1)
    (fun z hz => ((ha p).1.1 _ (chart_mem b hz).1.1).1)
    (by simpa [restriction,hmrb] using (ha p).2 r hrDp)
  obtain ⟨w,hw,hwp⟩ := b.whole.symm ▸
    ((exclusion_symmetric p q).mp hqDp)
  have hcoeff : f (b.param (-m)) = f p * a p (b.param (-m)) := by
    have hfwp := hF w
    have hawp := hA w
    change f (b.param w) = _ at hfwp
    change a p (b.param w) = _ at hawp
    rw [hwp] at hfwp hawp
    rw [(ha p).1.2] at hawp
    nlinarith
  have hres : restriction b f = restriction b (f p • a p) := by
    ext z
    change f (b.param z) = f p * a p (b.param z)
    have h1 := hF z
    have h2 := hA z
    change f (b.param z) = _ at h1
    change a p (b.param z) = _ at h2
    rw [h1,h2,hcoeff]
    ring
  obtain ⟨Λ,hΛ⟩ := hcharts q b
  have hfq : f ∈ zeroPositive C u q := ⟨hf,hz q hqDp⟩
  have haq : f p • a p ∈ zeroPositive C u q :=
    ⟨fun x hx => mul_nonneg (hf p (pure_mem p).1) ((ha p).1.1 x hx).1,
      by simp [(ha p).2 q hqDp]⟩
  exact (hΛ.inverse_positive f hfq).symm.trans
    ((congrArg Λ hres).trans (hΛ.inverse_positive _ haq))

private theorem unique_maximum [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (p : pure C u) (ap : V →ₗ[ℝ] ℝ)
    (ha : common C u p ap) : {x | x ∈ base C u ∧ ap x = 1} = {(p : V)} := by
  let M : Set V := {x | x ∈ base C u ∧ ap x = 1}
  have hM : M = ap.toContinuousLinearMap.toExposed (base C u) := by
    ext x
    constructor
    · rintro ⟨hx,hax⟩
      refine ⟨hx,fun y hy => ?_⟩
      change ap y ≤ ap x
      rw [hax]
      simpa [hy.2] using (ha.1.1 y hy.1).2
    · rintro ⟨hx,hmax⟩
      have hp := hmax p (pure_mem p)
      change ap p ≤ ap x at hp
      exact ⟨hx,le_antisymm (by simpa [hx.2] using (ha.1.1 x hx.1).2)
        (ha.1.2 ▸ hp)⟩
  have hex : IsExposed ℝ (base C u) M := hM ▸ ContinuousLinearMap.toExposed.isExposed
  have hpM : (p : V) ∈ M := ⟨pure_mem p,ha.1.2⟩
  have hproper : M ≠ base C u := by
    obtain ⟨q,hq⟩ := ((exclusion_ball_faces hc hs hg hB).1 p).1.nonempty
    intro he
    have hh : q ∈ M := he.symm ▸ hq.1
    have hz := ha.2 q hq
    exact zero_ne_one (hz.symm.trans hh.2)
  rcases (exclusion_ball_faces hc hs hg hB).2.1 M ⟨p,hpM⟩
    (hex.convex (base_convex C u)) hex.isExtreme hproper with ⟨q,hq⟩ | ⟨q,hq⟩
  · have hpq : (p : V) = q := by simpa [hq] using hpM
    simpa [M,hpq] using hq
  · have hpD : (p : V) ∈ exclusion C u q := hq ▸ hpM
    have hqp := (exclusion_symmetric p q).mpr hpD
    obtain ⟨r,hr,_⟩ := (whole_joint_completion hc hs hg hB hW).1 p q hqp.2
    have hrD : (r : V) ∈ exclusion C u p ∩ exclusion C u q := by
      rw [hr.1]; simp
    have hrM : (r : V) ∈ M := hq.symm ▸ hrD.2
    exact (zero_ne_one ((ha.2 r hrD.1).symm.trans hrM.2)).elim

end D5.S3.Quantum.Foundation.PositiveComplementaryProjections
