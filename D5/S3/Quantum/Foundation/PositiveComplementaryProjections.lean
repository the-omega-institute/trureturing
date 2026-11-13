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

/-! Full original-domain mathematical positive projections and their native cone faces. -/

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
    change f (b.param w) = f (b.param (-m)) / 2 * (1 + ⟪-m,w⟫) at hfwp
    change a p (b.param w) = a p (b.param (-m)) / 2 * (1 + ⟪-m,w⟫) at hawp
    rw [hwp] at hfwp hawp
    rw [(ha p).1.2] at hawp
    calc
      f (b.param (-m)) = f (b.param (-m)) * 1 := by ring
      _ = f (b.param (-m)) * (a p (b.param (-m)) / 2 * (1 + ⟪-m,w⟫)) := by rw [← hawp]
      _ = (f (b.param (-m)) / 2 * (1 + ⟪-m,w⟫)) * a p (b.param (-m)) := by ring
      _ = f p * a p (b.param (-m)) := by rw [← hfwp]
  have hres : restriction b f = restriction b (f p • a p) := by
    ext z
    change f (b.param z) = f p * a p (b.param z)
    have h1 := hF z
    have h2 := hA z
    change f (b.param z) = f (b.param (-m)) / 2 * (1 + ⟪-m,z⟫) at h1
    change a p (b.param z) = a p (b.param (-m)) / 2 * (1 + ⟪-m,z⟫) at h2
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


private theorem cone_zero {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (p : pure C u)
    (ap : V →ₗ[ℝ] ℝ) (ha : common C u p ap) :
    PointedCone.hull ℝ (exclusion C u p) = C ⊓ PointedCone.ofSubmodule (LinearMap.ker ap) := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx => ⟨hx.1.1,ha.2 x hx⟩)
  · intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using (PointedCone.hull ℝ (exclusion C u p)).zero_mem
    have hux := hs x hx.1 hx0
    have hn := normalized_mem hs hx.1 hx0
    have hnD : (u x)⁻¹ • x ∈ exclusion C u p :=
      ⟨hn,ap,ha.1,by simp [map_smul,show ap x = 0 from hx.2]⟩
    have hh := (PointedCone.hull ℝ (exclusion C u p)).smul_mem hux.le
      (PointedCone.subset_hull hnD)
    simpa [smul_smul,hux.ne'] using hh

private theorem hull_base (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) : PointedCone.hull ℝ (base C u) = C := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx => hx.1)
  · intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using (PointedCone.hull ℝ (base C u)).zero_mem
    have hux := hs x hx hx0
    have hh := (PointedCone.hull ℝ (base C u)).smul_mem hux.le
      (PointedCone.subset_hull (normalized_mem hs hx hx0))
    simpa [smul_smul,hux.ne'] using hh

/-- Positivity and idempotence, with positivity on the whole specified cone. -/
def PositiveProjection {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : PointedCone ℝ E) (T : E →ₗ[ℝ] E) : Prop :=
  (∀ x ∈ C, T x ∈ C) ∧ T.comp T = T

/-- All eight exact positive range/kernel equalities and original mass laws. -/
structure PointLaws (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (p : pure C u) (ap : V →ₗ[ℝ] ℝ)
    (Pi : V →ₗ[ℝ] V) (Sigma : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V) : Prop where
  genuine_dual : Pi.dualMap = Sigma
  pi_projection : PositiveProjection C Pi
  r_projection : PositiveProjection C (ap.smulRight (p : V))
  sigma_projection : PositiveProjection (positiveDual C) Sigma
  rstar_projection : PositiveProjection (positiveDual C) (ap.smulRight (p : V)).dualMap
  sigma_unit : Sigma u = u-ap
  sigma_effect : Sigma ap = 0
  pi_point : Pi p = 0
  pi_exclusion : ∀ x ∈ exclusion C u p, Pi x = x
  pi_image : positiveImage C Pi = (PointedCone.hull ℝ (exclusion C u p) : Set V)
  pi_kernel : positiveKernel C Pi = (PointedCone.hull ℝ {(p : V)} : Set V)
  r_image : positiveImage C (ap.smulRight (p : V)) = (PointedCone.hull ℝ {(p : V)} : Set V)
  r_kernel : positiveKernel C (ap.smulRight (p : V)) =
    (PointedCone.hull ℝ (exclusion C u p) : Set V)
  sigma_image : positiveImage (positiveDual C) Sigma = zeroPositive C u p
  rstar_kernel : positiveKernel (positiveDual C) (ap.smulRight (p : V)).dualMap = zeroPositive C u p
  sigma_kernel : positiveKernel (positiveDual C) Sigma =
    (PointedCone.hull ℝ {ap} : Set (Module.Dual ℝ V))
  rstar_image : positiveImage (positiveDual C) (ap.smulRight (p : V)).dualMap =
    (PointedCone.hull ℝ {ap} : Set (Module.Dual ℝ V))
  rstar_formula : ∀ f, (ap.smulRight (p : V)).dualMap f = f p • ap
  mass : ∀ v, u (Pi v) = (u-ap) v ∧ u (ap.smulRight (p : V) v) = ap v
  mass_bounds : ∀ v ∈ C, (0 ≤ u (Pi v) ∧ u (Pi v) ≤ u v) ∧
    (0 ≤ u (ap.smulRight (p : V) v) ∧ u (ap.smulRight (p : V) v) ≤ u v)

private theorem point_laws [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p))
    (hcharts : ∀ (p : pure C u) (b : ExclusionChart C u p), ∃ Λ, ExtensionLaws b (a p) Λ)
    (p : pure C u) (b : ExclusionChart C u p)
    (Λ : (EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ))
    (hΛ : ExtensionLaws b (a p) Λ) :
    PointLaws C u p (a p) (primal (Λ.comp (restriction b))) (Λ.comp (restriction b)) := by
  let S := Λ.comp (restriction b)
  let T := primal S
  let R := (a p).smulRight (p : V)
  have hspan : affineSpan ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) 1) = ⊤ :=
    affineSpan_eq_top_of_nonempty_interior ⟨0, by
      rw [(convex_closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) (1 : ℝ)).convexHull_eq]
      exact Metric.ball_subset_interior_closedBall (by simp)⟩
  have hresu : restriction b u = AffineMap.const ℝ _ (1 : ℝ) := by
    apply AffineMap.ext_on hspan
    intro z hz
    exact (chart_mem b (by simpa using hz)).1.2
  have hresa : restriction b (a p) = 0 := by
    apply AffineMap.ext_on hspan
    intro z hz
    exact (ha p).2 _ (chart_mem b (by simpa using hz))
  have hSu : S u = u-a p := by dsimp [S]; rw [hresu,hΛ.unit_eq]
  have hSa : S (a p) = 0 := by dsimp [S]; rw [hresa,map_zero]
  have hSS : S.comp S = S := by
    ext f v
    change Λ (restriction b (Λ (restriction b f))) v = _
    rw [hΛ.restrict_eq]
    rfl
  have hTT : T.comp T = T := by
    ext v
    apply dual_separates
    intro f
    change f (primal S (primal S v)) = f (primal S v)
    rw [primal_eval,primal_eval,primal_eval]
    exact congrArg (fun L : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V => L f v) hSS
  have hSpos : ∀ f ∈ positiveDual C, S f ∈ positiveDual C := by
    intro f hf x hx
    exact hΛ.positive _ (fun z hz => hf (chart_mem b hz).1.1) x hx
  have hTpos : ∀ v ∈ C, T v ∈ C := by
    intro v hv
    by_contra hn
    let D : ProperCone ℝ V := {toSubmodule := C,isClosed' := hc}
    obtain ⟨f,hf,hneg⟩ := D.hyperplane_separation_point hn
    have hh := hSpos f.toLinearMap (fun x hx => hf x hx) hv
    change 0 ≤ S f.toLinearMap v at hh
    rw [← primal_eval S f.toLinearMap v] at hh
    exact (not_le_of_gt hneg) hh
  have hRf (f : Module.Dual ℝ V) : R.dualMap f = f p • a p := by
    ext v
    simp [R,LinearMap.smulRight_apply,mul_comm]
  have hRR : R.comp R = R := by ext v; simp [R,(ha p).1.2]
  have hRpos : ∀ v ∈ C, R v ∈ C := fun v hv =>
    C.smul_mem ((ha p).1.1 v hv).1 (pure_mem p).1
  have hRstarpos : ∀ f ∈ positiveDual C, R.dualMap f ∈ positiveDual C := by
    intro f hf x hx
    change 0 ≤ f (R x)
    exact hf (hRpos x hx)
  have hRstarstar : R.dualMap.comp R.dualMap = R.dualMap := by
    ext f v
    change f (R (R v)) = f (R v)
    exact congrArg f (LinearMap.congr_fun hRR v)
  have hTp : T p = 0 := by
    apply dual_separates
    intro f
    rw [map_zero,primal_eval]
    exact hΛ.at_point _
  have hTD : ∀ x ∈ exclusion C u p, T x = x := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := b.whole.symm ▸ hx
    apply dual_separates
    intro f
    rw [primal_eval]
    exact congrArg (fun h => h z) (hΛ.restrict_eq (restriction b f))
  have hmass (v : V) : u (T v) = (u-a p) v ∧ u (R v) = a p v := by
    constructor
    · rw [primal_eval,hSu]
    · simp [R,(pure_mem p).2]
  have hzero := cone_zero hs p (a p) (ha p)
  have hmax := unique_maximum hc hs hg hB hW p (a p) (ha p)
  have hTfix : ∀ x ∈ PointedCone.hull ℝ (exclusion C u p), T x = x := by
    have hle : PointedCone.hull ℝ (exclusion C u p) ≤
        PointedCone.ofSubmodule (LinearMap.ker (T-(LinearMap.id : V →ₗ[ℝ] V))) :=
      Submodule.span_le.mpr (fun x hx => by simp [hTD x hx])
    intro x hx
    have hh : (T-(LinearMap.id : V →ₗ[ℝ] V)) x = 0 := hle hx
    simpa using sub_eq_zero.mp hh
  have hTidem : IsIdempotentElem T := hTT
  have hSidem : IsIdempotentElem S := hSS
  have hRidem : IsIdempotentElem R := hRR
  have hRSidem : IsIdempotentElem R.dualMap := hRstarstar
  have hTim : positiveImage C T = (PointedCone.hull ℝ (exclusion C u p) : Set V) := by
    ext x
    constructor
    · rintro ⟨hx,hxC⟩
      rw [hzero]
      refine ⟨hxC,?_⟩
      have hfix := (LinearMap.IsIdempotentElem.mem_range_iff hTidem).mp hx
      have hh := primal_eval S (a p) x
      change a p (T x) = S (a p) x at hh
      rw [hfix,hSa] at hh
      exact hh
    · intro hx
      refine ⟨(LinearMap.IsIdempotentElem.mem_range_iff hTidem).mpr (hTfix x hx),?_⟩
      exact ((show x ∈ C ⊓ PointedCone.ofSubmodule (LinearMap.ker (a p)) from hzero ▸ hx)).1
  have hTker : positiveKernel C T = (PointedCone.hull ℝ {(p : V)} : Set V) := by
    ext x
    constructor
    · rintro ⟨hx,hxC⟩
      by_cases hx0 : x = 0
      · simpa [hx0] using (PointedCone.hull ℝ {(p : V)}).zero_mem
      have hux := hs x hxC hx0
      have hn := normalized_mem hs hxC hx0
      have hax : a p x = u x := by
        have hh := (hmass x).1
        rw [show T x = 0 from hx,map_zero] at hh
        simpa only [LinearMap.sub_apply] using (sub_eq_zero.mp hh.symm).symm
      have hnM : (u x)⁻¹ • x ∈ {x | x ∈ base C u ∧ a p x = 1} :=
        ⟨hn,by simp [map_smul,hax,hux.ne']⟩
      have hnP : (u x)⁻¹ • x = p := by simpa [hmax] using hnM
      apply PointedCone.mem_hull_singleton.mpr
      exact ⟨u x,hux.le,by rw [← hnP]; simp [smul_smul,hux.ne']⟩
    · intro hx
      obtain ⟨t,ht,rfl⟩ := PointedCone.mem_hull_singleton.mp hx
      exact ⟨by simp [hTp],C.smul_mem ht (pure_mem p).1⟩
  have hRim : positiveImage C R = (PointedCone.hull ℝ {(p : V)} : Set V) := by
    ext x
    constructor
    · rintro ⟨hx,hxC⟩
      exact PointedCone.mem_hull_singleton.mpr
        ⟨a p x,((ha p).1.1 x hxC).1,(LinearMap.IsIdempotentElem.mem_range_iff hRidem).mp hx⟩
    · intro hx
      obtain ⟨t,ht,rfl⟩ := PointedCone.mem_hull_singleton.mp hx
      exact ⟨(LinearMap.IsIdempotentElem.mem_range_iff hRidem).mpr (by simp [R,(ha p).1.2]),
        C.smul_mem ht (pure_mem p).1⟩
  have hp0 : (p : V) ≠ 0 := by intro he; simpa [he] using (pure_mem p).2
  have hRker : positiveKernel C R = (PointedCone.hull ℝ (exclusion C u p) : Set V) := by
    ext x
    rw [hzero]
    constructor
    · rintro ⟨hx,hxC⟩
      exact ⟨hxC,(smul_eq_zero.mp (show a p x • (p : V) = 0 from hx)).resolve_right hp0⟩
    · rintro ⟨hxC,hxa⟩
      exact ⟨by change a p x • (p : V) = 0; rw [show a p x = 0 from hxa,zero_smul],hxC⟩
  have hSim : positiveImage (positiveDual C) S = zeroPositive C u p := by
    ext f
    constructor
    · rintro ⟨hf,hfpos⟩
      exact ⟨fun x hx => hfpos hx,by
        rw [← (LinearMap.IsIdempotentElem.mem_range_iff hSidem).mp hf]; exact hΛ.at_point _⟩
    · intro hf
      exact ⟨(LinearMap.IsIdempotentElem.mem_range_iff hSidem).mpr (hΛ.inverse_positive f hf),fun x hx => hf.1 x hx⟩
  have hSker : positiveKernel (positiveDual C) S =
      (PointedCone.hull ℝ {a p} : Set (Module.Dual ℝ V)) := by
    ext f
    constructor
    · rintro ⟨hf,hfpos⟩
      have hres : restriction b f = 0 := by
        have hh := hΛ.restrict_eq (restriction b f)
        change restriction b (S f) = _ at hh
        rw [show S f = 0 from hf,map_zero] at hh
        exact hh.symm
      have hz : ∀ x ∈ exclusion C u p, f x = 0 := by
        intro x hx
        obtain ⟨z,hz,rfl⟩ := b.whole.symm ▸ hx
        exact congrArg (fun h => h z) hres
      have he := annihilator_ray hc hs hg hB hW a ha hcharts p f (fun x hx => hfpos hx) hz
      exact PointedCone.mem_hull_singleton.mpr ⟨f p,hfpos (pure_mem p).1,he.symm⟩
    · intro hf
      obtain ⟨t,ht,rfl⟩ := PointedCone.mem_hull_singleton.mp hf
      exact ⟨by simp [hSa],fun x hx => mul_nonneg ht ((ha p).1.1 x hx).1⟩
  have hRSker : positiveKernel (positiveDual C) R.dualMap = zeroPositive C u p := by
    ext f
    constructor
    · rintro ⟨hf,hfpos⟩
      refine ⟨fun x hx => hfpos hx,?_⟩
      have hh := LinearMap.congr_fun (show R.dualMap f = 0 from hf) p
      simpa [hRf,(ha p).1.2] using hh
    · intro hf
      exact ⟨by change R.dualMap f = 0; rw [hRf,hf.2,zero_smul],fun x hx => hf.1 x hx⟩
  have hRSim : positiveImage (positiveDual C) R.dualMap =
      (PointedCone.hull ℝ {a p} : Set (Module.Dual ℝ V)) := by
    ext f
    constructor
    · rintro ⟨hf,hfpos⟩
      exact PointedCone.mem_hull_singleton.mpr ⟨f p,hfpos (pure_mem p).1,
        (hRf f).symm.trans ((LinearMap.IsIdempotentElem.mem_range_iff hRSidem).mp hf)⟩
    · intro hf
      obtain ⟨t,ht,rfl⟩ := PointedCone.mem_hull_singleton.mp hf
      refine ⟨(LinearMap.IsIdempotentElem.mem_range_iff hRSidem).mpr ?_,fun x hx => mul_nonneg ht ((ha p).1.1 x hx).1⟩
      rw [hRf]
      simp [(ha p).1.2]
  exact {
    genuine_dual := by ext f v; exact primal_eval S f v
    pi_projection := ⟨hTpos,hTT⟩
    r_projection := ⟨hRpos,hRR⟩
    sigma_projection := ⟨hSpos,hSS⟩
    rstar_projection := ⟨hRstarpos,hRstarstar⟩
    sigma_unit := hSu
    sigma_effect := hSa
    pi_point := hTp
    pi_exclusion := hTD
    pi_image := hTim
    pi_kernel := hTker
    r_image := hRim
    r_kernel := hRker
    sigma_image := hSim
    rstar_kernel := hRSker
    sigma_kernel := hSker
    rstar_image := hRSim
    rstar_formula := hRf
    mass := hmass
    mass_bounds := by
      intro x hx
      rw [(hmass x).1,(hmass x).2]
      have hh := (ha p).1.1 x hx
      simp only [LinearMap.sub_apply]
      exact ⟨⟨sub_nonneg.mpr hh.2,by linarith⟩,hh⟩ }


/-- Mathematical complementary filters, including the actual dual conditions.
There is no assertion that the two linear maps sum to the identity. -/
structure ComplementaryPair (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (T R : V →ₗ[ℝ] V) : Prop where
  first : PositiveProjection C T
  second : PositiveProjection C R
  dual_first : PositiveProjection (positiveDual C) T.dualMap
  dual_second : PositiveProjection (positiveDual C) R.dualMap
  image_kernel : positiveImage C T = positiveKernel C R
  kernel_image : positiveKernel C T = positiveImage C R
  dual_image_kernel : positiveImage (positiveDual C) T.dualMap = positiveKernel (positiveDual C) R.dualMap
  dual_kernel_image : positiveKernel (positiveDual C) T.dualMap = positiveImage (positiveDual C) R.dualMap
  normalization : ∀ x ∈ C, u (T x) ≤ u x ∧ u (R x) ≤ u x

private theorem pair_swap {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    {T R : V →ₗ[ℝ] V} (h : ComplementaryPair C u T R) : ComplementaryPair C u R T :=
  ⟨h.second,h.first,h.dual_second,h.dual_first,h.kernel_image.symm,h.image_kernel.symm,
    h.dual_kernel_image.symm,h.dual_image_kernel.symm,fun x hx => (h.normalization x hx).symm⟩

private theorem pair_of_point {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    {p : pure C u} {ap : V →ₗ[ℝ] ℝ} {T : V →ₗ[ℝ] V}
    {S : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V}
    (h : PointLaws C u p ap T S) : ComplementaryPair C u T (ap.smulRight (p : V)) := by
  refine ⟨h.pi_projection,h.r_projection,?_,h.rstar_projection,?_,?_,?_,?_,?_⟩
  · rw [h.genuine_dual]; exact h.sigma_projection
  · rw [h.pi_image,h.r_kernel]
  · rw [h.pi_kernel,h.r_image]
  · rw [h.genuine_dual,h.sigma_image,h.rstar_kernel]
  · rw [h.genuine_dual,h.sigma_kernel,h.rstar_image]
  · intro x hx
    exact ⟨(h.mass_bounds x hx).1.2,(h.mass_bounds x hx).2.2⟩

private theorem zero_id_pair (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hu : ∀ x ∈ C, 0 ≤ u x) :
    ComplementaryPair C u 0 LinearMap.id := by
  have hz : (0 : V →ₗ[ℝ] V).dualMap = 0 := by ext f v; simp
  have hi : (LinearMap.id : V →ₗ[ℝ] V).dualMap = LinearMap.id := by ext f v; rfl
  refine ⟨⟨fun _ _ => C.zero_mem,by simp⟩,⟨fun x hx => hx,by simp⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hz]
    exact ⟨fun _ _ => (positiveDual C).zero_mem,by simp⟩
  · rw [hi]
    exact ⟨fun x hx => hx,by simp⟩
  · ext x; simp [positiveImage,positiveKernel]
  · ext x; simp [positiveImage,positiveKernel]
  · rw [hz,hi]; ext f; simp [positiveImage,positiveKernel]
  · rw [hz,hi]; ext f; simp [positiveImage,positiveKernel]
  · intro x hx
    simp only [LinearMap.zero_apply,map_zero,LinearMap.id_apply]
    exact ⟨hu x hx,le_rfl⟩

private theorem native_faces [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (a : pure C u → (V →ₗ[ℝ] ℝ))
    (hp : ∀ p : pure C u, ∃ T S, PointLaws C u p (a p) T S) :
    ∀ F : PointedCone.Face C, ∃ T R, ComplementaryPair C u T R ∧ positiveImage C T = (F : Set V) := by
  intro F
  have hu : ∀ x ∈ C, 0 ≤ u x := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · exact (hs x hx hx0).le
  by_cases hF0 : F.toPointedCone = ⊥
  · refine ⟨0,LinearMap.id,zero_id_pair C u hu,?_⟩
    change positiveImage C 0 = (F.toPointedCone : Set V)
    rw [hF0]
    ext x
    simp [positiveImage]
  by_cases hFC : F.toPointedCone = C
  · refine ⟨LinearMap.id,0,pair_swap (zero_id_pair C u hu),?_⟩
    change positiveImage C LinearMap.id = (F.toPointedCone : Set V)
    rw [hFC]
    ext x
    simp [positiveImage]
  have hFn : ∃ x ∈ F, x ≠ (0 : V) := by
    by_contra! hn
    apply hF0
    ext x
    constructor
    · intro hx; simpa using hn x hx
    · intro hx; simpa only [Submodule.mem_bot] using hx ▸ F.toPointedCone.zero_mem
  obtain ⟨x,hx,hx0⟩ := hFn
  have hsf : ∀ x ∈ F.toPointedCone, x ≠ 0 → 0 < u x :=
    fun x hx hx0 => hs x (F.isFaceOf.le hx) hx0
  have hnon : (base F.toPointedCone u).Nonempty := ⟨_,normalized_mem hsf hx hx0⟩
  have hface : IsExtreme ℝ (base C u) (base F.toPointedCone u) := by
    refine ⟨fun x hx => ⟨F.isFaceOf.le hx.1,hx.2⟩,?_⟩
    intro x hx y hy z hz hseg
    exact ⟨F.isFaceOf.isExtreme.left_mem_of_mem_openSegment hx.1 hy.1 hz.1 hseg,hx.2⟩
  have hproper : base F.toPointedCone u ≠ base C u := by
    intro he
    exact hFC ((hull_base F.toPointedCone u hsf).symm.trans
      ((congrArg (PointedCone.hull ℝ) he).trans (hull_base C u hs)))
  rcases (exclusion_ball_faces hc hs hg hB).2.1 _ hnon (base_convex F.toPointedCone u)
    hface hproper with ⟨p,he⟩ | ⟨p,he⟩
  · obtain ⟨T,S,hp⟩ := hp p
    refine ⟨(a p).smulRight (p : V),T,pair_swap (pair_of_point hp),?_⟩
    rw [hp.r_image]
    change (PointedCone.hull ℝ {(p : V)} : Set V) = (F.toPointedCone : Set V)
    rw [← he,hull_base F.toPointedCone u hsf]
  · obtain ⟨T,S,hp⟩ := hp p
    refine ⟨T,(a p).smulRight (p : V),pair_of_point hp,?_⟩
    rw [hp.pi_image]
    change (PointedCone.hull ℝ (exclusion C u p) : Set V) = (F.toPointedCone : Set V)
    rw [← he,hull_base F.toPointedCone u hsf]

/-- Full original VII105.5. The common effect and the single positive extension
are derived from W. Every chart gives the genuine primal/dual maps, and every
native cone face is the positive range of a complementary mathematical pair. -/
theorem whole_positive_projections [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) :
    ∃ a : pure C u → (V →ₗ[ℝ] ℝ),
      (∀ p : pure C u, common C u p (a p)) ∧
      (∀ (p : pure C u) f, common C u p f → f = a p) ∧
      (∀ (p : pure C u) (b : ExclusionChart C u p),
        ∃ Λ : (EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ),
          ExtensionLaws b (a p) Λ ∧
          (restriction b).comp Λ = LinearMap.id ∧
          PointLaws C u p (a p) (primal (Λ.comp (restriction b))) (Λ.comp (restriction b)) ∧
          ∀ (c : ExclusionChart C u p)
            (Γ : (EuclideanSpace ℝ (Fin c.dim) →ᵃ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ)),
            PositiveLift c Γ → Λ.comp (restriction b) = Γ.comp (restriction c)) ∧
      ∀ F : PointedCone.Face C, ∃ T R,
        ComplementaryPair C u T R ∧ positiveImage C T = (F : Set V) := by
  obtain ⟨a,ha,hu,_,hcharts⟩ := whole_positive_extension hc hs hg hB hW
  have hch (p : pure C u) (b : ExclusionChart C u p) : ∃ Λ, ExtensionLaws b (a p) Λ := by
    obtain ⟨Λ,hΛ,_⟩ := (hcharts p b).2
    exact ⟨Λ,hΛ⟩
  have hp (p : pure C u) (b : ExclusionChart C u p) :=
    point_laws hc hs hg hB hW a ha hch p b
  refine ⟨a,ha,hu,?_,?_⟩
  · intro p b
    obtain ⟨Λ,hΛ⟩ := hch p b
    refine ⟨Λ,hΛ,LinearMap.ext (hΛ.restrict_eq),hp p b Λ hΛ,?_⟩
    intro c Γ hΓ
    apply LinearMap.ext
    intro f
    exact hΛ.intrinsic c Γ hΓ (restriction b f) (restriction c f)
      (fun z w _ _ he => congrArg f he)
  · apply native_faces hc hs hg hB a
    intro p
    obtain ⟨b⟩ := hB p
    obtain ⟨Λ,hΛ⟩ := hch p b
    exact ⟨primal (Λ.comp (restriction b)),Λ.comp (restriction b),hp p b Λ hΛ⟩

#print axioms whole_positive_projections

end D5.S3.Quantum.Foundation.PositiveComplementaryProjections
