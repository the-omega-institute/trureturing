/- GID: D5/S3/Quantum/Foundation/CommonPositiveExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/CommonPositiveExtension
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Intrinsic positive restriction and one common signed affine extension. -/

import D5.S3.Quantum.Foundation.OrthogonalJointCompletion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.QuadraticDiscriminant

/-! Original positive restriction on entire exclusion balls. -/

noncomputable section
open Set
open scoped RealInnerProductSpace Pointwise

namespace D5.S3.Quantum.Foundation.CommonPositiveExtension

open CircuitBalancedConfirmation FacetZeroGluing WholePairBallConfirmation
open ExclusionBallFaces OrthogonalJointCompletion WholeExclusionSupport

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem common_exists {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) : ∃ a, common C u p a := by
  obtain ⟨a, ha, hz⟩ := ((exclusion_ball_faces hc hs hg hB).1 p).2.2.2.2.2.2
  exact ⟨a, ha, fun x hx => (hz ▸ hx).2⟩

private theorem common_unique [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (p : pure C u) {a a' : V →ₗ[ℝ] ℝ}
    (ha : common C u p a) (ha' : common C u p a') : a = a' := by
  have comp := (whole_joint_completion hc hs hg hB hW).1
  obtain ⟨q, r, hqr⟩ := (whole_joint_completion hc hs hg hB hW).2.1 p
  obtain ⟨s, hrs, _⟩ := comp p r hqr.2.2.2.1
  have hqp : (q : V) ∈ exclusion C u p := ⟨pure_mem q, hqr.2.2.1⟩
  have hqr' : (q : V) ∈ exclusion C u r :=
    (exclusion_symmetric q r).mp ⟨pure_mem r, hqr.2.2.2.2.1⟩
  have hqs : q = s := Subtype.ext (by
    have hh : (q : V) ∈ exclusion C u p ∩ exclusion C u r := ⟨hqp, hqr'⟩
    simpa [hrs.1] using hh)
  subst s
  obtain ⟨b, hb⟩ := common_exists hc hs hg hB q
  have hle (a a' : V →ₗ[ℝ] ℝ) (ha : common C u p a)
      (ha' : common C u p a') (x : V) (hx : x ∈ C) : a x ≤ a' x := by
    let S : Set ℝ := {t | ∃ b, common C u q b ∧ b x = t}
    have hne : S.Nonempty := ⟨b x, b, hb, rfl⟩
    have hbd : BddAbove S := ⟨u x, by rintro t ⟨d, hd, rfl⟩; exact (hd.1.1 x hx).2⟩
    have hh : sSup S ≤ sSup S - a x + a' x := by
      apply csSup_le hne
      rintro t ⟨d, hd, rfl⟩
      have hc' := (hqr.2.2.2.2.2 a d ha hd).1
      have hd' := (hrs.2.2.2.2.2 a' (u - a - d) ha' hc').1
      have hval := le_csSup hbd (show (u - a' - (u - a - d)) x ∈ S from
        ⟨_, hd', rfl⟩)
      simp only [LinearMap.sub_apply] at hval
      linarith
    linarith
  have heq : ∀ x ∈ C, (a - a') x = 0 := by
    intro x hx
    simp only [LinearMap.sub_apply]
    exact sub_eq_zero.mpr (le_antisymm (hle a a' ha ha' x hx) (hle a' a ha' ha x hx))
  have hker : Submodule.span ℝ (C : Set V) ≤ LinearMap.ker (a - a') :=
    Submodule.span_le.mpr heq
  rw [hg] at hker
  exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp (top_le_iff.mp hker))

private theorem affine_ball_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E →ᵃ[ℝ] ℝ} (h : ∀ z, ‖z‖ ≤ 1 → f z = g z) : f = g := by
  apply AffineMap.ext_on (s := Metric.closedBall (0 : E) 1)
    (affineSpan_eq_top_of_nonempty_interior ?_)
  · intro z hz
    exact h z (by simpa using hz)
  · exact ⟨0, by
      rw [(convex_closedBall (0 : E) (1 : ℝ)).convexHull_eq]
      exact Metric.ball_subset_interior_closedBall (by simp)⟩

omit [FiniteDimensional ℝ V] in
private theorem chart_mem {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p : V}
    (b : ExclusionChart C u p) {z} (hz : ‖z‖ ≤ 1) : b.param z ∈ exclusion C u p := by
  rw [← b.whole]
  exact ⟨z, by simpa using hz, rfl⟩

private theorem diameter [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p)) (p : pure C u) (b : ExclusionChart C u p)
    (n : EuclideanSpace ℝ (Fin b.dim)) (hn : ‖n‖ = 1) :
    ∃ q r : pure C u, b.param n = q ∧ b.param (-n) = r ∧
      a p + a q + a r = u ∧
      (∀ z, a q (b.param z) = (1 + ⟪n,z⟫) / 2) ∧
      (∀ z, a r (b.param z) = (1 - ⟪n,z⟫) / 2) ∧
      a q p = 0 ∧ a r p = 0 := by
  have : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  have hnex : n ∈ (Metric.closedBall 0 1).extremePoints ℝ := by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    simpa using hn
  have hqex := affine_extreme_image (Metric.closedBall 0 1) (convex_closedBall 0 1)
    b.param (fun _ _ _ _ h => b.injective h) hnex
  rw [b.whole] at hqex
  have hqpure := ((exclusion_ball_faces hc hs hg hB).1 p).2.2.2.2.1
    |>.extremePoints_subset_extremePoints hqex
  let q : pure C u := ⟨b.param n, hqpure⟩
  obtain ⟨r, hr, _⟩ := (whole_joint_completion hc hs hg hB hW).1 p q
    (chart_mem b hn.le).2
  have hcompletion := hr.2.2.2.2.2 (a p) (a q) (ha p) (ha q)
  have hac : u - a p - a q = a r := common_unique hc hs hg hB hW r hcompletion.1 (ha r)
  have hsum : a p + a q + a r = u := by rw [← hac]; abel
  have hrD : (r : V) ∈ exclusion C u p := ⟨pure_mem r, hr.2.2.2.1⟩
  obtain ⟨m, hm, hmr⟩ := b.whole.symm ▸ hrD
  have hmnorm : ‖m‖ ≤ 1 := by simpa using hm
  let f := (AffineMap.const ℝ (EuclideanSpace ℝ (Fin b.dim)) (1 : ℝ)) -
    (a q).toAffineMap.comp b.param
  have hfpos (z) (hz : ‖z‖ ≤ 1) : 0 ≤ f z := by
    have hx := chart_mem b hz
    have hh := ((ha q).1.1 _ hx.1.1).2
    rw [hx.1.2] at hh
    exact sub_nonneg.mpr hh
  have hf := affine_zero_antipode f (by simpa using hn : ‖-n‖ = 1) hfpos
    (by simp [f, q, (ha q).1.2])
  have hfm : f m = 1 := by
    change 1 - a q (b.param m) = 1
    rw [hmr, hcompletion.2.2.2.2.2.2.1]
    norm_num
  have hfc : f (-n) ≤ 1 := by
    change 1 - a q (b.param (-n)) ≤ 1
    linarith [((ha q).1.1 _ (chart_mem b (z := -n) (by simp [hn])).1.1).1]
  have hfc0 := hfpos (-n) (by simp [hn])
  have him : ⟪-n,m⟫ ≤ 1 := (real_inner_le_norm (-n) m).trans (by simpa [hn] using hmnorm)
  have he := hf m
  rw [hfm] at he
  have hfc1 : f (-n) = 1 := by nlinarith
  have him1 : ⟪-n,m⟫ = 1 := by rw [hfc1] at he; linarith
  have hmone : ‖m‖ = 1 := by
    have hh := real_inner_le_norm (-n) m
    rw [him1] at hh
    exact le_antisymm hmnorm (by simpa [hn] using hh)
  have hnm : -n = m := (inner_eq_one_iff_of_norm_eq_one (by simpa using hn) hmone).mp him1
  have hrparam : b.param (-n) = r := by rw [hnm, hmr]
  have haqformula (z) : a q (b.param z) = (1 + ⟪n,z⟫) / 2 := by
    have hh := hf z
    change 1 - a q (b.param z) = f (-n) / 2 * (1 + ⟪-n,z⟫) at hh
    rw [hfc1, inner_neg_left] at hh
    linarith
  have harq : a r (b.param n) = 0 := by
    have hqD : (q : V) ∈ exclusion C u r := (exclusion_symmetric q r).mp
      ⟨pure_mem r, hr.2.2.2.2.1⟩
    exact (ha r).2 q hqD
  have harformula' := affine_zero_antipode ((a r).toAffineMap.comp b.param)
    (by simpa using hn : ‖-n‖ = 1)
    (fun z hz => ((ha r).1.1 _ (chart_mem b hz).1.1).1) (by simpa using harq)
  refine ⟨q, r, rfl, hrparam, hsum, haqformula, ?_, ?_, ?_⟩
  · intro z
    have hh := harformula' z
    change a r (b.param z) = a r (b.param (-n)) / 2 * (1 + ⟪-n,z⟫) at hh
    simpa [hrparam, (ha r).1.2, inner_neg_left, sub_eq_add_neg, div_eq_mul_inv, mul_comm] using hh
  · exact hcompletion.2.2.2.2.1
  · have hpD : (p : V) ∈ exclusion C u r := (exclusion_symmetric p r).mp hrD
    exact (ha r).2 p hpD

private theorem affine_diameter {d : ℕ} (hd : 0 < d)
    (h : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) :
    ∃ n : EuclideanSpace ℝ (Fin d), ‖n‖ = 1 ∧
      ∀ z, h z = h n * ((1 + ⟪n,z⟫) / 2) + h (-n) * ((1 - ⟪n,z⟫) / 2) := by
  let L := h.linear.toContinuousLinearMap
  let v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm L
  have hv (z) : h z = h 0 + ⟪v,z⟫ := by
    rw [InnerProductSpace.toDual_symm_apply]
    simpa [L, add_comm] using congrFun h.decomp z
  by_cases hv0 : v = 0
  · let n : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0,hd⟩ 1
    have hn : ‖n‖ = 1 := by simp [n, EuclideanSpace.single]
    refine ⟨n, hn, fun z => ?_⟩
    rw [hv z, hv n, hv (-n)]
    simp only [hv0, inner_zero_left, add_zero]
    ring
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    let n := ‖v‖⁻¹ • v
    have hn : ‖n‖ = 1 := by simp [n, norm_smul, hvpos.ne']
    have hvn : v = ‖v‖ • n := by simp [n, smul_smul, hvpos.ne']
    refine ⟨n, hn, fun z => ?_⟩
    have hi (x) : ⟪v,x⟫ = ‖v‖ * ⟪n,x⟫ := by
      nth_rw 1 [hvn]
      exact real_inner_smul_left _ _ _
    rw [hv z, hv n, hv (-n), hi z, hi n, hi (-n)]
    simp only [inner_neg_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
    ring

private theorem reconstruction [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p)) (p : pure C u)
    (b : ExclusionChart C u p) (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ C, 0 ≤ f x) (hfp : f p = 0)
    (n : EuclideanSpace ℝ (Fin b.dim))
    (q r : pure C u)
    (hsum : a p + a q + a r = u)
    (haq : ∀ z, a q (b.param z) = (1 + ⟪n,z⟫) / 2)
    (har : ∀ z, a r (b.param z) = (1 - ⟪n,z⟫) / 2)
    (hqp : a q p = 0) (hrp : a r p = 0)
    (hformula : ∀ z, f (b.param z) = f q * ((1 + ⟪n,z⟫) / 2) +
      f r * ((1 - ⟪n,z⟫) / 2)) : f = f q • a q + f r • a r := by
  obtain ⟨y, hy, hmax⟩ := (base_compact hc hs).exists_isMaxOn ⟨p, pure_mem p⟩
    f.continuous_of_finiteDimensional.continuousOn
  let M := 1 + f y
  have hM : 0 < M := by dsimp [M]; linarith [hf y hy.1]
  have hbound : ∀ x ∈ C, f x ≤ M * u x := by
    have hh := nonneg_on_cone (f := M • u - f) (base_compact hc hs) hs (fun s => by
      have hm : f s ≤ f y := hmax (pure_mem s)
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, (pure_mem s).2, mul_one]
      dsimp [M]
      linarith)
    intro x hx
    have he := hh x hx
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_nonneg] using he
  have hq0 := hf q (pure_mem q).1
  have hr0 := hf r (pure_mem r).1
  have hqM : f q ≤ M := by simpa [(pure_mem q).2] using hbound q (pure_mem q).1
  have hrM : f r ≤ M := by simpa [(pure_mem r).2] using hbound r (pure_mem r).1
  have hα : 0 ≤ 1 - M⁻¹ * f q := by
    rw [← div_eq_inv_mul]
    exact sub_nonneg.mpr ((div_le_one hM).mpr hqM)
  have hβ : 0 ≤ 1 - M⁻¹ * f r := by
    rw [← div_eq_inv_mul]
    exact sub_nonneg.mpr ((div_le_one hM).mpr hrM)
  let k := u - M⁻¹ • f - (1 - M⁻¹ * f q) • a q - (1 - M⁻¹ * f r) • a r
  have hkp : k p = 1 := by simp [k, hfp, hqp, hrp, (pure_mem p).2]
  have hkupper : ∀ x ∈ C, k x ≤ u x := by
    intro x hx
    change u x - M⁻¹ * f x - (1 - M⁻¹ * f q) * a q x - (1 - M⁻¹ * f r) * a r x ≤ u x
    linarith [mul_nonneg (inv_nonneg.mpr hM.le) (hf x hx),
      mul_nonneg hα ((ha q).1.1 x hx).1, mul_nonneg hβ ((ha r).1.1 x hx).1]
  have hkzero : ∀ x ∈ exclusion C u p, k x = 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := b.whole.symm ▸ hx
    change u (b.param z) - M⁻¹ * f (b.param z) -
      (1 - M⁻¹ * f q) * a q (b.param z) - (1 - M⁻¹ * f r) * a r (b.param z) = 0
    rw [(chart_mem b (by simpa using hz)).1.2, hformula, haq, har]
    ring
  have hkeq : k = a p := common_unique hc hs hg hB hW p
    ⟨whole_exclusion_support hc hs p k hkp hkupper hkzero, hkzero⟩ (ha p)
  ext x
  have hkx := LinearMap.congr_fun hkeq x
  have hsx := LinearMap.congr_fun hsum x
  change u x - M⁻¹ * f x - (1 - M⁻¹ * f q) * a q x -
    (1 - M⁻¹ * f r) * a r x = a p x at hkx
  change a p x + a q x + a r x = u x at hsx
  change f x = f q * a q x + f r * a r x
  have hMinv : M * M⁻¹ = 1 := mul_inv_cancel₀ hM.ne'
  have hh := congrArg (fun t : ℝ => M * t) hkx
  nlinarith

/-- The normal form and whole-cone least clause of VII105.3, without any
assertion of positive or signed dual spectral generation. -/
def ConfirmationNormalForm {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (a : pure C u → (V →ₗ[ℝ] ℝ)) (p : pure C u) (g : V →ₗ[ℝ] ℝ) : Prop :=
  (∃ q r : pure C u, (q : V) ∈ exclusion C u p ∧ (r : V) ∈ exclusion C u p ∧
    a p + a q + a r = u ∧ g = a p + g q • a q + g r • a r ∧
    (0 ≤ g q ∧ g q ≤ 1) ∧ (0 ≤ g r ∧ g r ≤ 1)) ∧
  ∀ x ∈ C, a p x ≤ g x

private theorem confirmation_normal_form [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p)) (p : pure C u)
    (g : V →ₗ[ℝ] ℝ) (hgconf : confirms C u p g) : ConfirmationNormalForm a p g := by
  obtain ⟨b⟩ := hB p
  obtain ⟨n,hn,hform⟩ := affine_diameter b.dim_pos ((u-g).toAffineMap.comp b.param)
  obtain ⟨q,r,hq,hr,hsum,haq,har,hqp,hrp⟩ := diameter hc hs hg hB hW a ha p b n hn
  have hf : ∀ x ∈ C, 0 ≤ (u-g) x := fun x hx => sub_nonneg.mpr (hgconf.1 x hx).2
  have hfp : (u-g) p = 0 := by simp [(pure_mem p).2,hgconf.2]
  have hrec := reconstruction hc hs hg hB hW a ha p b (u-g) hf hfp n q r
    hsum haq har hqp hrp (fun z => by simpa [hq,hr] using hform z)
  have he : g = a p + g q • a q + g r • a r := by
    ext x
    have h1 := LinearMap.congr_fun hrec x
    have h2 := LinearMap.congr_fun hsum x
    change u x - g x = (u q - g q) * a q x + (u r - g r) * a r x at h1
    change a p x + a q x + a r x = u x at h2
    rw [(pure_mem q).2,(pure_mem r).2] at h1
    change g x = a p x + g q * a q x + g r * a r x
    nlinarith
  have hq01 : 0 ≤ g q ∧ g q ≤ 1 := by simpa [(pure_mem q).2] using hgconf.1 q (pure_mem q).1
  have hr01 : 0 ≤ g r ∧ g r ≤ 1 := by simpa [(pure_mem r).2] using hgconf.1 r (pure_mem r).1
  refine ⟨⟨q,r,hq ▸ chart_mem b hn.le,hr ▸ chart_mem b (by simp [hn]),hsum,he,hq01,hr01⟩,?_⟩
  intro x hx
  have hh := LinearMap.congr_fun he x
  change g x = a p x + g q * a q x + g r * a r x at hh
  linarith [mul_nonneg hq01.1 ((ha q).1.1 x hx).1,
    mul_nonneg hr01.1 ((ha r).1.1 x hx).1]

/-- The actual original positive dual cone annihilating p. -/
def zeroPositive (C : PointedCone ℝ V) (_u : V →ₗ[ℝ] ℝ) (p : V) : Set (V →ₗ[ℝ] ℝ) :=
  {f | (∀ x ∈ C, 0 ≤ f x) ∧ f p = 0}

/-- Positivity on the entire closed coordinate ball. -/
def ballPositive {d : ℕ} (h : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) : Prop :=
  ∀ z, ‖z‖ ≤ 1 → 0 ≤ h z

/-- Linear restriction through an arbitrary chart of the entire original D_p. -/
def restriction {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p : V}
    (b : ExclusionChart C u p) :
    (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ) where
  toFun f := f.toAffineMap.comp b.param
  map_add' _ _ := by ext z; rfl
  map_smul' _ _ := by ext z; rfl

private theorem positive_fiber [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p)) (p : pure C u)
    (b : ExclusionChart C u p) (h : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ)
    (hh : ballPositive h) : ∃! f, f ∈ zeroPositive C u p ∧ restriction b f = h := by
  obtain ⟨n, hn, hformula⟩ := affine_diameter b.dim_pos h
  obtain ⟨q,r,hq,hr,hsum,haq,har,hqp,hrp⟩ := diameter hc hs hg hB hW a ha p b n hn
  let F := h n • a q + h (-n) • a r
  have hF : F ∈ zeroPositive C u p := by
    refine ⟨fun x hx => ?_, ?_⟩
    · change 0 ≤ h n * a q x + h (-n) * a r x
      exact add_nonneg (mul_nonneg (hh n hn.le) ((ha q).1.1 x hx).1)
        (mul_nonneg (hh (-n) (by simp [hn])) ((ha r).1.1 x hx).1)
    · simp [F, hqp, hrp]
  have hres : restriction b F = h := by
    ext z
    change h n * a q (b.param z) + h (-n) * a r (b.param z) = h z
    rw [haq,har]
    exact (hformula z).symm
  refine ⟨F, ⟨hF,hres⟩, ?_⟩
  rintro f ⟨hf,he⟩
  have hval (z) : f (b.param z) = h z := congrArg (fun g => g z) he
  have hfq : f q = h n := by rw [← hq]; exact hval n
  have hfr : f r = h (-n) := by rw [← hr]; exact hval (-n)
  have hrec := reconstruction hc hs hg hB hW a ha p b f hf.1 hf.2 n q r
    hsum haq har hqp hrp (fun z => by rw [hval,hfq,hfr]; exact hformula z)
  simpa [F,hfq,hfr] using hrec

private theorem positive_bijection [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (a : pure C u → (V →ₗ[ℝ] ℝ))
    (ha : ∀ p : pure C u, common C u p (a p)) (p : pure C u)
    (b : ExclusionChart C u p) :
    Set.BijOn (restriction b) (zeroPositive C u p) {h | ballPositive h} := by
  have hmap : MapsTo (restriction b) (zeroPositive C u p) {h | ballPositive h} :=
    fun f hf z hz => hf.1 _ (chart_mem b hz).1.1
  refine ⟨hmap, ?_, ?_⟩
  · intro f hf g hgpos hfg
    obtain ⟨F, hF, huniq⟩ := positive_fiber hc hs hg hB hW a ha p b
      (restriction b f) (hmap hf)
    exact (huniq f ⟨hf,rfl⟩).trans (huniq g ⟨hgpos,hfg.symm⟩).symm
  · intro h hh
    obtain ⟨f,hf,_⟩ := positive_fiber hc hs hg hB hW a ha p b h hh
    exact ⟨f,hf⟩

private theorem affine_difference {d : ℕ} (h : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) :
    ∃ h₁ h₂, ballPositive h₁ ∧ ballPositive h₂ ∧ h = h₁ - h₂ := by
  obtain ⟨z,hz,hmin⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).exists_isMinOn
    ⟨0, by simp⟩ h.continuous_of_finiteDimensional.continuousOn
  let c := AffineMap.const ℝ (EuclideanSpace ℝ (Fin d)) |h z|
  refine ⟨h+c,c,?_,?_,by abel⟩
  · intro y hy
    have hm : h z ≤ h y := hmin (by simpa using hy)
    change 0 ≤ h y + |h z|
    linarith [neg_abs_le (h z)]
  · intro y _
    exact abs_nonneg _

omit [FiniteDimensional ℝ V] in
private theorem positive_span_difference {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    {p : V} {f : V →ₗ[ℝ] ℝ} (hf : f ∈ Submodule.span ℝ (zeroPositive C u p)) :
    ∃ g ∈ zeroPositive C u p, ∃ k ∈ zeroPositive C u p, f = g-k := by
  classical
  let S := Submodule.span ℝ (zeroPositive C u p)
  have hz : (0 : V →ₗ[ℝ] ℝ) ∈ zeroPositive C u p := by constructor <;> simp
  rcases subsingleton_or_nontrivial S with hS | hS
  · haveI := hS
    have he : f = 0 := congrArg S.subtype (Subsingleton.elim (⟨f,hf⟩ : S) 0)
    exact ⟨0,hz,0,hz,by simpa using he⟩
  · haveI := hS
    let Z : ConvexCone ℝ S := {
      carrier := {g | (g : V →ₗ[ℝ] ℝ) ∈ zeroPositive C u p}
      smul_mem' := by
        intro t ht g hg
        exact ⟨fun x hx => mul_nonneg ht.le (hg.1 x hx),by simp [hg.2]⟩
      add_mem' := by
        intro g hg k hk
        exact ⟨fun x hx => add_nonneg (hg.1 x hx) (hk.1 x hx),by simp [hg.2,hk.2]⟩ }
    have himage : S.subtype '' (Z : Set S) = zeroPositive C u p := by
      ext g
      constructor
      · rintro ⟨g,hg,rfl⟩
        exact hg
      · intro hg
        exact ⟨⟨g,Submodule.subset_span hg⟩,hg,rfl⟩
    have hspan : Submodule.span ℝ (Z : Set S) = ⊤ := by
      apply Submodule.map_injective_of_injective S.injective_subtype
      rw [Submodule.map_span,himage,Submodule.map_top,Submodule.range_subtype]
    have hrep := ConvexCone.IsReproducing.of_span_eq_top hspan
    have hm : (⟨f,hf⟩ : S) ∈ (Z : Set S)-(Z : Set S) := by
      rw [hrep]
      trivial
    obtain ⟨g,hg,k,hk,he⟩ := Set.mem_sub.mp hm
    exact ⟨g,hg,k,hk,(congrArg S.subtype he).symm⟩

/-- The three defining laws of a positive common extension, with no assumed
injectivity on the larger signed annihilator of p. -/
structure PositiveLift {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p : V}
    (b : ExclusionChart C u p)
    (Λ : (EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ)) : Prop where
  restrict_eq : ∀ h, restriction b (Λ h) = h
  at_point : ∀ h, Λ h p = 0
  positive : ∀ h, ballPositive h → ∀ x ∈ C, 0 ≤ Λ h x

/-- Full original extension laws, including intrinsic agreement across arbitrary
charts and the exact signed image span(Z_p). -/
structure ExtensionLaws {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p : V}
    (b : ExclusionChart C u p) (ap : V →ₗ[ℝ] ℝ)
    (Λ : (EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ))
    : Prop extends PositiveLift b Λ where
  unit_eq : Λ (AffineMap.const ℝ _ (1 : ℝ)) = u-ap
  inverse_positive : ∀ f ∈ zeroPositive C u p, Λ (restriction b f) = f
  budget : ∀ h, (∀ z, ‖z‖ ≤ 1 → 0 ≤ h z ∧ h z ≤ 1) →
    ∀ x ∈ C, 0 ≤ Λ h x ∧ Λ h x ≤ (u-ap) x
  range_eq : LinearMap.range Λ = Submodule.span ℝ (zeroPositive C u p)
  intrinsic : ∀ (c : ExclusionChart C u p)
    (Γ : (EuclideanSpace ℝ (Fin c.dim) →ᵃ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ)),
    PositiveLift c Γ → ∀ h k,
      (∀ z w, ‖z‖ ≤ 1 → ‖w‖ ≤ 1 → b.param z = c.param w → h z = k w) → Λ h = Γ k

/-- Original VII105.4 on all pure points, all positive annihilators, all signed
affine functions and every actual entire exclusion chart, under only W. -/
theorem whole_positive_extension [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) :
    ∃ a : pure C u → (V →ₗ[ℝ] ℝ),
      (∀ p : pure C u, common C u p (a p)) ∧
      (∀ (p : pure C u) f, common C u p f → f = a p) ∧
      (∀ (p : pure C u) g, confirms C u p g → ConfirmationNormalForm a p g) ∧
      ∀ (p : pure C u) (b : ExclusionChart C u p),
        Set.BijOn (restriction b) (zeroPositive C u p) {h | ballPositive h} ∧
        ∃! Λ, ExtensionLaws b (a p) Λ := by
  classical
  let a := fun p : pure C u => Classical.choose (common_exists hc hs hg hB p)
  have ha (p : pure C u) : common C u p (a p) := Classical.choose_spec (common_exists hc hs hg hB p)
  refine ⟨a,ha,fun p f hf => common_unique hc hs hg hB hW p hf (ha p),
    fun p g hgconf => confirmation_normal_form hc hs hg hB hW a ha p g hgconf,?_⟩
  intro p b
  have hbij := positive_bijection hc hs hg hB hW a ha p b
  refine ⟨hbij,?_⟩
  let S := Submodule.span ℝ (zeroPositive C u p)
  let R := (restriction b).comp S.subtype
  have hRinj : Function.Injective R := by
    intro f g hfg
    obtain ⟨f₁,hf₁,f₂,hf₂,hf⟩ := positive_span_difference f.property
    obtain ⟨g₁,hg₁,g₂,hg₂,hg'⟩ := positive_span_difference g.property
    have he : restriction b (f₁+g₂) = restriction b (g₁+f₂) := by
      change restriction b (f : V →ₗ[ℝ] ℝ) = restriction b (g : V →ₗ[ℝ] ℝ) at hfg
      rw [hf,hg',map_sub,map_sub] at hfg
      rw [map_add,map_add]
      exact sub_eq_sub_iff_add_eq_add.mp hfg
    have hfg' := hbij.injOn
      (show f₁+g₂ ∈ zeroPositive C u p from
        ⟨fun x hx => add_nonneg (hf₁.1 x hx) (hg₂.1 x hx), by simp [hf₁.2,hg₂.2]⟩)
      (show g₁+f₂ ∈ zeroPositive C u p from
        ⟨fun x hx => add_nonneg (hg₁.1 x hx) (hf₂.1 x hx), by simp [hg₁.2,hf₂.2]⟩) he
    apply Subtype.ext
    rw [hf,hg']
    exact sub_eq_sub_iff_add_eq_add.mpr hfg'
  have hRsurj : Function.Surjective R := by
    intro h
    obtain ⟨h₁,h₂,hh₁,hh₂,hh⟩ := affine_difference h
    obtain ⟨f,hf,_⟩ := positive_fiber hc hs hg hB hW a ha p b h₁ hh₁
    obtain ⟨g,hg',_⟩ := positive_fiber hc hs hg hB hW a ha p b h₂ hh₂
    refine ⟨⟨f-g,S.sub_mem (Submodule.subset_span hf.1) (Submodule.subset_span hg'.1)⟩,?_⟩
    change restriction b (f-g) = h
    rw [map_sub,hf.2,hg'.2,← hh]
  let e := LinearEquiv.ofBijective R ⟨hRinj,hRsurj⟩
  let Λ := S.subtype.comp e.symm.toLinearMap
  have hright (h) : restriction b (Λ h) = h := e.apply_symm_apply h
  have hrange (h) : Λ h ∈ S := (e.symm h).property
  have hleft (f) (hf : f ∈ S) : Λ (restriction b f) = f := by
    exact congrArg S.subtype (e.symm_apply_apply ⟨f,hf⟩)
  have hleftpos (f) (hf : f ∈ zeroPositive C u p) : Λ (restriction b f) = f :=
    hleft f (Submodule.subset_span hf)
  have hpos (h) (hh : ballPositive h) : ∀ x ∈ C, 0 ≤ Λ h x := by
    obtain ⟨f,hf,_⟩ := positive_fiber hc hs hg hB hW a ha p b h hh
    rw [← hf.2,hleftpos f hf.1]
    exact hf.1.1
  have hat (h) : Λ h p = 0 := by
    obtain ⟨f,hf,g,hg',he⟩ := positive_span_difference (hrange h)
    rw [he]
    simp [hf.2,hg'.2]
  have hunitpos : u-a p ∈ zeroPositive C u p := by
    exact ⟨fun x hx => sub_nonneg.mpr ((ha p).1.1 x hx).2,
      by simp [(pure_mem p).2,(ha p).1.2]⟩
  have hunitres : restriction b (u-a p) = AffineMap.const ℝ _ (1 : ℝ) := by
    apply affine_ball_ext
    intro z hz
    change u (b.param z) - a p (b.param z) = 1
    rw [(chart_mem b hz).1.2,(ha p).2 _ (chart_mem b hz)]
    ring
  have hunit : Λ (AffineMap.const ℝ _ (1 : ℝ)) = u-a p := by
    rw [← hunitres]
    exact hleftpos _ hunitpos
  have hΓrange (c : ExclusionChart C u p)
      (Γ : (EuclideanSpace ℝ (Fin c.dim) →ᵃ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ))
      (hΓ : PositiveLift c Γ) (k) : Γ k ∈ S := by
    obtain ⟨k₁,k₂,hk₁,hk₂,hk⟩ := affine_difference k
    rw [hk,map_sub]
    exact S.sub_mem
      (Submodule.subset_span ⟨hΓ.positive k₁ hk₁,hΓ.at_point k₁⟩)
      (Submodule.subset_span ⟨hΓ.positive k₂ hk₂,hΓ.at_point k₂⟩)
  have hintr (c : ExclusionChart C u p)
      (Γ : (EuclideanSpace ℝ (Fin c.dim) →ᵃ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ))
      (hΓ : PositiveLift c Γ) (h k)
      (he : ∀ z w, ‖z‖ ≤ 1 → ‖w‖ ≤ 1 → b.param z = c.param w → h z = k w) :
      Λ h = Γ k := by
    have hre : restriction b (Γ k) = h := by
      apply affine_ball_ext
      intro z hz
      obtain ⟨w,hw,heq⟩ := c.whole.symm ▸ chart_mem b hz
      have hkw := congrArg (fun f => f w) (hΓ.restrict_eq k)
      change Γ k (c.param w) = k w at hkw
      change Γ k (b.param z) = h z
      rw [← heq,hkw]
      exact (he z w hz (by simpa using hw) heq.symm).symm
    rw [← hre, hleft _ (hΓrange c Γ hΓ k)]
  have hLaws : ExtensionLaws b (a p) Λ := {
    restrict_eq := hright
    at_point := hat
    positive := hpos
    unit_eq := hunit
    inverse_positive := hleftpos
    range_eq := by
      apply le_antisymm
      · rintro f ⟨h,rfl⟩
        exact hrange h
      · intro f hf
        exact ⟨restriction b f,hleft f hf⟩
    intrinsic := hintr
    budget := by
      intro h hh x hx
      refine ⟨hpos h (fun z hz => (hh z hz).1) x hx,?_⟩
      have hp := hpos (AffineMap.const ℝ _ (1 : ℝ) - h)
        (fun z hz => sub_nonneg.mpr (hh z hz).2) x hx
      rw [map_sub,hunit] at hp
      exact sub_nonneg.mp hp }
  refine ⟨Λ,hLaws,?_⟩
  intro Γ hΓ
  apply LinearMap.ext
  intro h
  exact (hintr b Γ hΓ.toPositiveLift h h (fun z w _ _ he => congrArg h (b.injective he))).symm

/-- The original all-space arc identity in arbitrary exclusion coordinates.
The coordinate tangent w represents the actual vector b.param.linear w, whose
intrinsic ball norm is norm w. The vanishing statement is on the whole M_p. -/
def ArcFamily {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (a : pure C u → (V →ₗ[ℝ] ℝ)) : Prop :=
  ∀ (q p : pure C u) (b : ExclusionChart C u q)
    (e w : EuclideanSpace ℝ (Fin b.dim)),
    ‖e‖ = 1 → b.param e = p → w ≠ 0 → ⟪e,w⟫ = 0 →
    ∃ (r : pure C u) (γ : ℝ → pure C u) (B : V →ₗ[ℝ] ℝ),
      b.param (-e) = r ∧ a p + a q + a r = u ∧ (r : V) ∈ exclusion C u p ∧
      (∀ t, (γ t : V) = b.param (Real.cos t • e + Real.sin t • (‖w‖⁻¹ • w))) ∧
      (∀ t, a (γ t) = ((1+Real.cos t)/2) • a p +
        ((1-Real.cos t)/2) • a r + Real.sin t • B) ∧
      B p = 0 ∧ B r = 0 ∧ B (b.param.linear w) = ‖w‖ / 2 ∧
      (∀ x ∈ Submodule.span ℝ (insert (p : V) (exclusion C u p)), B x = 0)

/-- The whole-space VIII108.5 consumer of the single common extension. No
projection, cross-ball reciprocity, common center or spectral expansion enters. -/
theorem whole_arc_effect [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) :
    ∃ a : pure C u → (V →ₗ[ℝ] ℝ),
      (∀ p : pure C u, common C u p (a p)) ∧
      (∀ (p : pure C u) f, common C u p f → f = a p) ∧ ArcFamily a := by
  classical
  obtain ⟨a,ha,hunique,_,hcharts⟩ := whole_positive_extension hc hs hg hB hW
  refine ⟨a,ha,hunique,?_⟩
  intro q p b e w he hep hw hew
  obtain ⟨Λ,hΛ,_⟩ := (hcharts q b).2
  let n := ‖w‖⁻¹ • w
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hn : ‖n‖ = 1 := by simp [n,norm_smul,hwpos.ne']
  have hen : ⟪e,n⟫ = 0 := by simp [n,inner_smul_right,hew]
  have hne : ⟪n,e⟫ = 0 := by rw [real_inner_comm]; exact hen
  obtain ⟨p',r,hp',hr,hsum,hap',har,_,_⟩ := diameter hc hs hg hB hW a ha q b e he
  have hp'p : p' = p := Subtype.ext (hp'.symm.trans hep)
  subst p'
  have hframe : a p+a q+a r=u := by
    calc
      a p+a q+a r = a q+a p+a r := by abel
      _ = u := hsum
  have hrDp : (r : V) ∈ exclusion C u p := by
    refine ⟨pure_mem r,a p,(ha p).1,?_⟩
    rw [← hr,hap',inner_neg_right,real_inner_self_eq_norm_sq,he]
    norm_num
  let H : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] ℝ :=
    (1/2 : ℝ) • ((InnerProductSpace.toDual ℝ _) n).toLinearMap.toAffineMap
  let B := Λ H
  have hH (y) : H y = ⟪n,y⟫ / 2 := by simp [H,div_eq_mul_inv,mul_comm]
  have hBy (y) : B (b.param y) = ⟪n,y⟫ / 2 := by
    have hh := congrArg (fun f => f y) (hΛ.restrict_eq H)
    exact hh.trans (hH y)
  have hBp : B p = 0 := by rw [← hep,hBy,hne]; norm_num
  have hBr : B r = 0 := by rw [← hr,hBy,inner_neg_right,hne]; norm_num
  have hBz : B (b.param.linear w) = ‖w‖ / 2 := by
    have hlin : b.param.linear w = b.param w - b.param 0 := by
      simpa using b.param.linear_apply_vsub w 0
    rw [hlin,map_sub,hBy,hBy,inner_zero_right,zero_div,sub_zero]
    simp only [n,real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
  have hfix (s : pure C u) (hsD : (s : V) ∈ exclusion C u q) :
      Λ (restriction b (a s)) = a s := by
    exact hΛ.inverse_positive _ ⟨fun x hx => ((ha s).1.1 x hx).1,
      (ha s).2 q ((exclusion_symmetric q s).mp hsD)⟩
  have hfixp := hfix p (hep ▸ chart_mem b he.le)
  have hfixr := hfix r (hr ▸ chart_mem b (by simp [he]))
  have hcircle (c s : ℝ) (hcs : c^2+s^2=1) :
      ∃ v : pure C u, (v : V) = b.param (c • e+s • n) ∧
        a v = ((1+c)/2) • a p + ((1-c)/2) • a r + s • B := by
    let d := c • e+s • n
    have hd : ‖d‖ = 1 := by
      have hi : ⟪d,d⟫ = 1 := by
        simp only [d,inner_add_left,inner_add_right,real_inner_smul_left,
          inner_smul_right,real_inner_self_eq_norm_sq,he,hn,hen,hne]
        nlinarith
      rw [real_inner_self_eq_norm_sq] at hi
      nlinarith [norm_nonneg d]
    obtain ⟨v,v',hv,_,_,hav,_,_,_⟩ := diameter hc hs hg hB hW a ha q b d hd
    have hres : restriction b (a v) = ((1+c)/2) • restriction b (a p) +
        ((1-c)/2) • restriction b (a r) + s • H := by
      ext y
      change a v (b.param y) = ((1+c)/2) * a p (b.param y) +
        ((1-c)/2) * a r (b.param y) + s * H y
      rw [hav,hap',har,hH]
      simp only [d,inner_add_left,real_inner_smul_left]
      ring
    have hh := congrArg Λ hres
    rw [map_add,map_add,map_smul,map_smul,map_smul,hfixp,hfixr,
      hfix v (hv ▸ chart_mem b hd.le)] at hh
    exact ⟨v,hv.symm,hh⟩
  have hangles (t : ℝ) := hcircle (Real.cos t) (Real.sin t) (Real.cos_sq_add_sin_sq t)
  let γ := fun t : ℝ => Classical.choose (hangles t)
  have hγ (t : ℝ) := Classical.choose_spec (hangles t)
  have hBzero : ∀ x ∈ exclusion C u p, B x = 0 := by
    intro x hx
    have hax : a p x = 0 := (ha p).2 x hx
    have hquad (t : ℝ) : 0 ≤ a r x * (t*t) + (2*B x)*t + 0 := by
      let D := 1+t^2
      have hD : 0 < D := by dsimp [D]; positivity
      have hcircleunit : ((1-t^2)/D)^2+(2*t/D)^2=1 := by
        dsimp [D]
        field_simp
        ring
      obtain ⟨v,_,hv⟩ := hcircle ((1-t^2)/D) (2*t/D) hcircleunit
      have hpv := ((ha v).1.1 x hx.1.1).1
      have hvx := LinearMap.congr_fun hv x
      change a v x = ((1+(1-t^2)/D)/2) * a p x +
        ((1-(1-t^2)/D)/2) * a r x + (2*t/D) * B x at hvx
      rw [hax,mul_zero,zero_add] at hvx
      have heval : a v x * D = a r x * (t*t) + (2*B x)*t + 0 := by
        rw [hvx]
        dsimp [D]
        field_simp
        ring
      rw [← heval]
      exact mul_nonneg hpv hD.le
    have hd := discrim_le_zero hquad
    simp only [discrim,mul_zero,sub_zero] at hd
    nlinarith [sq_nonneg (B x)]
  have hspan : ∀ x ∈ Submodule.span ℝ (insert (p : V) (exclusion C u p)), B x = 0 := by
    have hh : Submodule.span ℝ (insert (p : V) (exclusion C u p)) ≤ LinearMap.ker B := by
      apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hBp
      · exact hBzero x hx
    exact hh
  exact ⟨r,γ,B,hr,hframe,hrDp,fun t => (hγ t).1,fun t => (hγ t).2,hBp,hBr,hBz,hspan⟩

#print axioms whole_positive_extension
#print axioms whole_arc_effect

end D5.S3.Quantum.Foundation.CommonPositiveExtension
