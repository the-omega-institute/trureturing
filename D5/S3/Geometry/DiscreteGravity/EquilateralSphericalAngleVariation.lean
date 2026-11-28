/- GID: D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation
   generality: G
   mirror-B: D5/B/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv]
   utility: none
   digest: Explicit unit-sphere equilateral triangles with all tangent-projection angle derivatives one and spherical excess derivative three. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! An explicit one-parameter family of spherical equilateral triangles.
The Gram matrix has diagonal one and off-diagonal r = cos(t)/(1-cos(t)).
On the open interval (π/3, π), the tangent projections have angle t.

The spherical excess is defined by 3*t-π. Its interpretation as intrinsic
unit-sphere area uses the classical Girard theorem for the corresponding
geodesic triangle; the area interpretation remains external to this proof.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators RealInnerProductSpace Topology
open Filter

namespace D5.S3.Geometry.DiscreteGravity.EquilateralSphericalAngleVariation

private theorem inner_coordinates (x y : EuclideanSpace ℝ (Fin 3)) : ⟪x, y⟫ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

private def sphericalDot (t : ℝ) : ℝ := Real.cos t / (1 - Real.cos t)

/-- For angles in (π/3, π), three unit vectors with the same pairwise dot product. -/
def sphericalVertices (t : ℝ) (i : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  let r := sphericalDot t
  let a := Real.sqrt (1 - r)
  let b := (Real.sqrt (1 + 2 * r) - a) / 3
  WithLp.toLp 2 (fun k => (if i = k then a else 0) + b)

/-- The angle between the two tangent projections at vertex i. -/
def sphericalAngle (t : ℝ) (i j k : Fin 3) : ℝ :=
  let p := sphericalVertices t
  let x := p j - ⟪p i, p j⟫ • p i
  let y := p k - ⟪p i, p k⟫ • p i
  Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))

/-- The spherical excess of the triangle with three equal angles t. -/
def sphericalExcess (t : ℝ) : ℝ := 3 * t - Real.pi

private theorem spherical_gram (t : ℝ) (ht : t ∈ Set.Ioo (Real.pi / 3) Real.pi) :
    -1 / 2 < sphericalDot t ∧ sphericalDot t < 1 ∧
    ∀ i j, ⟪sphericalVertices t i, sphericalVertices t j⟫ =
      if i = j then 1 else sphericalDot t := by
  have hc : Real.cos t < 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.strictAntiOn_cos
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩ ht.1
  have hcos : -1 < Real.cos t := by
    rw [← Real.cos_pi]
    exact Real.strictAntiOn_cos ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩
      ⟨Real.pi_pos.le, le_rfl⟩ ht.2
  have hden : 0 < 1 - Real.cos t := by linarith
  have hl : -1 / 2 < sphericalDot t := by
    unfold sphericalDot
    rw [lt_div_iff₀ hden]
    linarith
  have hr : sphericalDot t < 1 := by
    unfold sphericalDot
    rw [div_lt_iff₀ hden]
    linarith
  let r := sphericalDot t
  let a := Real.sqrt (1 - r)
  let b := (Real.sqrt (1 + 2 * r) - a) / 3
  have ha : a ^ 2 = 1 - r := Real.sq_sqrt (by linarith)
  have hb : 2 * a * b + 3 * b ^ 2 = r := by
    dsimp [b]
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + 2 * r by linarith)]
  refine ⟨hl, hr, fun i j => ?_⟩
  rw [inner_coordinates]
  change (∑ k : Fin 3, ((if i = k then a else 0) + b) *
    ((if j = k then a else 0) + b)) = _
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_three] <;> nlinarith
private theorem spherical_angle_eq (t : ℝ) (ht : t ∈ Set.Ioo (Real.pi / 3) Real.pi)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sphericalAngle t i j k = t := by
  obtain ⟨hl, hr, hg⟩ := spherical_gram t ht
  let p := sphericalVertices t
  let r := sphericalDot t
  have hdiag : ⟪p i, p i⟫ = 1 := by simpa using hg i i
  have hpj : ⟪p j, p j⟫ = 1 := by simpa using hg j j
  have hpk : ⟪p k, p k⟫ = 1 := by simpa using hg k k
  have hj : ⟪p i, p j⟫ = r := by simpa [hij] using hg i j
  have hk : ⟪p i, p k⟫ = r := by simpa [hik] using hg i k
  have hjk' : ⟪p j, p k⟫ = r := by simpa [hjk] using hg j k
  have hji : ⟪p j, p i⟫ = r := (real_inner_comm _ _).trans hj
  have hki : ⟪p k, p i⟫ = r := (real_inner_comm _ _).trans hk
  let x := p j - r • p i
  let y := p k - r • p i
  have hnormx : ‖x‖ ^ 2 = 1 - r ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [x, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hdiag, hj, hji, hpj]
    ring
  have hnormy : ‖y‖ ^ 2 = 1 - r ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [y, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hdiag, hk, hki, hpk]
    ring
  have hp : 0 < 1 - r ^ 2 := by unfold r; nlinarith
  have hp' : ‖x‖ = ‖y‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
  have hxy : ⟪x, y⟫ = r - r ^ 2 := by
    simp only [x, y, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hdiag, hk, hji, hjk']
    ring
  unfold sphericalAngle
  dsimp only
  change Real.arccos (⟪p j - ⟪p i, p j⟫ • p i, p k - ⟪p i, p k⟫ • p i⟫ /
    (‖p j - ⟪p i, p j⟫ • p i‖ * ‖p k - ⟪p i, p k⟫ • p i‖)) = t
  rw [hj, hk]
  change Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖)) = t
  rw [← hp', ← pow_two, hnormx, hxy]
  have hr' : r = Real.cos t * (1 + r) := by
    dsimp [r, sphericalDot]
    have hc : Real.cos t < 1 := by
      rw [← Real.cos_zero]
      exact Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
        ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩ (by linarith [ht.1, Real.pi_pos])
    field_simp [hc.ne']
    ring
  have hfrac : (r - r ^ 2) / (1 - r ^ 2) = Real.cos t := by
    apply (div_eq_iff hp.ne').mpr
    linear_combination (1 - r) * hr'
  rw [hfrac, Real.arccos_cos (by linarith [ht.1, Real.pi_pos]) ht.2.le]

theorem equilateral_spherical_angle_variation (t : ℝ)
    (ht : t ∈ Set.Ioo (Real.pi / 3) Real.pi) :
    (∀ i, ‖sphericalVertices t i‖ = 1) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k → HasDerivAt (fun s => sphericalAngle s i j k) 1 t) ∧
    HasDerivAt sphericalExcess 3 t ∧
    (∑ i : Fin 3, deriv (fun s => sphericalAngle s i (i + 1) (i + 2)) t) =
      deriv sphericalExcess t ∧ deriv sphericalExcess t ≠ 0 := by
  have hexcess : HasDerivAt sphericalExcess 3 t := by
    convert ((hasDerivAt_id t).const_mul 3).sub_const Real.pi using 1
    · rfl
    · norm_num
  have hn : ∀ᶠ s in 𝓝 t, s ∈ Set.Ioo (Real.pi / 3) Real.pi := isOpen_Ioo.mem_nhds ht
  have hangle (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      HasDerivAt (fun s => sphericalAngle s i j k) 1 t :=
    (hasDerivAt_id t).congr_of_eventuallyEq
      (hn.mono fun s hs => spherical_angle_eq s hs i j k hij hik hjk)
  refine ⟨fun i => ?_, hangle, hexcess, ?_, by norm_num [hexcess.deriv]⟩
  · have h := (spherical_gram t ht).2.2 i i
    simp only [ite_eq_left, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (sphericalVertices t i)]
  · rw [hexcess.deriv]
    simp only [show ∀ i : Fin 3,
        deriv (fun s => sphericalAngle s i (i + 1) (i + 2)) t = 1 from fun i =>
      (hangle i (i + 1) (i + 2) (by fin_cases i <;> decide)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)).deriv]
    simp


end D5.S3.Geometry.DiscreteGravity.EquilateralSphericalAngleVariation
