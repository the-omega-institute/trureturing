/- GID: D5/S3/Quantum/Analysis/CStarTriangleEqualityPlane
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CStarTriangleEqualityPlane
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangle-equality rigidity for complex C-star algebras. -/

/-
admission_basis: escape-witness
escape_witness: first_axis_lower
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27516
Declarations (definition rows carry no proof-shape claim):
NormParallel: definition; consumers: none.
TEAPair: definition; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary.seminorm_algebraically_unital_rigidity, D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary.seminorm_cross_scale_of_continuous, D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary.seminorm_local_corner_cross, D5.S3.Quantum.Analysis.CStarTriangleEqualityNonunitalContinuity.nine_corners_bound, D5.S3.Quantum.Analysis.CStarTriangleEqualityNonunitalContinuity.seminorm_nonunital_lipschitz, D5.S3.Quantum.Analysis.CStarTriangleEqualityNonunitalContinuity.spectral_three_points_lipschitz, PreservesTEAForward, dominant_first, face_norm_sum, product_plane_scale, seminorm_on_isometric_plane, seminorm_orthogonal_axes, seminorm_orthogonal_unit_scale, seminorm_product_rigidity, seminorm_two_coordinate_rigidity, swap_preserves_forward, D5.S3.Quantum.Analysis.CStarTriangleEqualityPreservers.PreservesTEABothDirections, D5.S3.Quantum.Analysis.CStarTriangleEqualityPreservers.claim_of_seminorm_rigidity, D5.S3.Quantum.Analysis.CStarTriangleEqualityPreservers.result, D5.S3.Quantum.Analysis.CStarTriangleEqualityPreservers.seminorm_rigidity, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital.seminorm_realPart_le, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital.seminorm_spectral_real_direction_lower, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital.seminorm_unital_rigidity, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_normal_scale, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_scale_of_spectral_norm_attainment, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_selfadjoint_scale, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_spectral_plane_scale, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_tea_at_one, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_tea_smul, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_unital_bound, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_unital_lipschitz, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.tea_realpart, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.tea_slope_eq_of_quadratic_direction, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.tea_smul_right.
PreservesTEAForward: definition; consumers: axes_equal, dominant_first, face_norm_sum, first_axis_lower, swap_preserves_forward, two_coordinate_rigidity.
face_norm_sum: proof_shape: bind-only; consumers: axes_equal, first_axis_lower.
first_axis_lower: proof_shape: content; consumers: dominant_first.
swap_preserves_forward: proof_shape: bind-only; consumers: axes_equal, two_coordinate_rigidity.
axes_equal: proof_shape: bind-only; consumers: two_coordinate_rigidity.
dominant_first: proof_shape: content; consumers: two_coordinate_rigidity.
two_coordinate_rigidity: proof_shape: content; consumers: seminorm_two_coordinate_rigidity.
seminorm_two_coordinate_rigidity: proof_shape: content; consumers: seminorm_on_isometric_plane.
affineFacePlane: definition; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_spectral_plane_scale.
seminorm_on_isometric_plane: proof_shape: content; consumers: product_plane_scale, seminorm_orthogonal_axes, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_spectral_plane_scale.
norm_add_eq_max_of_cstar_orthogonal: proof_shape: bind-only; consumers: norm_smul_add_smul_of_cstar_orthogonal.
norm_smul_add_smul_of_cstar_orthogonal: proof_shape: bind-only; consumers: orthogonalSupPlane, seminorm_orthogonal_axes.
orthogonalSupPlane: definition; consumers: seminorm_orthogonal_axes.
seminorm_orthogonal_axes: proof_shape: content; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityNonunitalContinuity.nine_corners_bound, seminorm_orthogonal_unit_scale.
seminorm_orthogonal_unit_scale: proof_shape: content; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityNonunitalContinuity.nine_corners_bound.
productSupPlane: definition; consumers: product_plane_scale.
product_plane_scale: proof_shape: content; consumers: seminorm_product_rigidity.
unit_direction: proof_shape: bind-only; consumers: seminorm_product_rigidity.
seminorm_product_rigidity: proof_shape: content; consumers: none.
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

namespace D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane

section

/-- Norm parallelism over the complex field, including zero elements. -/
def NormParallel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b : E) : Prop :=
  ∃ μ : ℂ, ‖μ‖ = 1 ∧ ‖a + μ • b‖ = ‖a‖ + ‖b‖

/-- A triangle equality attaining pair; the source takes the phase to be one. -/
def TEAPair {E : Type*} [NormedAddCommGroup E] (a b : E) : Prop :=
  ‖a + b‖ = ‖a‖ + ‖b‖


end
section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

private def PreservesTEAForward (T : (ℂ × ℂ) →ₗ[ℂ] E) : Prop :=
  ∀ x y, TEAPair x y → ‖T x + T y‖ = ‖T x‖ + ‖T y‖

private theorem face_norm_sum (T : (ℂ × ℂ) →ₗ[ℂ] E)
    (hT : PreservesTEAForward T) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖T (1, z)‖ + ‖T (1, -z)‖ = 2 * ‖T (1, 0)‖ := by
  have hp : TEAPair ((1, z) : ℂ × ℂ) (1, -z) := by
    norm_num [TEAPair, Prod.norm_def, max_eq_left hz]
  have hs : ((1, z) + (1, -z) : ℂ × ℂ) = (2 : ℂ) • (1, 0) := by
    ext <;> norm_num
  calc
    ‖T (1, z)‖ + ‖T (1, -z)‖ = ‖T (1, z) + T (1, -z)‖ := (hT _ _ hp).symm
    _ = 2 * ‖T (1, 0)‖ := by rw [← map_add, hs, map_smul, norm_smul]; norm_num

private theorem first_axis_lower (T : (ℂ × ℂ) →ₗ[ℂ] E)
    (hT : PreservesTEAForward T) (x y : ℂ) :
    ‖T (1, 0)‖ * ‖x‖ ≤ ‖T (x, y)‖ := by
  obtain ⟨f, hf, hfe⟩ := exists_dual_vector'' ℂ (T (1, 0))
  let g : (ℂ × ℂ) →ₗ[ℂ] ℂ := f.toLinearMap.comp T
  have hge : g (1, 0) = (‖T (1, 0)‖ : ℂ) := hfe
  have hgl (v : ℂ × ℂ) : ‖g v‖ ≤ ‖T v‖ := by
    exact (f.le_opNorm (T v)).trans (mul_le_of_le_one_left (norm_nonneg _) hf)
  have hreal (z : ℂ) (hz : ‖z‖ ≤ 1) : (g (1, z)).im = 0 := by
    have he : g (1, z) + g (1, -z) = 2 * (‖T (1, 0)‖ : ℂ) := by
      rw [← map_add]
      have hs : ((1, z) + (1, -z) : ℂ × ℂ) = (2 : ℂ) • (1, 0) := by
        ext <;> norm_num
      rw [hs, map_smul, hge, smul_eq_mul]
    have hre : (g (1, z)).re + (g (1, -z)).re = 2 * ‖T (1, 0)‖ := by
      simpa using congrArg Complex.re he
    have hn : (g (1, z)).re = ‖g (1, z)‖ := by
      have hs := face_norm_sum T hT hz
      have ha := hgl (1, z)
      have hb := hgl (1, -z)
      have hc := Complex.re_le_norm (g (1, z))
      have hd := Complex.re_le_norm (g (1, -z))
      linarith
    apply Complex.abs_re_eq_norm.mp
    rw [abs_of_nonneg (by rw [hn]; exact norm_nonneg _)]
    exact hn
  have hdecomp (a b : ℂ) : g (a, b) = a * g (1, 0) + b * g (0, 1) := by
    have hs : ((a, b) : ℂ × ℂ) = a • (1, 0) + b • (0, 1) := by ext <;> norm_num
    rw [hs, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hg2im : (g (0, 1)).im = 0 := by
    have hr := hreal 1 (by norm_num)
    rw [hdecomp, hge] at hr
    simpa using hr
  have hg2re : (g (0, 1)).re = 0 := by
    have hr := hreal Complex.I (by norm_num)
    rw [hdecomp, hge] at hr
    simpa using hr
  have hg2 : g (0, 1) = 0 := Complex.ext hg2re hg2im
  have hgv : g (x, y) = x * (‖T (1, 0)‖ : ℂ) := by rw [hdecomp, hg2, hge]; simp
  have hl := hgl (x, y)
  rw [hgv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at hl
  simpa [mul_comm] using hl

private theorem swap_preserves_forward (T : (ℂ × ℂ) →ₗ[ℂ] E)
    (hT : PreservesTEAForward T) : PreservesTEAForward (T.comp (LinearEquiv.prodComm ℂ ℂ ℂ).toLinearMap) := by
  intro v w hvw
  apply hT
  change TEAPair (v.2, v.1) (w.2, w.1)
  simpa [TEAPair, Prod.norm_def, max_comm] using hvw

private theorem axes_equal (T : (ℂ × ℂ) →ₗ[ℂ] E)
    (hT : PreservesTEAForward T) : ‖T (1, 0)‖ = ‖T (0, 1)‖ := by
  have ha := face_norm_sum T hT (z := 1) (by norm_num)
  have hb := face_norm_sum (T.comp (LinearEquiv.prodComm ℂ ℂ ℂ).toLinearMap) (swap_preserves_forward T hT)
    (z := 1) (by norm_num)
  have he : ‖T (-1, 1)‖ = ‖T (1, -1)‖ := by
    have hv : ((-1, 1) : ℂ × ℂ) = -((1, -1) : ℂ × ℂ) := by ext <;> norm_num
    rw [hv, map_neg, norm_neg]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.swap_prod_mk] at hb
  rw [he] at hb
  linarith

private theorem dominant_first (T : (ℂ × ℂ) →ₗ[ℂ] E)
    (hT : PreservesTEAForward T) {x y : ℂ} (hxy : ‖y‖ ≤ ‖x‖) :
    ‖T (x, y)‖ = ‖T (1, 0)‖ * ‖x‖ := by
  have hp : TEAPair ((x, y) : ℂ × ℂ) (x, -y) := by
    have hs : ((x, y) + (x, -y) : ℂ × ℂ) = (2 : ℂ) • (x, 0) := by
      ext <;> simp [two_mul]
    unfold TEAPair
    rw [hs, norm_smul]
    norm_num [Prod.norm_def, max_eq_left hxy, max_eq_left (norm_nonneg x)]
    ring
  have hs : ((x, y) + (x, -y) : ℂ × ℂ) = (2 * x : ℂ) • (1, 0) := by
    ext <;> simp [two_mul]
  have ht := hT _ _ hp
  change ‖T (x, y) + T (x, -y)‖ = _ at ht
  rw [← map_add, hs, map_smul, norm_smul, norm_mul] at ht
  norm_num at ht
  have ha := first_axis_lower T hT x y
  have hb := first_axis_lower T hT x (-y)
  nlinarith

/-- Complex two-coordinate TEA preservers into any normed space are scaled isometric embeddings. -/
private theorem two_coordinate_rigidity (T : (ℂ × ℂ) →ₗ[ℂ] E)
    (hT : PreservesTEAForward T) (v : ℂ × ℂ) :
    ‖T v‖ = ‖T (1, 0)‖ * ‖v‖ := by
  rcases v with ⟨x, y⟩
  rcases le_total ‖y‖ ‖x‖ with h | h
  · simpa [Prod.norm_def, max_eq_left h] using dominant_first T hT h
  · have ht := dominant_first (T.comp (LinearEquiv.prodComm ℂ ℂ ℂ).toLinearMap) (swap_preserves_forward T hT) h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.swap_prod_mk] at ht
    rw [← axes_equal T hT] at ht
    simpa [Prod.norm_def, max_eq_right h] using ht

/-- The nominated finite-valued complex seminorm rigidity statement on the sup-norm plane. -/
private theorem seminorm_two_coordinate_rigidity (p : Seminorm ℂ (ℂ × ℂ))
    (hp : ∀ v w : ℂ × ℂ, TEAPair v w → p (v + w) = p v + p w)
    (v : ℂ × ℂ) : p v = p (1, 0) * ‖v‖ := by
  letI : SeminormedAddCommGroup (ℂ × ℂ) :=
    p.toAddGroupSeminorm.toSeminormedAddCommGroup
  letI : NormedSpace ℂ (ℂ × ℂ) :=
    { norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }
  have h := @two_coordinate_rigidity (ℂ × ℂ) _ _ (LinearMap.id : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ))
    (by
      intro x y hxy
      change p (x + y) = p x + p y
      exact hp x y hxy) v
  exact h

end

section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A continuous real parameter attaining zero and one gives a complex sup plane. -/
def affineFacePlane (t : C(X, ℝ)) (ht : ∀ x, t x ∈ Set.Icc (0 : ℝ) 1)
    (x₀ x₁ : X) (h₀ : t x₀ = 0) (h₁ : t x₁ = 1) :
    (ℂ × ℂ) →ₗᵢ[ℂ] C(X, ℂ) where
  toFun v := ⟨fun x => (1 - (t x : ℂ)) * v.1 + (t x : ℂ) * v.2, by fun_prop⟩
  map_add' v w := by
    ext x
    change (1 - (t x : ℂ)) * (v.1 + w.1) + (t x : ℂ) * (v.2 + w.2) =
      ((1 - (t x : ℂ)) * v.1 + (t x : ℂ) * v.2) +
      ((1 - (t x : ℂ)) * w.1 + (t x : ℂ) * w.2)
    ring
  map_smul' z v := by
    ext x
    change (1 - (t x : ℂ)) * (z * v.1) + (t x : ℂ) * (z * v.2) =
      z * ((1 - (t x : ℂ)) * v.1 + (t x : ℂ) * v.2)
    ring
  norm_map' v := by
    let f : C(X, ℂ) := ⟨fun x => (1 - (t x : ℂ)) * v.1 + (t x : ℂ) * v.2, by fun_prop⟩
    change ‖f‖ = ‖v‖
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg v)).mpr
      intro x
      change ‖(1 - (t x : ℂ)) * v.1 + (t x : ℂ) * v.2‖ ≤ ‖v‖
      have ht0 := (ht x).1
      have ht1 := (ht x).2
      have hnorm : ‖(1 - (t x : ℂ))‖ = 1 - t x := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_of_nonneg (sub_nonneg.mpr ht1)]
      calc
        _ ≤ ‖1 - (t x : ℂ)‖ * ‖v.1‖ + ‖(t x : ℂ)‖ * ‖v.2‖ := by
          simpa only [norm_mul] using norm_add_le ((1 - (t x : ℂ)) * v.1) ((t x : ℂ) * v.2)
        _ = (1 - t x) * ‖v.1‖ + t x * ‖v.2‖ := by
          rw [hnorm, Complex.norm_real, Real.norm_of_nonneg ht0]
        _ ≤ (1 - t x) * ‖v‖ + t x * ‖v‖ := add_le_add
          (mul_le_mul_of_nonneg_left (norm_fst_le v) (sub_nonneg.mpr ht1))
          (mul_le_mul_of_nonneg_left (norm_snd_le v) ht0)
        _ = ‖v‖ := by ring
    · rw [Prod.norm_def]
      apply max_le
      · have h := ContinuousMap.norm_coe_le_norm f x₀
        simpa only [f, ContinuousMap.coe_mk, h₀, Complex.ofReal_zero,
          sub_zero, one_mul, zero_mul, add_zero] using h
      · have h := ContinuousMap.norm_coe_le_norm f x₁
        simpa only [f, ContinuousMap.coe_mk, h₁, Complex.ofReal_one,
          sub_self, zero_mul, one_mul, zero_add] using h

/-- Pullback to an arbitrary isometric complex sup plane. -/
theorem seminorm_on_isometric_plane {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : Seminorm ℂ F) (hp : ∀ a b : F, TEAPair a b → p (a + b) = p a + p b)
    (J : (ℂ × ℂ) →ₗᵢ[ℂ] F) (v : ℂ × ℂ) :
    p (J v) = p (J (1, 0)) * ‖v‖ := by
  apply seminorm_two_coordinate_rigidity (p.comp J.toLinearMap)
  intro x y hxy
  change p (J (x + y)) = p (J x) + p (J y)
  rw [map_add]
  apply hp
  simpa only [TEAPair, ← map_add, J.norm_map] using hxy

end
section

/-- Orthogonal elements in an arbitrary complex C*-algebra span a sup-norm plane. -/
private theorem norm_add_eq_max_of_cstar_orthogonal {A : Type*} [NonUnitalCStarAlgebra A]
    (a b : A) (hleft : star a * b = 0) (hright : a * star b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  have hba : star b * a = 0 := by
    have h := congrArg star hleft
    simpa only [star_mul, star_star, star_zero] using h
  have hab : (star a * a) * (star b * b) = 0 := by
    calc
      (star a * a) * (star b * b) = star a * (a * star b) * b := by simp [mul_assoc]
      _ = 0 := by rw [hright, mul_zero, zero_mul]
  have hs : star (a + b) * (a + b) = star a * a + star b * b := by
    simp only [star_add, add_mul, mul_add, hleft, hba, add_zero, zero_add]
  have hn := (IsSelfAdjoint.star_mul_self a).norm_add_eq_max
    (IsSelfAdjoint.star_mul_self b) hab
  rw [← hs, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self,
    CStarRing.norm_star_mul_self] at hn
  rcases le_total ‖a‖ ‖b‖ with h | h
  · rw [max_eq_right h]
    rw [max_eq_right (mul_self_le_mul_self (norm_nonneg a) h)] at hn
    nlinarith [norm_nonneg (a + b), norm_nonneg b]
  · rw [max_eq_left h]
    rw [max_eq_left (mul_self_le_mul_self (norm_nonneg b) h)] at hn
    nlinarith [norm_nonneg (a + b), norm_nonneg a]

/-- Scaling either orthogonal vector preserves the exact max-norm identity. -/
private theorem norm_smul_add_smul_of_cstar_orthogonal {A : Type*} [NonUnitalCStarAlgebra A]
    (a b : A) (hleft : star a * b = 0) (hright : a * star b = 0)
    (α β : ℂ) :
    ‖α • a + β • b‖ = max (‖α‖ * ‖a‖) (‖β‖ * ‖b‖) := by
  rw [norm_add_eq_max_of_cstar_orthogonal (α • a) (β • b), norm_smul, norm_smul]
  · simp only [star_smul, smul_mul_assoc, mul_smul_comm, hleft, smul_zero]
  · simp only [star_smul, smul_mul_assoc, mul_smul_comm, hright, smul_zero]

end

section

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The canonical isometric plane associated to two orthogonal norm-one elements. -/
private def orthogonalSupPlane (a b : A) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hleft : star a * b = 0) (hright : a * star b = 0) :
    (ℂ × ℂ) →ₗᵢ[ℂ] A where
  toFun v := v.1 • a + v.2 • b
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    simp only [add_assoc, add_left_comm, add_comm]
  map_smul' z v := by simp [smul_add, smul_smul]
  norm_map' v := by
    change ‖v.1 • a + v.2 • b‖ = ‖v‖
    rw [norm_smul_add_smul_of_cstar_orthogonal a b hleft hright, ha, hb]
    simp only [mul_one, Prod.norm_def]

/-- Orthogonal norm-one elements receive the same seminorm value. -/
theorem seminorm_orthogonal_axes (p : Seminorm ℂ A)
    (hp : ∀ a b : A, TEAPair a b → p (a + b) = p a + p b)
    (a b : A) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hleft : star a * b = 0) (hright : a * star b = 0) : p a = p b := by
  let J := orthogonalSupPlane a b ha hb hleft hright
  have h := seminorm_on_isometric_plane p hp J (0, 1)
  norm_num [J, orthogonalSupPlane, Prod.norm_def] at h
  exact h.symm

/-- Any element orthogonal to a norm-one element has the synchronized norm scale. -/
theorem seminorm_orthogonal_unit_scale (p : Seminorm ℂ A)
    (hp : ∀ a b : A, TEAPair a b → p (a + b) = p a + p b)
    (x g : A) (hg : ‖g‖ = 1) (hleft : star x * g = 0) (hright : x * star g = 0) :
    p x = p g * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let a : A := (‖x‖ : ℂ)⁻¹ • x
  have ha : ‖a‖ = 1 := by
    simp [a, norm_smul, hxn]
  have hal : star a * g = 0 := by
    simp only [a, star_smul, smul_mul_assoc, hleft, smul_zero]
  have har : a * star g = 0 := by
    simp only [a, smul_mul_assoc, hright, smul_zero]
  have hs := seminorm_orthogonal_axes p hp a g ha hg hal har
  have hs' : ‖x‖⁻¹ * p x = p g := by
    simpa only [a, map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_norm] using hs
  calc
    p x = ‖x‖ * (‖x‖⁻¹ * p x) := by rw [← mul_assoc, mul_inv_cancel₀ hxn, one_mul]
    _ = ‖x‖ * p g := by rw [hs']
    _ = p g * ‖x‖ := mul_comm _ _

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The coordinate axes associated to unit vectors form an isometric complex sup plane. -/
private def productSupPlane (e : E) (f : F) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    (ℂ × ℂ) →ₗᵢ[ℂ] (E × F) where
  toFun v := (v.1 • e, v.2 • f)
  map_add' v w := by ext <;> simp [add_smul]
  map_smul' z v := by ext <;> simp [smul_smul]
  norm_map' v := by
    change max ‖v.1 • e‖ ‖v.2 • f‖ = max ‖v.1‖ ‖v.2‖
    simp only [norm_smul, he, hf, mul_one]

private theorem product_plane_scale (p : Seminorm ℂ (E × F))
    (hp : ∀ a b : E × F, TEAPair a b → p (a + b) = p a + p b)
    (e : E) (f : F) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (v : ℂ × ℂ) :
    p (v.1 • e, v.2 • f) = p (e, 0) * ‖v‖ := by
  simpa [productSupPlane] using
    seminorm_on_isometric_plane p hp (productSupPlane e f he hf) v

private theorem unit_direction {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (g₀ : G) (hg₀ : ‖g₀‖ = 1) (x : G) :
    ∃ g : G, ‖g‖ = 1 ∧ x = (‖x‖ : ℂ) • g := by
  by_cases hx : x = 0
  · exact ⟨g₀, hg₀, by simp [hx]⟩
  · refine ⟨(‖x‖ : ℂ)⁻¹ • x, ?_, ?_⟩
    · simpa using (norm_smul_inv_norm (𝕜 := ℂ) hx)
    · have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
      rw [smul_inv_smul₀ hn]

/-- A TEA-additive complex seminorm on any nontrivial sup product has a single norm scale. -/
theorem seminorm_product_rigidity (p : Seminorm ℂ (E × F))
    (hp : ∀ a b : E × F, TEAPair a b → p (a + b) = p a + p b)
    (e₀ : E) (f₀ : F) (he₀ : ‖e₀‖ = 1) (hf₀ : ‖f₀‖ = 1) (v : E × F) :
    p v = p (e₀, 0) * ‖v‖ := by
  obtain ⟨e, he, hxe⟩ := unit_direction e₀ he₀ v.1
  obtain ⟨f, hf, hyf⟩ := unit_direction f₀ hf₀ v.2
  have haxis (a : E) (b : F) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
      p (a, 0) = p (0, b) := by
    have h := product_plane_scale p hp a b ha hb (0, 1)
    simpa [Prod.norm_def] using h.symm
  have hs : p (e, 0) = p (e₀, 0) :=
    (haxis e f₀ he hf₀).trans (haxis e₀ f₀ he₀ hf₀).symm
  have h := product_plane_scale p hp e f he hf ((‖v.1‖ : ℂ), (‖v.2‖ : ℂ))
  rw [← hxe, ← hyf, hs] at h
  simpa only [Prod.mk.eta, Prod.norm_def, Complex.norm_real, Real.norm_eq_abs,
    abs_norm] using h

end

end D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane
