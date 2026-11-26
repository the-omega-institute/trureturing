/- GID: D5/S3/QuadraticForms/QuadraticGermInvariance
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/QuadraticGermInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic-germ symmetries preserve the bilinear form and its infinitesimal action. -/

module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Tactic

/-! Quadratic expansion uniqueness and infinitesimal conjugation invariance. -/

@[expose] public section

namespace D5.S3.QuadraticForms.QuadraticGermInvariance

open Filter Asymptotics
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restricting a quadratic expansion to a ray gives its exact scalar coefficient. -/
theorem quadratic_germ_on_ray (f : E → ℝ) (B : LinearMap.BilinForm ℝ E)
    (hgerm : (fun X => f X - (1 - B X X / 2)) =o[𝓝 0]
      (fun X : E => ‖X‖ ^ 2)) (X : E) :
    (fun t : ℝ => f (t • X) - (1 - B X X * t ^ 2 / 2)) =o[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
  have ht : Tendsto (fun t : ℝ => t • X) (𝓝 0) (𝓝 (0 : E)) := by
    simpa only [id_eq, zero_smul] using!
      (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).smul_const X
  have hr := hgerm.comp_tendsto ht
  have hr' : (fun t : ℝ => f (t • X) - (1 - B X X * t ^ 2 / 2)) =o[𝓝 0]
      (fun t : ℝ => ‖X‖ ^ 2 * t ^ 2) := by
    refine hr.congr (fun t => ?_) (fun t => ?_)
    · simp only [Function.comp_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    · simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
  exact hr'.of_const_mul_right

private theorem quadratic_coefficient_unique (f : ℝ → ℝ) {a b : ℝ}
    (ha : (fun t => f t - (1 - a * t ^ 2 / 2)) =o[𝓝 0] (fun t : ℝ => t ^ 2))
    (hb : (fun t => f t - (1 - b * t ^ 2 / 2)) =o[𝓝 0] (fun t : ℝ => t ^ 2)) :
    a = b := by
  by_contra hab
  have hc : (a - b) / 2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr hab) (by norm_num)
  have hd : (fun t : ℝ => ((a - b) / 2) * t ^ 2) =o[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
    refine (ha.sub hb).congr_left (fun t => ?_)
    ring
  have hs := (isLittleO_const_mul_left_iff hc).mp hd
  have hn : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact pow_ne_zero _ (by simpa using ht)
  exact isLittleO_irrefl hn.frequently (hs.mono nhdsWithin_le_nhds)

/-- Every linear symmetry of a scalar quadratic germ preserves its symmetric bilinear form. -/
theorem bilinear_invariant_of_quadratic_germ (f : E → ℝ)
    (B : LinearMap.BilinForm ℝ E) (hB : B.IsSymm)
    (hgerm : (fun X => f X - (1 - B X X / 2)) =o[𝓝 0]
      (fun X : E => ‖X‖ ^ 2))
    (T : E →ₗ[ℝ] E) (hinv : ∀ X, f (T X) = f X) (X Y : E) :
    B (T X) (T Y) = B X Y := by
  have hdiag (Z : E) : B (T Z) (T Z) = B Z Z := by
    have hTZ := quadratic_germ_on_ray f B hgerm (T Z)
    have hZ := quadratic_germ_on_ray f B hgerm Z
    apply quadratic_coefficient_unique (fun t : ℝ => f (t • Z)) _ hZ
    refine hTZ.congr_left (fun t => ?_)
    rw [← T.map_smul, hinv]
  calc
    B (T X) (T Y) =
        (B (T X + T Y) (T X + T Y) - B (T X) (T X) - B (T Y) (T Y)) / 2 :=
      hB.polarization _ _
    _ = (B (X + Y) (X + Y) - B X X - B Y Y) / 2 := by
      rw [← T.map_add, hdiag, hdiag, hdiag]
    _ = B X Y := (hB.polarization X Y).symm

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

private theorem exp_conjugation_hasDerivAt (L : LieSubalgebra ℝ A) (C X : L)
    (hmem : ∀ t : ℝ, NormedSpace.exp (t • (C : A)) * (X : A) *
      NormedSpace.exp (-(t • (C : A))) ∈ L) :
    HasDerivAt (fun t : ℝ => (⟨NormedSpace.exp (t • (C : A)) * (X : A) *
      NormedSpace.exp (-(t • (C : A))), hmem t⟩ : L)) ⁅C, X⁆ 0 := by
  have hp : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (C : A))) (C : A) 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using!
      hasDerivAt_exp_smul_const (C : A) (0 : ℝ)
  have hm : HasDerivAt (fun t : ℝ => NormedSpace.exp (-(t • (C : A)))) (-(C : A)) 0 := by
    simpa only [smul_neg, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul] using!
      hasDerivAt_exp_smul_const (-(C : A)) (0 : ℝ)
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (C : A)) * (X : A) *
      NormedSpace.exp (-(t • (C : A)))) ((C : A) * (X : A) - (X : A) * (C : A)) 0 := by
    simpa only [Pi.mul_apply, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul, mul_one,
      mul_neg, sub_eq_add_neg] using! (hp.mul_const (X : A)).mul hm
  rw [hasDerivAt_iff_tendsto_slope, tendsto_subtype_rng]
  simpa only [slope, vsub_eq_sub, Submodule.coe_smul_of_tower, Submodule.coe_sub,
    LieSubalgebra.coe_bracket, Ring.lie_def] using! hd.tendsto_slope

/-- Exponential conjugation symmetries of a quadratic germ have skew adjoint action. -/
theorem ad_invariant_of_exp_conjugation [FiniteDimensional ℝ A]
    (L : LieSubalgebra ℝ A) (f : L → ℝ) (B : LinearMap.BilinForm ℝ L)
    (hB : B.IsSymm)
    (hgerm : (fun X => f X - (1 - B X X / 2)) =o[𝓝 0]
      (fun X : L => ‖X‖ ^ 2))
    (hmem : ∀ (C : L) (t : ℝ) (X : L),
      NormedSpace.exp (t • (C : A)) * (X : A) *
        NormedSpace.exp (-(t • (C : A))) ∈ L)
    (hinv : ∀ (C : L) (t : ℝ) (X : L),
      f ⟨NormedSpace.exp (t • (C : A)) * (X : A) *
        NormedSpace.exp (-(t • (C : A))), hmem C t X⟩ = f X)
    (C X Y : L) : B ⁅C, X⁆ Y + B X ⁅C, Y⁆ = 0 := by
  let T (t : ℝ) : L →ₗ[ℝ] L :=
    { toFun := fun Z => ⟨NormedSpace.exp (t • (C : A)) * (Z : A) *
          NormedSpace.exp (-(t • (C : A))), hmem C t Z⟩
      map_add' := by
        intro U V
        apply Subtype.ext
        simp [mul_add, add_mul]
      map_smul' := by
        intro r Z
        apply Subtype.ext
        simp }
  have hzero (Z : L) : T 0 Z = Z := by
    apply Subtype.ext
    simp [T]
  have hconstant (t : ℝ) : B (T t X) (T t Y) = B X Y :=
    bilinear_invariant_of_quadratic_germ f B hB hgerm (T t) (hinv C t) X Y
  have hx : HasDerivAt (fun t : ℝ => T t X) ⁅C, X⁆ 0 :=
    exp_conjugation_hasDerivAt L C X (fun t => hmem C t X)
  have hy : HasDerivAt (fun t : ℝ => T t Y) ⁅C, Y⁆ 0 :=
    exp_conjugation_hasDerivAt L C Y (fun t => hmem C t Y)
  have hd := B.toContinuousBilinearMap.hasDerivAt_of_bilinear (fun _ => hx) (fun _ => hy)
  have heq : (fun t : ℝ => B.toContinuousBilinearMap (T t X) (T t Y)) =
      fun _ : ℝ => B X Y := funext hconstant
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (B X Y))
  simp only [LinearMap.toContinuousBilinearMap_apply, hzero] at hz
  linarith

end

end D5.S3.QuadraticForms.QuadraticGermInvariance
