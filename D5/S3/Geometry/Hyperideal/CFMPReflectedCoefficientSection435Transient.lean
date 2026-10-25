import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import D5.S3.Geometry.Hyperideal.CFMPReflectedPlaneChart435Transient
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open CFMPReflectedPlaneChart435Transient

namespace CFMPReflectedCoefficientSection435Transient

abbrev Coeff := Fin 4 → ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

def dropPlane : Coeff →ₗ[ℝ] W where
  toFun u := ![u 0,u 2,u 3]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

def insertPlane : W →ₗ[ℝ] Coeff where
  toFun v := ![v 0,0,v 1,v 2]
  map_add' _ _ := by ext i; fin_cases i <;> simp
  map_smul' _ _ := by ext i; fin_cases i <;> simp

theorem insert_drop (u : Coeff) (h : u 1 = 0) : insertPlane (dropPlane u) = u := by
  ext i
  fin_cases i <;> simp [insertPlane, dropPlane, h]

def sumCoefficients : Coeff →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i

def forward (M : M4) (R : Coeff →ₗ[ℝ] Coeff) : Coeff →ₗ[ℝ] W :=
  dropPlane.comp (R.comp M.vecMulLinear)

def back (M : M4) (R : Coeff →ₗ[ℝ] Coeff) : W →ₗ[ℝ] Coeff :=
  (M⁻¹).vecMulLinear.comp (R.comp insertPlane)

def sectionMap (M : M4) (R : Coeff →ₗ[ℝ] Coeff) : W →ₗ[ℝ] ℝ :=
  sumCoefficients.comp (back M R)

theorem back_forward (M : M4) (R : Coeff →ₗ[ℝ] Coeff)
    (hM : M.det ≠ 0) (hR : Function.Involutive R)
    (ξ : Coeff) (hplane : R (ξ ᵥ* M) 1 = 0) :
    back M R (forward M R ξ) = ξ := by
  change R (insertPlane (dropPlane (R (ξ ᵥ* M)))) ᵥ* M⁻¹ = ξ
  rw [insert_drop _ hplane, hR, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM), Matrix.vecMul_one]

theorem section_forward (M : M4) (R : Coeff →ₗ[ℝ] Coeff)
    (hM : M.det ≠ 0) (hR : Function.Involutive R)
    (ξ : Coeff) (hplane : R (ξ ᵥ* M) 1 = 0) :
    sectionMap M R (forward M R ξ) = ∑ i, ξ i := by
  change sumCoefficients (back M R (forward M R ξ)) = _
  rw [back_forward M R hM hR ξ hplane]
  simp [sumCoefficients]

def reflectedTangents (M : M4) (R : Coeff →ₗ[ℝ] Coeff) (b c : Coeff) : A32 :=
  fun i j => ![forward M R b,forward M R c] j i

theorem tangent_mulVec (M : M4) (R : Coeff →ₗ[ℝ] Coeff)
    (b c : Coeff) (q : E) :
    (reflectedTangents M R b c).mulVec q = forward M R (q 0 • b + q 1 • c) := by
  ext i
  simp [reflectedTangents, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    map_add, map_smul, smul_eq_mul]
  <;> ring

theorem affine_forward (M : M4) (R : Coeff →ₗ[ℝ] Coeff)
    (a b c : Coeff) (q : E) :
    affine (forward M R a) (reflectedTangents M R b c) q =
      forward M R (a + q 0 • b + q 1 • c) := by
  rw [affine, tangent_mulVec]
  simp only [map_add, map_smul, add_assoc]

theorem tangent_plane (M : M4) (R : Coeff →ₗ[ℝ] Coeff)
    (b c : Coeff) (hb : R (b ᵥ* M) 1 = 0) (hc : R (c ᵥ* M) 1 = 0) (q : E) :
    R ((q 0 • b + q 1 • c) ᵥ* M) 1 = 0 := by
  simp only [Matrix.add_vecMul, Matrix.smul_vecMul, map_add, map_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb, hc, mul_zero, add_zero]

theorem reflected_tangents_injective (M : M4) (R : Coeff →ₗ[ℝ] Coeff)
    (hM : M.det ≠ 0) (hR : Function.Involutive R) (b c : Coeff)
    (hb : R (b ᵥ* M) 1 = 0) (hc : R (c ᵥ* M) 1 = 0)
    (hbc : Function.Injective (fun q : E => q 0 • b + q 1 • c)) :
    Function.Injective (reflectedTangents M R b c).mulVec := by
  intro p q hpq
  rw [tangent_mulVec, tangent_mulVec] at hpq
  have h := congrArg (back M R) hpq
  rw [back_forward M R hM hR _ (tangent_plane M R b c hb hc p),
    back_forward M R hM hR _ (tangent_plane M R b c hb hc q)] at h
  exact hbc h

theorem actual_section_data (M : M4) (R : Coeff →ₗ[ℝ] Coeff)
    (hM : M.det ≠ 0) (hR : Function.Involutive R) (a b c : Coeff)
    (ha : R (a ᵥ* M) 1 = 0) (hb : R (b ᵥ* M) 1 = 0) (hc : R (c ᵥ* M) 1 = 0)
    (hsa : ∑ i, a i = 1) (hsb : ∑ i, b i = 0) (hsc : ∑ i, c i = 0) :
    sectionMap M R (forward M R a) = 1 ∧
      ∀ j, sectionMap M R ((reflectedTangents M R b c).col j) = 0 := by
  constructor
  · rw [section_forward M R hM hR a ha, hsa]
  · intro j
    fin_cases j
    · change sectionMap M R (forward M R b) = 0
      rw [section_forward M R hM hR b hb, hsb]
    · change sectionMap M R (forward M R c) = 0
      rw [section_forward M R hM hR c hc, hsc]

theorem actual_augmented_det_ne_zero (M : M4) (R : Coeff →ₗ[ℝ] Coeff)
    (hM : M.det ≠ 0) (hR : Function.Involutive R) (a b c : Coeff)
    (ha : R (a ᵥ* M) 1 = 0) (hb : R (b ᵥ* M) 1 = 0) (hc : R (c ᵥ* M) 1 = 0)
    (hsa : ∑ i, a i = 1) (hsb : ∑ i, b i = 0) (hsc : ∑ i, c i = 0)
    (hbc : Function.Injective (fun q : E => q 0 • b + q 1 • c)) :
    (augmented (reflectedTangents M R b c) (forward M R a)).det ≠ 0 := by
  have h := actual_section_data M R hM hR a b c ha hb hc hsa hsb hsc
  exact augmented_det_ne_zero _ _ (sectionMap M R) h.1 h.2
    (reflected_tangents_injective M R hM hR b c hb hc hbc)

-- The normal is chosen for this exact triangle, before constructing its reflection.
def pairing (X : Coeff) : Coeff →ₗ[ℝ] ℝ :=
  ∑ k, ((![(1 : ℝ),1,1,-1] k) * X k) • LinearMap.proj k

theorem pairing_apply (X Y : Coeff) : pairing X Y = lorentz X Y := by
  simp [pairing, lorentz]

def triplePairing (X Y Z : Coeff) : Coeff →ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearMap.pi (fun i => pairing (![X,Y,Z] i))

theorem exists_triangle_normal (X Y Z : Coeff) :
    ∃ N : Coeff, N ≠ 0 ∧ lorentz X N = 0 ∧ lorentz Y N = 0 ∧ lorentz Z N = 0 := by
  have hk : LinearMap.ker (triplePairing X Y Z) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by norm_num [Coeff])
  obtain ⟨N, hN, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hzero : triplePairing X Y Z N = 0 := hN
  refine ⟨N, hn, ?_, ?_, ?_⟩
  · simpa [triplePairing, pairing_apply] using congrFun hzero 0
  · simpa [triplePairing, pairing_apply] using congrFun hzero 1
  · simpa [triplePairing, pairing_apply] using congrFun hzero 2

-- This statement only transfers the quadratic expression. It does not assert measure equality.
theorem actual_radius (M : M4) (R : Coeff →ₗ[ℝ] Coeff)
    (hR : ∀ X Y, lorentz (R X) (R Y) = lorentz X Y)
    (ξ : Coeff) (hplane : R (ξ ᵥ* M) 1 = 0) :
    radius (forward M R ξ) = -lorentz (ξ ᵥ* M) (ξ ᵥ* M) := by
  rw [← hR (ξ ᵥ* M) (ξ ᵥ* M)]
  simp [forward, dropPlane, radius, lorentz, Fin.sum_univ_four, hplane]
  <;> ring

end CFMPReflectedCoefficientSection435Transient
